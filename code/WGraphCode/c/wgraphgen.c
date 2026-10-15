#ifndef _WIN32
#define _POSIX_C_SOURCE 200809L
#endif
#ifdef __APPLE__
#define _DARWIN_C_SOURCE 1
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <errno.h>
#include <limits.h>
#include <ctype.h>

// OpenMP for multithreading
#include <omp.h>

#ifndef _WIN32
#include <unistd.h>
#endif

#ifdef __APPLE__
#include <sys/sysctl.h>
#endif

// ==========================================
// CONFIGURATION
// ==========================================
#define DEFAULT_THREAD_COUNT 1
#define MIN_N 1
#define MAX_N 8
#define MAX_SUPPORTED_N 32

// Enable verbose diagnostic output when investigating the algorithm.
#define DEBUG_MODE 0

// Global RAM policy defaults
#define DEFAULT_MEMORY_FRACTION 0.70
#define DEFAULT_MEMORY_RESERVE_MB 4096
#define DEFAULT_MEMORY_WAIT_SECONDS 300
#define MEMORY_POLL_MILLISECONDS 1000

// Conservative headroom for memory estimation
#define MEMORY_ESTIMATE_HEADROOM 1.35L

// ==========================================
// OS-Specific Directory Creation / Sleep
// ==========================================
#ifdef _WIN32
#include <direct.h>
#include <windows.h>
#define MKDIR(path) _mkdir(path)
#define CHDIR(path) _chdir(path)
static void sleep_millis(int ms) { Sleep((DWORD)ms); }
#else
#include <sys/stat.h>
#include <sys/types.h>
#define MKDIR(path) mkdir(path, 0777)
#define CHDIR(path) chdir(path)
static void sleep_millis(int ms) {
    struct timespec delay = {ms / 1000, (ms % 1000) * 1000000L};
    while (nanosleep(&delay, &delay) != 0 && errno == EINTR) {}
}
#endif

// ==========================================
// Constants
// ==========================================
#define MAX_CAPACITY ((size_t)INT32_MAX - 1u)

_Static_assert(SIZE_MAX > UINT32_MAX, "wgraphgen requires a 64-bit size_t");
_Static_assert(INT_MAX >= INT32_MAX, "wgraphgen requires at least 32-bit int");

// ==========================================
// Export Format
// ==========================================
// File format:
//
// [32-byte little-endian header: five uint32_t fields, four zero bytes, uint64_t edges]
// [partition array: uint32_t[partition_len]]
// [offsets: uint64_t[num_vertices + 1]]
// [targets: uint32_t[num_edges]]
// [weights: int32_t[num_edges]]
//
// Only edges (u,v,w) with u < v are stored, exactly once.

#define GRAPH_MAGIC   0x55474C31u   /* "UGL1" */
#define GRAPH_VERSION 3u

// ==========================================
// Data Structures
// ==========================================
typedef struct {
    int target;
    int32_t weight;
} Edge;

typedef struct {
    Edge *edges;
    int size;
    int capacity;
} VertexFlat;

// --- Thread Context ---
typedef struct {
    int N;
    int PARTITION[64];
    int PARTITION_LEN;

    int NUM_TABLEAUX;
    size_t CURRENT_CAPACITY;
    int GLOBAL_TAG;
    size_t RESERVED_BYTES;

    // Graph data
    uint8_t *COL_INDS;
    uint8_t *ROW_INDS;
    uint32_t *DESCENTS;
    int32_t *TABLE;
    VertexFlat *FLAT_GRAPH;

    // Caches
    int32_t *WEIGHT_CACHE;
    int *CACHE_TAGS;

    // Hash table (single-array open addressing)
    int *HASH_KEYS;
    size_t HASH_SIZE;
    size_t HASH_MASK;

    uint32_t FULL_DESC_MASK;
    uint32_t *MASK_OFFSETS;
    int *MASK_VERTICES;
    int *PHASE2_CANDIDATES;
    int *PHASE2_SCRATCH;
    uint8_t *MAX_POSITIVE_DESCENT;
} Context;

typedef enum {
    TASK_STATE_SKIP = 0,
    TASK_STATE_PENDING,
    TASK_STATE_RUNNING,
    TASK_STATE_DONE,
    TASK_STATE_DEFERRED,
    TASK_STATE_FAILED
} TaskState;

// --- Task Definition ---
typedef struct {
    int n;
    int partition[64];
    int len;

    char part_str[128];
    double dim_approx;
    size_t est_bytes;
    size_t initial_capacity;
    int attempts;

    TaskState state;
} PartitionTask;

// ==========================================
// Globals
// ==========================================
PartitionTask *ALL_TASKS = NULL;
int TASK_COUNT = 0;
int TASK_CAPACITY = 1000;

static int FORCE_SINGLE_PARTITION = 0;
static int RANGE_MIN_N = MIN_N;
static int RANGE_MAX_N = MAX_N;
static int THREADS_TO_USE = DEFAULT_THREAD_COUNT;

static double MEMORY_FRACTION = DEFAULT_MEMORY_FRACTION;
static size_t MEMORY_RESERVE_BYTES = (size_t)DEFAULT_MEMORY_RESERVE_MB * 1024ULL * 1024ULL;
static int MEMORY_WAIT_SECONDS = DEFAULT_MEMORY_WAIT_SECONDS;
static const char *OUTPUT_DIR = "data";

static const char *COMPLETED_LOG_FILENAME = "completed_partitions.log";
static const char *STARTED_LOG_FILENAME   = "started_partitions.log";
static const char *DEFERRED_LOG_FILENAME  = "deferred_partitions.log";
static const char *FAILED_LOG_FILENAME    = "failed_partitions.log";

// Completed partition list loaded at startup
static char **COMPLETED_PARTITIONS = NULL;
static int COMPLETED_COUNT = 0;
static int COMPLETED_CAPACITY = 0;

// Scheduler / memory state
static omp_lock_t GLOBAL_LOCK;
static omp_lock_t LOG_LOCK;
static size_t GLOBAL_RESERVED_BYTES = 0;
static int TASK_PENDING_COUNT = 0;
static int TASK_RUNNING_COUNT = 0;
static int TASK_DONE_COUNT = 0;
static int TASK_DEFERRED_COUNT = 0;
static int TASK_FAILED_COUNT = 0;
static double LAST_PROGRESS_TIME = 0.0;

// ==========================================
// Utility Helpers
// ==========================================
static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) {
        fprintf(stderr, "malloc failed for %zu bytes\n", n);
        exit(1);
    }
    return p;
}

static void *xcalloc(size_t count, size_t size) {
    if (size != 0 && count > SIZE_MAX / size) {
        fprintf(stderr, "calloc size overflow\n");
        exit(1);
    }
    if (count == 0 || size == 0) return xmalloc(1);
    void *p = calloc(count, size);
    if (!p) {
        fprintf(stderr, "calloc failed for %zu bytes\n", count * size);
        exit(1);
    }
    return p;
}

static void *xrealloc(void *ptr, size_t n) {
    void *p = realloc(ptr, n ? n : 1);
    if (!p) {
        fprintf(stderr, "realloc failed for %zu bytes\n", n);
        exit(1);
    }
    return p;
}

static char *xstrdup_local(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = (char *)xmalloc(len);
    memcpy(p, s, len);
    return p;
}

static void partition_to_string(const int *part, int len, char *out, size_t out_sz) {
    out[0] = '\0';
    size_t used = 0;
    for (int i = 0; i < len; i++) {
        int written = snprintf(out + used, (used < out_sz ? out_sz - used : 0),
                               (i == 0) ? "%d" : "_%d", part[i]);
        if (written < 0) break;
        used += (size_t)written;
        if (used >= out_sz) {
            out[out_sz - 1] = '\0';
            return;
        }
    }
}

static int parse_partition_string(const char *s, int *out, int *len, int *sum_out) {
    *len = 0;
    *sum_out = 0;
    while (*s) {
        if (*len >= MAX_SUPPORTED_N || !isdigit((unsigned char)*s)) return 0;
        char *end;
        errno = 0;
        long value = strtol(s, &end, 10);
        if (errno || value <= 0 || value > MAX_SUPPORTED_N - *sum_out) return 0;
        int x = (int)value;
        if (*len > 0 && x > out[*len - 1]) return 0; // must be non-increasing
        out[*len] = x;
        (*len)++;
        *sum_out += x;
        s = end;
        if (!*s) break;
        if (*s != '_' && *s != ' ' && *s != ',') return 0;
        s++;
        while (*s == ' ') s++;
        if (!*s) return 0;
    }
    return (*len > 0);
}

static int ensure_dir_exists(const char *path) {
    if (MKDIR(path) == 0) return 1;
    if (errno == EEXIST) return 1;
    return 0;
}

static int ensure_output_root(const char *path) {
    if (!*path) return 0;
    char *copy = xstrdup_local(path);
    int ok = 1;
    for (char *p = copy + 1; *p; p++) {
        if (*p == '/') {
            *p = '\0';
            ok = ensure_dir_exists(copy);
            *p = '/';
            if (!ok) break;
        }
    }
    if (ok) ok = ensure_dir_exists(copy);
    free(copy);
    return ok && CHDIR(path) == 0;
}

static int compare_cstrings(const void *a, const void *b) {
    const char *sa = *(const char * const *)a;
    const char *sb = *(const char * const *)b;
    return strcmp(sa, sb);
}

static int compare_partitions_lex(const int *a, int len_a, const int *b, int len_b) {
    int min_len = (len_a < len_b) ? len_a : len_b;
    for (int i = 0; i < min_len; i++) {
        if (a[i] < b[i]) return -1;
        if (a[i] > b[i]) return 1;
    }
    if (len_a < len_b) return -1;
    if (len_a > len_b) return 1;
    return 0;
}

static void compute_conjugate_partition(const int *part, int len, int *conj, int *conj_len) {
    int max_col = part[0];
    for (int j = 0; j < max_col; j++) {
        int count = 0;
        for (int i = 0; i < len; i++) {
            if (part[i] > j) count++;
        }
        conj[j] = count;
    }
    *conj_len = max_col;
    while (*conj_len > 0 && conj[*conj_len - 1] == 0) {
        (*conj_len)--;
    }
}

static void canonicalize_partition_lexmax(int *part, int *len) {
    int conj[64];
    int conj_len = 0;
    compute_conjugate_partition(part, *len, conj, &conj_len);

    if (compare_partitions_lex(part, *len, conj, conj_len) < 0) {
        memcpy(part, conj, conj_len * sizeof(int));
        *len = conj_len;
    }
}

static int is_partition_canonical_lexmax(const int *part, int len) {
    int conj[64];
    int conj_len = 0;
    compute_conjugate_partition(part, len, conj, &conj_len);
    return compare_partitions_lex(part, len, conj, conj_len) >= 0;
}

static void add_completed_partition_name(const char *part_str) {
    if (COMPLETED_COUNT >= COMPLETED_CAPACITY) {
        COMPLETED_CAPACITY = (COMPLETED_CAPACITY == 0) ? 1024 : COMPLETED_CAPACITY * 2;
        COMPLETED_PARTITIONS = (char **)xrealloc(COMPLETED_PARTITIONS,
                                                 COMPLETED_CAPACITY * sizeof(char *));
    }
    COMPLETED_PARTITIONS[COMPLETED_COUNT++] = xstrdup_local(part_str);
}

static void load_completed_log(void) {
    FILE *f = fopen(COMPLETED_LOG_FILENAME, "r");
    if (!f) return;

    char line[512];
    while (fgets(line, sizeof(line), f)) {
        size_t len = strlen(line);
        while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) {
            line[--len] = '\0';
        }
        if (len == 0) continue;

        char *sep = strchr(line, '|');
        if (sep) *sep = '\0';

        if (line[0] != '\0') {
            int part[64], plen = 0, n = 0;
            if (parse_partition_string(line, part, &plen, &n)) {
                canonicalize_partition_lexmax(part, &plen);
                char canon[128];
                partition_to_string(part, plen, canon, sizeof(canon));
                add_completed_partition_name(canon);
            } else {
                add_completed_partition_name(line);
            }
        }
    }
    fclose(f);

    if (COMPLETED_COUNT > 1) {
        qsort(COMPLETED_PARTITIONS, COMPLETED_COUNT, sizeof(char *), compare_cstrings);
    }
}

static int is_in_completed_log(const char *part_str) {
    if (COMPLETED_COUNT == 0) return 0;
    char *key = (char *)part_str;
    return bsearch(&key, COMPLETED_PARTITIONS, COMPLETED_COUNT,
                   sizeof(char *), compare_cstrings) != NULL;
}

static void append_completed_log(const PartitionTask *task,
                                 int tableaux, long long edges, long long specials) {
    FILE *f = fopen(COMPLETED_LOG_FILENAME, "a");
    if (!f) {
        fprintf(stderr, "[WARN] Could not open %s for append\n", COMPLETED_LOG_FILENAME);
        return;
    }

    time_t now = time(NULL);
    fprintf(f, "%s|N=%d|tableaux=%d|edges=%lld|specials=%lld|est_mb=%zu|time=%lld\n",
            task->part_str, task->n, tableaux, edges, specials,
            (size_t)(task->est_bytes / (1024ULL * 1024ULL)),
            (long long)now);
    fflush(f);
    fclose(f);
}

static void append_started_log(const PartitionTask *task, size_t budget_bytes) {
    FILE *f = fopen(STARTED_LOG_FILENAME, "a");
    if (!f) return;
    time_t now = time(NULL);
    fprintf(f, "%s|N=%d|est_mb=%zu|budget_mb=%zu|attempt=%d|time=%lld\n",
            task->part_str, task->n,
            (size_t)(task->est_bytes / (1024ULL * 1024ULL)),
            (size_t)(budget_bytes / (1024ULL * 1024ULL)),
            task->attempts,
            (long long)now);
    fflush(f);
    fclose(f);
}

static void append_deferred_log(const PartitionTask *task, const char *reason, size_t budget_bytes) {
    FILE *f = fopen(DEFERRED_LOG_FILENAME, "a");
    if (!f) return;
    time_t now = time(NULL);
    fprintf(f, "%s|N=%d|reason=%s|est_mb=%zu|budget_mb=%zu|attempt=%d|time=%lld\n",
            task->part_str, task->n, reason,
            (size_t)(task->est_bytes / (1024ULL * 1024ULL)),
            (size_t)(budget_bytes / (1024ULL * 1024ULL)),
            task->attempts,
            (long long)now);
    fflush(f);
    fclose(f);
}

static void append_failed_log(const PartitionTask *task, const char *reason) {
    FILE *f = fopen(FAILED_LOG_FILENAME, "a");
    if (!f) return;
    time_t now = time(NULL);
    fprintf(f, "%s|N=%d|reason=%s|attempt=%d|time=%lld\n",
            task->part_str, task->n, reason, task->attempts, (long long)now);
    fflush(f);
    fclose(f);
}

static void free_completed_partitions(void) {
    for (int i = 0; i < COMPLETED_COUNT; i++) {
        free(COMPLETED_PARTITIONS[i]);
    }
    free(COMPLETED_PARTITIONS);
    COMPLETED_PARTITIONS = NULL;
    COMPLETED_COUNT = 0;
    COMPLETED_CAPACITY = 0;
}


static size_t next_hash_size_for_capacity(size_t cap) {
    size_t need = (cap < 1024) ? 1024 : cap * 2;
    size_t hash_size = 1;
    while (hash_size < need) {
        if (hash_size > SIZE_MAX / 2) {
            fprintf(stderr, "hash size overflow\n");
            exit(1);
        }
        hash_size <<= 1;
    }
    return hash_size;
}

static uint64_t exact_specht_dimension_capped(int n, const int *part, int len, uint64_t cap) {
    int primes[64];
    int prime_count = 0;
    int is_composite[256] = {0};
    for (int p = 2; p <= n; p++) {
        if (!is_composite[p]) {
            primes[prime_count++] = p;
            if ((int64_t)p * p <= n) {
                for (int q = p * p; q <= n; q += p) {
                    is_composite[q] = 1;
                }
            }
        }
    }

    int exponents[64] = {0};
    for (int i = 0; i < prime_count; i++) {
        int p = primes[i];
        int m = n;
        while (m > 0) {
            m /= p;
            exponents[i] += m;
        }
    }

    int conjugate[64] = {0};
    for (int j = 0; j < part[0]; j++) {
        for (int i = 0; i < len; i++) {
            if (part[i] > j) {
                conjugate[j]++;
            }
        }
    }

    for (int i = 0; i < len; i++) {
        for (int j = 0; j < part[i]; j++) {
            int h = (part[i] - j) + (conjugate[j] - i) - 1;
            for (int k = 0; k < prime_count; k++) {
                int p = primes[k];
                while (h % p == 0) {
                    exponents[k]--;
                    h /= p;
                }
                if (h == 1) {
                    break;
                }
            }
            if (h != 1) {
                fprintf(stderr, "failed to factor hook length %d\n", h);
                exit(1);
            }
        }
    }

    uint64_t result = 1;
    for (int i = 0; i < prime_count; i++) {
        for (int e = 0; e < exponents[i]; e++) {
            if (result > cap / (unsigned)primes[i]) return cap;
            result *= (unsigned)primes[i];
            if (result > cap) {
                return cap;
            }
        }
    }
    return (uint64_t)result;
}

static size_t descent_bucket_count(int n, size_t capacity) {
    // Dense masks are useful only when their index is proportionate to the graph.
    if (n <= 1 || n > 24) return 0;
    size_t count = (size_t)1u << (n - 1);
    return (count <= 1024 || count <= 4 * capacity) ? count : 0;
}

// ==========================================
// Memory Estimation / RAM Query
// ==========================================
static size_t estimate_context_bytes_for_capacity(int n, size_t cap) {
    size_t total = 0;
    size_t mask_count = descent_bucket_count(n, cap);

    total += next_hash_size_for_capacity(cap) * sizeof(int); // HASH_KEYS

    total += cap * (size_t)n * sizeof(uint8_t);        // COL_INDS
    total += cap * (size_t)n * sizeof(uint8_t);        // ROW_INDS
    total += cap * sizeof(uint32_t);                   // DESCENTS
    total += cap * (size_t)(n - 1) * sizeof(int32_t); // TABLE
    total += cap * sizeof(int32_t);                    // WEIGHT_CACHE
    total += cap * sizeof(int);                        // CACHE_TAGS
    total += cap * sizeof(VertexFlat);                 // FLAT_GRAPH metadata
    total += cap * sizeof(int);                        // MASK_VERTICES
    total += cap * sizeof(int);                        // PHASE2_CANDIDATES
    total += cap * sizeof(int);                        // PHASE2_SCRATCH
    total += cap * sizeof(uint8_t);                    // MAX_POSITIVE_DESCENT
    total += (3 * mask_count + 1) * sizeof(uint32_t);  // offsets and build scratch
    total += 4 * cap * (size_t)(n - 1) * sizeof(Edge); // adjacency storage budget

    return total;
}

static size_t get_total_physical_memory_bytes(void) {
#ifdef __APPLE__
    int64_t mem = 0;
    size_t len = sizeof(mem);
    if (sysctlbyname("hw.memsize", &mem, &len, NULL, 0) == 0 && mem > 0) {
        return (size_t)mem;
    }
#endif

#if defined(_SC_PHYS_PAGES) && defined(_SC_PAGESIZE)
    long pages = sysconf(_SC_PHYS_PAGES);
    long page_size = sysconf(_SC_PAGESIZE);
    if (pages > 0 && page_size > 0) {
        return (size_t)pages * (size_t)page_size;
    }
#endif

    return 0;
}

static size_t get_available_memory_bytes(void) {
#ifdef __linux__
    FILE *f = fopen("/proc/meminfo", "r");
    if (f) {
        char line[256];
        while (fgets(line, sizeof(line), f)) {
            unsigned long long kb = 0ULL;
            if (sscanf(line, "MemAvailable: %llu kB", &kb) == 1) {
                fclose(f);
                return (size_t)kb * 1024ULL;
            }
        }
        fclose(f);
    }
#endif

#if defined(_SC_AVPHYS_PAGES) && defined(_SC_PAGESIZE)
    long pages = sysconf(_SC_AVPHYS_PAGES);
    long page_size = sysconf(_SC_PAGESIZE);
    if (pages > 0 && page_size > 0) {
        return (size_t)pages * (size_t)page_size;
    }
#endif

    return get_total_physical_memory_bytes();
}

static size_t compute_usable_budget_bytes_unlocked(size_t reserved_snapshot) {
    size_t avail = get_available_memory_bytes();

    // Add our own reserved estimate back into the base before applying the fraction.
    // This avoids double-penalizing the memory our own scheduler already reserved.
    long double base = (long double)avail + (long double)reserved_snapshot;
    long double usable = MEMORY_FRACTION * base - (long double)MEMORY_RESERVE_BYTES;

    if (usable < 0.0L) return 0;
    if (usable > (long double)SIZE_MAX) return SIZE_MAX;
    return (size_t)usable;
}

static size_t get_current_usable_budget_bytes(void) {
    size_t reserved_snapshot;
    omp_set_lock(&GLOBAL_LOCK);
    reserved_snapshot = GLOBAL_RESERVED_BYTES;
    omp_unset_lock(&GLOBAL_LOCK);
    return compute_usable_budget_bytes_unlocked(reserved_snapshot);
}

static int wait_for_additional_reservation(Context *ctx, size_t new_required_bytes) {
    if (new_required_bytes <= ctx->RESERVED_BYTES) {
        return 1;
    }

    size_t delta = new_required_bytes - ctx->RESERVED_BYTES;
    double start = omp_get_wtime();

    while (1) {
        int ok = 0;
        omp_set_lock(&GLOBAL_LOCK);
        size_t budget = compute_usable_budget_bytes_unlocked(GLOBAL_RESERVED_BYTES);
        if (GLOBAL_RESERVED_BYTES <= budget && delta <= (budget - GLOBAL_RESERVED_BYTES)) {
            GLOBAL_RESERVED_BYTES += delta;
            ctx->RESERVED_BYTES = new_required_bytes;
            LAST_PROGRESS_TIME = omp_get_wtime();
            ok = 1;
        }
        omp_unset_lock(&GLOBAL_LOCK);

        if (ok) return 1;

        if (MEMORY_WAIT_SECONDS >= 0 &&
            (omp_get_wtime() - start) >= (double)MEMORY_WAIT_SECONDS) {
            return 0;
        }

        sleep_millis(MEMORY_POLL_MILLISECONDS);
    }
}

static void release_reserved_bytes_after_task(size_t bytes_released) {
    omp_set_lock(&GLOBAL_LOCK);
    if (GLOBAL_RESERVED_BYTES >= bytes_released) GLOBAL_RESERVED_BYTES -= bytes_released;
    else GLOBAL_RESERVED_BYTES = 0;
    LAST_PROGRESS_TIME = omp_get_wtime();
    omp_unset_lock(&GLOBAL_LOCK);
}

// ==========================================
// Memory Management (Context-based)
// ==========================================
static uint32_t hash_seq(const uint8_t *data, int len);

static void init_context(Context *ctx,
                         int n,
                         const int *part,
                         int len,
                         size_t reserved_bytes,
                         size_t initial_capacity) {
    memset(ctx, 0, sizeof(*ctx));

    ctx->N = n;
    ctx->PARTITION_LEN = len;
    memcpy(ctx->PARTITION, part, len * sizeof(int));

    ctx->NUM_TABLEAUX = 0;
    ctx->CURRENT_CAPACITY = (initial_capacity == 0) ? 1 : initial_capacity;
    ctx->GLOBAL_TAG = 0;
    ctx->RESERVED_BYTES = reserved_bytes;

    ctx->HASH_SIZE = next_hash_size_for_capacity(ctx->CURRENT_CAPACITY);
    ctx->HASH_MASK = ctx->HASH_SIZE - 1;
    ctx->HASH_KEYS = (int *)xmalloc(ctx->HASH_SIZE * sizeof(int));
    memset(ctx->HASH_KEYS, -1, ctx->HASH_SIZE * sizeof(int));

    ctx->COL_INDS = (uint8_t *)xmalloc(ctx->CURRENT_CAPACITY * (size_t)n * sizeof(uint8_t));
    ctx->ROW_INDS = (uint8_t *)xmalloc(ctx->CURRENT_CAPACITY * (size_t)n * sizeof(uint8_t));
    ctx->DESCENTS = (uint32_t *)xmalloc(ctx->CURRENT_CAPACITY * sizeof(uint32_t));
    ctx->TABLE = (int32_t *)xmalloc(ctx->CURRENT_CAPACITY * (size_t)(n - 1) * sizeof(int32_t));
    ctx->WEIGHT_CACHE = (int32_t *)xcalloc(ctx->CURRENT_CAPACITY, sizeof(int32_t));
    ctx->CACHE_TAGS = (int *)xcalloc(ctx->CURRENT_CAPACITY, sizeof(int));
    ctx->FLAT_GRAPH = NULL;
    ctx->FULL_DESC_MASK = (n <= 1) ? 0u : ((1u << (n - 1)) - 1u);
    ctx->MASK_OFFSETS = NULL;
    ctx->MASK_VERTICES = NULL;
    ctx->PHASE2_CANDIDATES = NULL;
    ctx->PHASE2_SCRATCH = NULL;
    ctx->MAX_POSITIVE_DESCENT = NULL;

    memset(ctx->TABLE, 0, ctx->CURRENT_CAPACITY * (size_t)(n - 1) * sizeof(int32_t));
}

static void free_context(Context *ctx) {
    free(ctx->COL_INDS);
    free(ctx->ROW_INDS);
    free(ctx->DESCENTS);
    free(ctx->TABLE);
    free(ctx->HASH_KEYS);
    free(ctx->WEIGHT_CACHE);
    free(ctx->CACHE_TAGS);
    free(ctx->MASK_OFFSETS);
    free(ctx->MASK_VERTICES);
    free(ctx->PHASE2_CANDIDATES);
    free(ctx->PHASE2_SCRATCH);
    free(ctx->MAX_POSITIVE_DESCENT);

    if (ctx->FLAT_GRAPH) {
        for (int i = 0; i < ctx->NUM_TABLEAUX; i++) {
            free(ctx->FLAT_GRAPH[i].edges);
        }
        free(ctx->FLAT_GRAPH);
    }

    memset(ctx, 0, sizeof(*ctx));
}

static int ensure_capacity(Context *ctx) {
    if (ctx->NUM_TABLEAUX < (int)ctx->CURRENT_CAPACITY) return 1;

    if (ctx->CURRENT_CAPACITY >= MAX_CAPACITY) {
        return 0;
    }

    size_t new_cap = (ctx->CURRENT_CAPACITY > MAX_CAPACITY / 2)
                   ? MAX_CAPACITY : ctx->CURRENT_CAPACITY * 2;

    size_t new_required_bytes = (size_t)((long double)estimate_context_bytes_for_capacity(ctx->N, new_cap)
                                         * MEMORY_ESTIMATE_HEADROOM);
    if (new_required_bytes < estimate_context_bytes_for_capacity(ctx->N, new_cap)) {
        new_required_bytes = estimate_context_bytes_for_capacity(ctx->N, new_cap);
    }

    if (!wait_for_additional_reservation(ctx, new_required_bytes)) {
        return 0;
    }

    ctx->COL_INDS = (uint8_t *)xrealloc(ctx->COL_INDS, new_cap * (size_t)ctx->N * sizeof(uint8_t));
    ctx->ROW_INDS = (uint8_t *)xrealloc(ctx->ROW_INDS, new_cap * (size_t)ctx->N * sizeof(uint8_t));
    ctx->DESCENTS = (uint32_t *)xrealloc(ctx->DESCENTS, new_cap * sizeof(uint32_t));
    ctx->TABLE = (int32_t *)xrealloc(ctx->TABLE, new_cap * (size_t)(ctx->N - 1) * sizeof(int32_t));
    size_t new_hash_size = next_hash_size_for_capacity(new_cap);
    int *old_hash_keys = ctx->HASH_KEYS;
    size_t old_hash_size = ctx->HASH_SIZE;

    ctx->WEIGHT_CACHE = (int32_t *)xrealloc(ctx->WEIGHT_CACHE, new_cap * sizeof(int32_t));
    ctx->CACHE_TAGS = (int *)xrealloc(ctx->CACHE_TAGS, new_cap * sizeof(int));

    if (new_hash_size != old_hash_size) {
        ctx->HASH_KEYS = (int *)xmalloc(new_hash_size * sizeof(int));
        memset(ctx->HASH_KEYS, -1, new_hash_size * sizeof(int));
        ctx->HASH_SIZE = new_hash_size;
        ctx->HASH_MASK = new_hash_size - 1;
        for (int idx = 0; idx < ctx->NUM_TABLEAUX; idx++) {
            uint8_t *key_data = &ctx->COL_INDS[(size_t)idx * ctx->N];
            uint32_t h = hash_seq(key_data, ctx->N) & (uint32_t)ctx->HASH_MASK;
            while (ctx->HASH_KEYS[h] != -1) {
                h = (h + 1) & (uint32_t)ctx->HASH_MASK;
            }
            ctx->HASH_KEYS[h] = idx;
        }
        free(old_hash_keys);
    }

    memset(ctx->TABLE + ctx->CURRENT_CAPACITY * (size_t)(ctx->N - 1), 0,
           (new_cap - ctx->CURRENT_CAPACITY) * (size_t)(ctx->N - 1) * sizeof(int32_t));
    memset(ctx->WEIGHT_CACHE + ctx->CURRENT_CAPACITY, 0,
           (new_cap - ctx->CURRENT_CAPACITY) * sizeof(int32_t));
    memset(ctx->CACHE_TAGS + ctx->CURRENT_CAPACITY, 0,
           (new_cap - ctx->CURRENT_CAPACITY) * sizeof(int));

    ctx->CURRENT_CAPACITY = new_cap;
    return 1;
}

static inline void reserve_vertex_capacity(VertexFlat *vf, int min_capacity) {
    if (min_capacity <= vf->capacity) return;
    vf->edges = (Edge *)xrealloc(vf->edges, (size_t)min_capacity * sizeof(Edge));
    vf->capacity = min_capacity;
}

static inline void add_edge_flat(Context *ctx, int u, int v, int32_t w) {
    VertexFlat *vu = &ctx->FLAT_GRAPH[u];
    VertexFlat *vv = &ctx->FLAT_GRAPH[v];
    if ((size_t)vu->size >= MAX_CAPACITY || (size_t)vv->size >= MAX_CAPACITY) {
        fprintf(stderr, "adjacency capacity exceeded\n");
        exit(1);
    }
    if (vu->size == vu->capacity) {
        int new_cap = (vu->capacity == 0) ? 8 :
            ((size_t)vu->capacity > MAX_CAPACITY / 2 ? (int)MAX_CAPACITY : vu->capacity * 2);
        reserve_vertex_capacity(vu, new_cap);
    }
    vu->edges[vu->size].target = v;
    vu->edges[vu->size].weight = w;
    vu->size++;

    if (vv->size == vv->capacity) {
        int new_cap = (vv->capacity == 0) ? 8 :
            ((size_t)vv->capacity > MAX_CAPACITY / 2 ? (int)MAX_CAPACITY : vv->capacity * 2);
        reserve_vertex_capacity(vv, new_cap);
    }
    vv->edges[vv->size].target = u;
    vv->edges[vv->size].weight = w;
    vv->size++;
}

static inline int get_weight_flat(Context *ctx, int u, int v) {
    VertexFlat *a = &ctx->FLAT_GRAPH[u];
    VertexFlat *b = &ctx->FLAT_GRAPH[v];
    int target = v;

    if (b->size < a->size) {
        a = b;
        target = u;
    }

    for (int i = 0; i < a->size; i++) {
        if (a->edges[i].target == target) {
            int weight = a->edges[i].weight;
            if (i > 0) {
                Edge hit = a->edges[i];
                a->edges[i] = a->edges[0];
                a->edges[0] = hit;
            }
            return weight;
        }
    }
    return 0;
}

static inline void sort_small_ints(int *a, int n) {
    for (int i = 1; i < n; i++) {
        int x = a[i];
        int j = i - 1;
        while (j >= 0 && a[j] > x) {
            a[j + 1] = a[j];
            j--;
        }
        a[j + 1] = x;
    }
}

static inline void sort_candidate_ints(Context *ctx, int n) {
    if (n <= 1) return;
    if (n < 64) {
        sort_small_ints(ctx->PHASE2_CANDIDATES, n);
        return;
    }

    int *src = ctx->PHASE2_CANDIDATES;
    int *dst = ctx->PHASE2_SCRATCH;
    uint32_t counts[256];

    memset(counts, 0, sizeof(counts));
    for (int i = 0; i < n; i++) counts[(src[i] >> 0) & 0xFFU]++;
    uint32_t sum = 0;
    for (int i = 0; i < 256; i++) {
        uint32_t c = counts[i];
        counts[i] = sum;
        sum += c;
    }
    for (int i = 0; i < n; i++) dst[counts[(src[i] >> 0) & 0xFFU]++] = src[i];

    memset(counts, 0, sizeof(counts));
    for (int i = 0; i < n; i++) counts[(dst[i] >> 8) & 0xFFU]++;
    sum = 0;
    for (int i = 0; i < 256; i++) {
        uint32_t c = counts[i];
        counts[i] = sum;
        sum += c;
    }
    for (int i = 0; i < n; i++) src[counts[(dst[i] >> 8) & 0xFFU]++] = dst[i];

    memset(counts, 0, sizeof(counts));
    for (int i = 0; i < n; i++) counts[(src[i] >> 16) & 0xFFU]++;
    sum = 0;
    for (int i = 0; i < 256; i++) {
        uint32_t c = counts[i];
        counts[i] = sum;
        sum += c;
    }
    for (int i = 0; i < n; i++) dst[counts[(src[i] >> 16) & 0xFFU]++] = src[i];

    memset(counts, 0, sizeof(counts));
    for (int i = 0; i < n; i++) counts[(dst[i] >> 24) & 0xFFU]++;
    sum = 0;
    for (int i = 0; i < 256; i++) {
        uint32_t c = counts[i];
        counts[i] = sum;
        sum += c;
    }
    for (int i = 0; i < n; i++) src[counts[(dst[i] >> 24) & 0xFFU]++] = dst[i];
}


static void build_desc_mask_buckets(Context *ctx) {
    size_t mask_count = descent_bucket_count(ctx->N, ctx->CURRENT_CAPACITY);
    ctx->PHASE2_CANDIDATES = (int *)xmalloc((size_t)ctx->NUM_TABLEAUX * sizeof(int));
    ctx->PHASE2_SCRATCH = (int *)xmalloc((size_t)ctx->NUM_TABLEAUX * sizeof(int));
    ctx->MAX_POSITIVE_DESCENT = (uint8_t *)xcalloc((size_t)ctx->NUM_TABLEAUX, sizeof(uint8_t));

    for (int t = 0; t < ctx->NUM_TABLEAUX; t++) {
        uint8_t max_pos = 0;
        uint32_t des_t = ctx->DESCENTS[t];
        for (int s = ctx->N - 2; s >= 0; s--) {
            if (((des_t >> s) & 1U) && ctx->TABLE[(size_t)t * (ctx->N - 1) + s] > 0) {
                max_pos = (uint8_t)(s + 1);
                break;
            }
        }
        ctx->MAX_POSITIVE_DESCENT[t] = max_pos;
    }

    if (mask_count == 0) return;
    uint32_t *counts = (uint32_t *)xcalloc(mask_count, sizeof(uint32_t));
    ctx->MASK_OFFSETS = (uint32_t *)xmalloc((mask_count + 1) * sizeof(uint32_t));
    ctx->MASK_VERTICES = (int *)xmalloc((size_t)ctx->NUM_TABLEAUX * sizeof(int));
    for (int t = 0; t < ctx->NUM_TABLEAUX; t++) counts[ctx->DESCENTS[t]]++;

    ctx->MASK_OFFSETS[0] = 0;
    for (size_t mask = 0; mask < mask_count; mask++) {
        ctx->MASK_OFFSETS[mask + 1] = ctx->MASK_OFFSETS[mask] + counts[mask];
    }

    uint32_t *cursor = (uint32_t *)xmalloc(mask_count * sizeof(uint32_t));
    memcpy(cursor, ctx->MASK_OFFSETS, mask_count * sizeof(uint32_t));

    for (int t = 0; t < ctx->NUM_TABLEAUX; t++) {
        uint32_t mask = ctx->DESCENTS[t];
        ctx->MASK_VERTICES[cursor[mask]++] = t;
    }

    free(cursor);
    free(counts);
}

// ==========================================
// Algorithms (Thread Safe - using Context)
// ==========================================
static uint32_t hash_seq(const uint8_t *data, int len) {
    uint32_t hash = 2166136261u;
    for (int i = 0; i < len; i++) {
        hash ^= data[i];
        hash *= 16777619u;
    }
    return hash;
}

static void hash_insert(Context *ctx, int val) {
    uint8_t *key_data = &ctx->COL_INDS[(size_t)val * ctx->N];
    uint32_t h = hash_seq(key_data, ctx->N) & (uint32_t)ctx->HASH_MASK;
    while (ctx->HASH_KEYS[h] != -1) {
        h = (h + 1) & (uint32_t)ctx->HASH_MASK;
    }
    ctx->HASH_KEYS[h] = val;
}

static int hash_find(Context *ctx, const uint8_t *target_seq) {
    uint32_t h = hash_seq(target_seq, ctx->N) & (uint32_t)ctx->HASH_MASK;
    while (ctx->HASH_KEYS[h] != -1) {
        int idx = ctx->HASH_KEYS[h];
        if (memcmp(&ctx->COL_INDS[(size_t)idx * ctx->N], target_seq, ctx->N) == 0) {
            return idx;
        }
        h = (h + 1) & (uint32_t)ctx->HASH_MASK;
    }
    return -1;
}

static int generate_tableaux(Context *ctx) {
    int N = ctx->N;

    int dual_pi[64] = {0};
    int max_col = ctx->PARTITION[0];
    for (int j = 0; j < max_col; j++) {
        for (int i = 0; i < ctx->PARTITION_LEN; i++) {
            if (ctx->PARTITION[i] > j) dual_pi[j]++;
        }
    }

    uint8_t r_seq[64], c_seq[64];
    int k = 0;
    for (int c = 0; c < max_col; c++) {
        for (int r = 0; r < dual_pi[c]; r++) {
            r_seq[k] = (uint8_t)(r + 1);
            c_seq[k] = (uint8_t)(c + 1);
            k++;
        }
    }

    memcpy(&ctx->COL_INDS[0], c_seq, N);
    memcpy(&ctx->ROW_INDS[0], r_seq, N);
    hash_insert(ctx, 0);

    uint32_t desc = 0;
    for (int i = 0; i < N - 1; i++) {
        if (r_seq[i] < r_seq[i + 1]) desc |= (1U << i);
    }
    ctx->DESCENTS[0] = desc;
    for (int i = 0; i < N - 1; i++) {
        if ((desc >> i) & 1U) ctx->TABLE[i] = -1;
    }

    ctx->NUM_TABLEAUX = 1;
    int m = 0;
    int finished = 0;

    uint8_t r_curr[64], c_curr[64];
    int pcl_arr[64];

    while (!finished) {
        memcpy(r_curr, &ctx->ROW_INDS[(size_t)m * N], N);
        memcpy(c_curr, &ctx->COL_INDS[(size_t)m * N], N);
        memset(pcl_arr, 0, sizeof(pcl_arr));

        int mag_j = 1;
        int pcl_len = 1;
        pcl_arr[1] = 1;

        while (mag_j < N) {
            int c_next = c_curr[mag_j];
            int r_next = r_curr[mag_j];
            int c_prev = c_curr[mag_j - 1];
            int r_prev = r_curr[mag_j - 1];
            int cond = 0;

            if (c_next == 1) cond = 1;
            else if (c_next == 1 + c_prev && r_next == r_prev) cond = 1;

            if (!cond) break;

            if (r_next == 1) {
                pcl_len++;
                pcl_arr[pcl_len] = 1;
            } else {
                pcl_arr[c_next]++;
            }
            mag_j++;
        }

        if (mag_j == N) {
            finished = 1;
        } else {
            int c_next = c_curr[mag_j];
            int r_next = r_curr[mag_j];

            if (r_next == 1) {
                pcl_len++;
                pcl_arr[pcl_len] = 1;
            } else {
                pcl_arr[c_next]++;
            }

            int k_col = c_next - 1;
            while (k_col > 0 && pcl_arr[k_col] == r_next) k_col--;
            pcl_arr[k_col]--;

            uint8_t new_r[64], new_c[64];
            int ptr = 0;
            for (int i = 1; i <= pcl_len; i++) {
                for (int h = 1; h <= pcl_arr[i]; h++) {
                    new_r[ptr] = (uint8_t)h;
                    new_c[ptr] = (uint8_t)i;
                    ptr++;
                }
            }
            new_r[ptr] = (uint8_t)(pcl_arr[k_col] + 1);
            new_c[ptr] = (uint8_t)k_col;
            ptr++;

            for (int x = mag_j + 1; x < N; x++) {
                new_r[ptr] = r_curr[x];
                new_c[ptr] = c_curr[x];
                ptr++;
            }

            if (!ensure_capacity(ctx)) return 0;

            int curr_idx = ctx->NUM_TABLEAUX;
            memcpy(&ctx->ROW_INDS[(size_t)curr_idx * N], new_r, N);
            memcpy(&ctx->COL_INDS[(size_t)curr_idx * N], new_c, N);
            hash_insert(ctx, curr_idx);
            ctx->NUM_TABLEAUX++;

            desc = 0;
            uint8_t temp_r[64], temp_c[64];

            for (int i = 0; i < N - 1; i++) {
                if (new_r[i] == new_r[i + 1]) {
                    ctx->TABLE[(size_t)curr_idx * (N - 1) + i] = curr_idx + 1;
                } else if (new_c[i] == new_c[i + 1]) {
                    ctx->TABLE[(size_t)curr_idx * (N - 1) + i] = -(curr_idx + 1);
                    desc |= (1U << i);
                } else if (new_r[i] < new_r[i + 1]) {
                    desc |= (1U << i);

                    memcpy(temp_r, new_r, N);
                    memcpy(temp_c, new_c, N);

                    uint8_t tmp = temp_r[i];
                    temp_r[i] = temp_r[i + 1];
                    temp_r[i + 1] = tmp;

                    tmp = temp_c[i];
                    temp_c[i] = temp_c[i + 1];
                    temp_c[i + 1] = tmp;

                    int neighbor_ind = hash_find(ctx, temp_c);
                    if (neighbor_ind != -1) {
                        ctx->TABLE[(size_t)curr_idx * (N - 1) + i] = neighbor_ind + 1;
                        ctx->TABLE[(size_t)neighbor_ind * (N - 1) + i] = curr_idx + 1;
                    }
                }
            }

            ctx->DESCENTS[curr_idx] = desc;
        }

        m++;
    }

    ctx->FLAT_GRAPH = (VertexFlat *)xcalloc((size_t)ctx->NUM_TABLEAUX, sizeof(VertexFlat));
    build_desc_mask_buckets(ctx);
    return 1;
}

// ==========================================
// Weighted Logic (Context Aware)
// ==========================================
static inline int resNum(Context *ctx, int u_idx, int t_idx) {
    int N = ctx->N;
    const uint8_t *u = &ctx->COL_INDS[(size_t)u_idx * N];
    const uint8_t *t = &ctx->COL_INDS[(size_t)t_idx * N];

    int k = 0;
    for (; k + 8 <= N; k += 8) {
        uint64_t a, b;
        memcpy(&a, u + k, 8);
        memcpy(&b, t + k, 8);
        uint64_t diff = a ^ b;
        if (diff != 0) {
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
            int bit_idx = __builtin_ctzll(diff);
            int byte_offset = bit_idx >> 3;
            int result = k + byte_offset;
            if (result < N) return result;
            return 0;
#else
            for (int offset = 0; offset < 8; offset++) {
                if (u[k + offset] != t[k + offset]) return k + offset;
            }
#endif
        }
    }

    for (; k < N; k++) {
        if (u[k] != t[k]) return k;
    }

    return 0;
}

static int favut(Context *ctx, int u_idx, int t_idx, int *fu, int *ft) {
    int r = resNum(ctx, u_idx, t_idx);
    if (r == 0) return 0;

    int N = ctx->N;
    uint8_t *x = &ctx->COL_INDS[(size_t)u_idx * N];
    uint8_t *y = &ctx->COL_INDS[(size_t)t_idx * N];

    int v1 = x[r];
    int v2 = y[r];
    int mn = (v1 < v2) ? v1 : v2;
    int mx = (v1 > v2) ? v1 : v2;
    mx--;

    int val_prev = x[r - 1];
    if (val_prev >= mn && val_prev <= mx) {
        *fu = u_idx;
        *ft = t_idx;
        return 1;
    } else {
        int s = r - 2;
        while (s >= 0) {
            if (x[s] >= mn && x[s] <= mx) break;
            s--;
        }
        if (s < 0) return 0;

        uint8_t z[64];
        memcpy(z, x, N);
        for (int k = s; k < r - 1; k++) z[k] = x[k + 1];
        z[r - 1] = x[s];

        uint8_t zy[64];
        memcpy(zy, z, r);
        memcpy(zy + r, y + r, N - r);

        *fu = hash_find(ctx, z);
        *ft = hash_find(ctx, zy);

        return (*fu != -1 && *ft != -1);
    }
}

static inline void bump_global_tag(Context *ctx) {
    ctx->GLOBAL_TAG++;
    if (ctx->GLOBAL_TAG == INT32_MAX) {
        memset(ctx->CACHE_TAGS, 0, ctx->CURRENT_CAPACITY * sizeof(int));
        ctx->GLOBAL_TAG = 1;
    }
}

static void cache_vertex_weights(Context *ctx, int vertex) {
    bump_global_tag(ctx);
    VertexFlat *vf = &ctx->FLAT_GRAPH[vertex];
    for (int z = 0; z < vf->size; z++) {
        int target = vf->edges[z].target;
        ctx->WEIGHT_CACHE[target] = vf->edges[z].weight;
        ctx->CACHE_TAGS[target] = ctx->GLOBAL_TAG;
    }
    ctx->WEIGHT_CACHE[vertex] = 1;
    ctx->CACHE_TAGS[vertex] = ctx->GLOBAL_TAG;
}

static int add_weight_product(int64_t *sum, int32_t a, int32_t b) {
    int64_t product = (int64_t)a * b;
    if (product < 0 || *sum > INT64_MAX - product) return 0;
    *sum += product;
    return 1;
}

static long long compute_weighted_graph(Context *ctx, long long *total_edges_out) {
    long long special_edges_count = 0;
    long long total_edges = 0;
    const int N = ctx->N;
    const int stride = N - 1;
    uint32_t *descents = ctx->DESCENTS;
    int32_t *table = ctx->TABLE;

    int *phase1_degrees = (int *)xcalloc((size_t)ctx->NUM_TABLEAUX, sizeof(int));

    // Phase 1: count simple edges first so adjacency lists start with a useful capacity.
    for (int t = 0; t < ctx->NUM_TABLEAUX; t++) {
        uint32_t des_t = descents[t];
        for (int s = 0; s < stride; s++) {
            if ((des_t >> s) & 1U) {
                int32_t val = table[(size_t)t * stride + s];
                if (val > 0) {
                    int u = val - 1;
                    if (u < t) {
                        phase1_degrees[u]++;
                        phase1_degrees[t]++;
                        total_edges++;
                    }
                }
            }
        }
    }

    for (int v = 0; v < ctx->NUM_TABLEAUX; v++) {
        if (phase1_degrees[v] > 0) {
            reserve_vertex_capacity(&ctx->FLAT_GRAPH[v], phase1_degrees[v]);
        }
    }

    for (int t = 0; t < ctx->NUM_TABLEAUX; t++) {
        uint32_t des_t = descents[t];
        for (int s = 0; s < stride; s++) {
            if ((des_t >> s) & 1U) {
                int32_t val = table[(size_t)t * stride + s];
                if (val > 0) {
                    int u = val - 1;
                    if (u < t) {
                        add_edge_flat(ctx, u, t, 1);
                    }
                }
            }
        }
    }

    free(phase1_degrees);

    // Phase 2
    for (int t = 1; t < ctx->NUM_TABLEAUX; t++) {
        uint32_t des_t = descents[t];
        int j = ctx->MAX_POSITIVE_DESCENT[t];
        if (j == 0) continue;
        int candidate_count = 0;
        uint32_t complement = ctx->FULL_DESC_MASK ^ des_t;
        uint32_t extra = complement;

        if (!ctx->MASK_OFFSETS) {
            // Preserve the baseline's ascending dependency order without a dense index.
            for (int u = 0; u < t; u++) {
                uint32_t des_u = descents[u];
                if ((des_t & des_u) == des_t && des_t != des_u)
                    ctx->PHASE2_CANDIDATES[candidate_count++] = u;
            }
        } else while (1) {
            uint32_t super = des_t | extra;
            if (super != des_t) {
                uint32_t start = ctx->MASK_OFFSETS[super];
                uint32_t end = ctx->MASK_OFFSETS[super + 1];
                for (uint32_t pos = start; pos < end; pos++) {
                    int u = ctx->MASK_VERTICES[pos];
                    if (u >= t) {
                        break;
                    }
                    ctx->PHASE2_CANDIDATES[candidate_count++] = u;
                }
            }

            if (extra == 0) {
                break;
            }
            extra = (extra - 1) & complement;
        }

        if (candidate_count > 1) {
            sort_candidate_ints(ctx, candidate_count);
        }

        for (int c = 0; c < candidate_count; c++) {
            int u = ctx->PHASE2_CANDIDATES[c];
            uint32_t des_u = descents[u];
            if ((des_t & des_u) == des_t && des_t != des_u) {
                int i = resNum(ctx, u, t);

                if (i > 0 && i < j) {
                    int i_bit = i - 1;
                    int j_bit = j - 1;
                    int in_diff = ((des_u >> i_bit) & 1U) && !((des_t >> i_bit) & 1U);

                    int fu = u, ft = t;
                    if (!in_diff) {
                        if (!favut(ctx, u, t, &fu, &ft)) {
                            fu = u;
                            ft = t;
                        }
                    }

                    uint32_t des_fu = descents[fu];
                    uint32_t des_ft = descents[ft];
                    int in_diff_f = ((des_fu >> i_bit) & 1U) && !((des_ft >> i_bit) & 1U);

                    if (in_diff_f) {
                        int64_t weight = 0;

                        if (ft < t) {
                            if (ft >= 0 && fu >= 0) {
                                int w = get_weight_flat(ctx, ft, fu);
                                if (w != 0) weight = w;
                            }
                        } else {
                            cache_vertex_weights(ctx, fu);

                            int32_t val_v = table[(size_t)ft * stride + j_bit];
                            int v = abs(val_v) - 1;

                            if (v >= 0) {
                                uint32_t des_v = descents[v];
                                int i_in_des_v = (des_v >> i_bit) & 1U;

                                if (!i_in_des_v) {
                                    int64_t sumji = 0, sumij = 0;
                                    VertexFlat *v_v = &ctx->FLAT_GRAPH[v];
                                    for (int z = 0; z < v_v->size; z++) {
                                        int x = v_v->edges[z].target;
                                        int w_vx = v_v->edges[z].weight;
                                        int w_xfu = (ctx->CACHE_TAGS[x] == ctx->GLOBAL_TAG) ? (int)ctx->WEIGHT_CACHE[x] : 0;
                                        if (w_xfu != 0) {
                                            uint32_t des_x = descents[x];
                                            if (x != ft && ((des_x >> j_bit) & 1U) && !((des_x >> i_bit) & 1U)) {
                                                if (!add_weight_product(&sumji, w_vx, w_xfu)) return -1;
                                            }
                                            if (((des_x >> i_bit) & 1U) && !((des_x >> j_bit) & 1U)) {
                                                if (!add_weight_product(&sumij, w_vx, w_xfu)) return -1;
                                            }
                                        }
                                    }
                                    weight = sumij - sumji;
                                }
                                else if (i == j - 1 && i_in_des_v) {
                                    int32_t val_w = table[(size_t)v * stride + i_bit];
                                    if (val_w > 0) {
                                        int w_idx = val_w - 1;
                                        int64_t sumji = 0, sumij = 0;
                                        VertexFlat *v_w = &ctx->FLAT_GRAPH[w_idx];
                                        for (int z = 0; z < v_w->size; z++) {
                                            int x = v_w->edges[z].target;
                                            int w_wx = v_w->edges[z].weight;
                                            uint32_t des_x = descents[x];
                                            int i_idx = (des_x >> i_bit) & 1U;
                                            int j_idx = (des_x >> j_bit) & 1U;
                                            int y = -1;

                                            if (x != v && i_idx && !j_idx) {
                                                int32_t t_jx = table[(size_t)x * stride + j_bit];
                                                if (abs(t_jx) - 1 > x) {
                                                    int tx = abs(t_jx) - 1;
                                                    if (!((descents[tx] >> i_bit) & 1U)) y = tx;
                                                } else {
                                                    int32_t t_ix = table[(size_t)x * stride + i_bit];
                                                    if (abs(t_ix) - 1 < x && t_ix > 0) {
                                                        int tix = abs(t_ix) - 1;
                                                        if ((descents[tix] >> j_bit) & 1U) y = tix;
                                                    }
                                                }
                                            }

                                            if (j_idx && !i_idx) {
                                                int32_t t_ix = table[(size_t)x * stride + i_bit];
                                                if (abs(t_ix) - 1 > x) {
                                                    int tix = abs(t_ix) - 1;
                                                    if (!((descents[tix] >> j_bit) & 1U)) y = tix;
                                                } else {
                                                    int32_t t_jx = table[(size_t)x * stride + j_bit];
                                                    if (abs(t_jx) - 1 < x && t_jx > 0) {
                                                        int tjx = abs(t_jx) - 1;
                                                        if ((descents[tjx] >> i_bit) & 1U) y = tjx;
                                                    }
                                                }
                                            }

                                            if (y != -1) {
                                                int w_yfu = (ctx->CACHE_TAGS[y] == ctx->GLOBAL_TAG) ? (int)ctx->WEIGHT_CACHE[y] : 0;
                                                if (w_yfu && !add_weight_product(&sumji, w_wx, w_yfu)) return -1;
                                            }
                                        }
                                        weight = sumji - sumij;
                                    }
                                }
                            }
                        }

                        if (weight > 0) {
                            if (weight > INT32_MAX) return -1;
                            add_edge_flat(ctx, u, t, (int32_t)weight);
                            total_edges++;
                            if (weight != 1) {
                                special_edges_count++;
                                if (DEBUG_MODE) {
                                    printf("[!] Special Edge: %d -- %d (Weight: %lld)\n", u + 1, t + 1, (long long)weight);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if (total_edges_out) *total_edges_out = total_edges;
    return special_edges_count;
}

// ==========================================
// Helpers
// ==========================================
static double get_specht_dimension_approx(int n, const int *part, int len) {
    double log_num = lgamma(n + 1.0);
    int conjugate[128] = {0};
    int max_col = part[0];

    for (int j = 0; j < max_col; j++) {
        for (int i = 0; i < len; i++) {
            if (part[i] > j) conjugate[j]++;
        }
    }

    double log_denom = 0.0;
    for (int i = 0; i < len; i++) {
        for (int j = 0; j < part[i]; j++) {
            int hook_length = (part[i] - j) + (conjugate[j] - i) - 1;
            log_denom += log((double)hook_length);
        }
    }

    return exp(log_num - log_denom);
}

// ==========================================
// Export: CSR-like upper adjacency list
// ==========================================
static void store_le(uint8_t *out, uint64_t value, size_t width) {
    for (size_t i = 0; i < width; i++) out[i] = (uint8_t)(value >> (8 * i));
}

static int write_le_array(FILE *f, const void *data, size_t count, size_t width) {
    const uint32_t one = 1;
    if (*(const uint8_t *)&one == 1) return fwrite(data, width, count, f) == count;
    const uint8_t *src = data;
    uint8_t buffer[4096];
    while (count) {
        size_t chunk = count < sizeof(buffer) / width ? count : sizeof(buffer) / width;
        for (size_t i = 0; i < chunk; i++) {
            for (size_t j = 0; j < width; j++) buffer[i * width + j] = src[i * width + width - 1 - j];
        }
        if (fwrite(buffer, width, chunk, f) != chunk) return 0;
        src += chunk * width;
        count -= chunk;
    }
    return 1;
}

static int compare_edges_by_target(const void *a, const void *b) {
    const Edge *ea = a, *eb = b;
    return (ea->target > eb->target) - (ea->target < eb->target);
}

static int export_csr_upper(Context *ctx, const char *filename) {
    char tmp_filename[272];
    if (snprintf(tmp_filename, sizeof(tmp_filename), "%s.tmp", filename) >= (int)sizeof(tmp_filename)) return 0;
    FILE *f = fopen(tmp_filename, "wb");
    if (!f) {
        fprintf(stderr, "Failed to open %s for writing\n", filename);
        return 0;
    }

    uint32_t num_vertices = (uint32_t)ctx->NUM_TABLEAUX;
    uint32_t *degrees = (uint32_t *)xcalloc(num_vertices, sizeof(uint32_t));
    uint64_t *offsets = (uint64_t *)xmalloc((num_vertices + 1) * sizeof(uint64_t));

    uint64_t num_edges = 0;
    for (uint32_t u = 0; u < num_vertices; u++) {
        VertexFlat *vu = &ctx->FLAT_GRAPH[u];
        if (vu->size > 1) qsort(vu->edges, (size_t)vu->size, sizeof(Edge), compare_edges_by_target);
        for (int i = 0; i < vu->size; i++) {
            uint32_t v = (uint32_t)vu->edges[i].target;
            if (u < v) {
                degrees[u]++;
                num_edges++;
            }
        }
    }

    offsets[0] = 0;
    for (uint32_t u = 0; u < num_vertices; u++) {
        offsets[u + 1] = offsets[u] + degrees[u];
    }

    uint32_t *targets = NULL;
    int32_t *weights = NULL;
    uint64_t *cursor = NULL;

    if (num_edges > 0) {
        if (num_edges > SIZE_MAX / sizeof(uint32_t)) {
            fclose(f);
            remove(tmp_filename);
            free(degrees);
            free(offsets);
            return 0;
        }
        targets = (uint32_t *)xmalloc((size_t)num_edges * sizeof(uint32_t));
        weights = (int32_t *)xmalloc((size_t)num_edges * sizeof(int32_t));
        cursor = (uint64_t *)xmalloc(num_vertices * sizeof(uint64_t));

        memcpy(cursor, offsets, num_vertices * sizeof(uint64_t));

        for (uint32_t u = 0; u < num_vertices; u++) {
            VertexFlat *vu = &ctx->FLAT_GRAPH[u];
            for (int i = 0; i < vu->size; i++) {
                uint32_t v = (uint32_t)vu->edges[i].target;
                if (u < v) {
                    if (vu->edges[i].weight <= 0) {
                        fprintf(stderr, "Nonpositive edge weight in %s: %d\n",
                                filename, vu->edges[i].weight);
                        fclose(f);
                        remove(tmp_filename);
                        free(degrees);
                        free(offsets);
                        free(targets);
                        free(weights);
                        free(cursor);
                        return 0;
                    }
                    uint64_t pos = cursor[u]++;
                    targets[pos] = v;
                    weights[pos] = vu->edges[i].weight;
                }
            }
        }
    }

    uint8_t hdr[32] = {0};
    store_le(hdr, GRAPH_MAGIC, 4);
    store_le(hdr + 4, GRAPH_VERSION, 4);
    store_le(hdr + 8, (uint32_t)ctx->N, 4);
    store_le(hdr + 12, (uint32_t)ctx->PARTITION_LEN, 4);
    store_le(hdr + 16, num_vertices, 4);
    store_le(hdr + 24, num_edges, 8);

    uint32_t part_u32[64];
    for (int i = 0; i < ctx->PARTITION_LEN; i++) {
        part_u32[i] = (uint32_t)ctx->PARTITION[i];
    }

    int ok = 1;
    ok &= (fwrite(hdr, sizeof(hdr), 1, f) == 1);
    ok &= write_le_array(f, part_u32, (size_t)ctx->PARTITION_LEN, sizeof(uint32_t));
    ok &= write_le_array(f, offsets, (size_t)num_vertices + 1, sizeof(uint64_t));

    if (num_edges > 0) {
        ok &= write_le_array(f, targets, (size_t)num_edges, sizeof(uint32_t));
        ok &= write_le_array(f, weights, (size_t)num_edges, sizeof(int32_t));
    }

    if (fclose(f) != 0) ok = 0;
    if (ok && rename(tmp_filename, filename) != 0) ok = 0;
    if (!ok) remove(tmp_filename);
    free(degrees);
    free(offsets);
    free(targets);
    free(weights);
    free(cursor);

    return ok;
}

// ==========================================
// Worker
// ==========================================
typedef enum {
    TASK_EXEC_SUCCESS = 1,
    TASK_EXEC_FAILED = 0
} TaskExecResult;

static TaskExecResult process_partition_task(const PartitionTask *task,
                                             size_t *reserved_out,
                                             char *fail_reason,
                                             size_t fail_reason_sz) {
    Context ctx;
    init_context(&ctx,
                 task->n,
                 task->partition,
                 task->len,
                 task->est_bytes,
                 task->initial_capacity);

    if (DEBUG_MODE) {
        #pragma omp critical
        {
            printf("DEBUG: Processing %s (N=%d)\n", task->part_str, task->n);
        }
    }

    if (!generate_tableaux(&ctx)) {
        snprintf(fail_reason, fail_reason_sz,
                 "capacity limit or memory-growth wait timeout during tableau generation");
        *reserved_out = ctx.RESERVED_BYTES;
        free_context(&ctx);
        return TASK_EXEC_FAILED;
    }

    long long total_edges = 0;
    long long specials = compute_weighted_graph(&ctx, &total_edges);
    if (specials < 0) {
        snprintf(fail_reason, fail_reason_sz, "weight recurrence overflow (int64 sum or positive weight > INT32_MAX)");
        *reserved_out = ctx.RESERVED_BYTES;
        free_context(&ctx);
        return TASK_EXEC_FAILED;
    }

    #pragma omp critical
    {
        if (DEBUG_MODE) {
            printf(">> Partition %s: %d tableaux, %lld edges, %lld specials.\n",
                   task->part_str, ctx.NUM_TABLEAUX, total_edges, specials);
        } else {
            if (specials > 0) {
                printf("[ALERT] %s: %lld Special Edges (Total: %lld)\n",
                       task->part_str, specials, total_edges);
            } else {
                printf("Processed %s (N=%d, Dim=%.0f)\n",
                       task->part_str, task->n, task->dim_approx);
            }
        }
    }

    int export_ok = 1;
    {
        char dir_name[64];
        char filename[256];

        snprintf(dir_name, sizeof(dir_name), "S_%d", task->n);
        snprintf(filename, sizeof(filename), "%s/%s.bin", dir_name, task->part_str);

        if (!ensure_dir_exists(dir_name)) {
            fprintf(stderr, "[ERROR] Could not create directory %s\n", dir_name);
            export_ok = 0;
        } else {
            export_ok = export_csr_upper(&ctx, filename);
            if (!export_ok) {
                fprintf(stderr, "[ERROR] Failed to export %s\n", filename);
            }
        }
    }

    if (!export_ok) {
        snprintf(fail_reason, fail_reason_sz, "export failed");
        *reserved_out = ctx.RESERVED_BYTES;
        free_context(&ctx);
        return TASK_EXEC_FAILED;
    }

    omp_set_lock(&LOG_LOCK);
    append_completed_log(task, ctx.NUM_TABLEAUX, total_edges, specials);
    omp_unset_lock(&LOG_LOCK);

    *reserved_out = ctx.RESERVED_BYTES;
    free_context(&ctx);
    return TASK_EXEC_SUCCESS;
}

// ==========================================
// Task Collection / Preparation
// ==========================================
static void collect_task(int n, const int *part, int len) {
    int canon[64];
    memcpy(canon, part, len * sizeof(int));
    int canon_len = len;
    canonicalize_partition_lexmax(canon, &canon_len);

    if (TASK_COUNT >= TASK_CAPACITY) {
        TASK_CAPACITY *= 2;
        ALL_TASKS = (PartitionTask *)xrealloc(ALL_TASKS, TASK_CAPACITY * sizeof(PartitionTask));
    }

    ALL_TASKS[TASK_COUNT].n = n;
    ALL_TASKS[TASK_COUNT].len = canon_len;
    memcpy(ALL_TASKS[TASK_COUNT].partition, canon, canon_len * sizeof(int));
    ALL_TASKS[TASK_COUNT].part_str[0] = '\0';
    ALL_TASKS[TASK_COUNT].dim_approx = 0.0;
    ALL_TASKS[TASK_COUNT].est_bytes = 0;
    ALL_TASKS[TASK_COUNT].initial_capacity = 0;
    ALL_TASKS[TASK_COUNT].attempts = 0;
    ALL_TASKS[TASK_COUNT].state = TASK_STATE_PENDING;
    TASK_COUNT++;
}

static void generate_partitions_recursive(int n, int max_val, int *buffer, int depth, int target_n) {
    if (n == 0) {
        if (is_partition_canonical_lexmax(buffer, depth)) {
            collect_task(target_n, buffer, depth);
        }
        return;
    }

    int start = (max_val < n) ? max_val : n;
    for (int i = start; i >= 1; i--) {
        buffer[depth] = i;
        generate_partitions_recursive(n - i, i, buffer, depth + 1, target_n);
    }
}

static void prepare_tasks_for_run(void) {
    TASK_PENDING_COUNT = 0;
    TASK_RUNNING_COUNT = 0;
    TASK_DONE_COUNT = 0;
    TASK_DEFERRED_COUNT = 0;
    TASK_FAILED_COUNT = 0;

    for (int i = 0; i < TASK_COUNT; i++) {
        PartitionTask *task = &ALL_TASKS[i];
        partition_to_string(task->partition, task->len, task->part_str, sizeof(task->part_str));
        if (!FORCE_SINGLE_PARTITION && is_in_completed_log(task->part_str)) {
            task->state = TASK_STATE_SKIP;
            continue;
        }
        task->dim_approx = get_specht_dimension_approx(task->n, task->partition, task->len);
        uint64_t dim_exact = exact_specht_dimension_capped(task->n, task->partition, task->len,
                                                           (uint64_t)MAX_CAPACITY + 1u);
        if (dim_exact > MAX_CAPACITY) {
            task->state = TASK_STATE_FAILED;
            TASK_FAILED_COUNT++;
            fprintf(stderr, "[ERROR] %s: dimension exceeds supported capacity %zu\n", task->part_str, MAX_CAPACITY);
            append_failed_log(task, "dimension exceeds supported int32 tableau capacity");
            continue;
        }
        task->initial_capacity = (size_t)((dim_exact == 0) ? 1 : dim_exact);
        task->est_bytes = estimate_context_bytes_for_capacity(task->n, task->initial_capacity);
        task->est_bytes = (size_t)((long double)task->est_bytes * MEMORY_ESTIMATE_HEADROOM);
        task->attempts = 0;

        task->state = TASK_STATE_PENDING;
        TASK_PENDING_COUNT++;
    }
}

// ==========================================
// Scheduler
// ==========================================
static int try_acquire_next_task(int *out_idx) {
    int idx = -1;
    size_t budget_snapshot = 0;

    omp_set_lock(&GLOBAL_LOCK);
    for (int i = 0; i < TASK_COUNT; i++) {
        if (ALL_TASKS[i].state == TASK_STATE_PENDING) {
            size_t budget = compute_usable_budget_bytes_unlocked(GLOBAL_RESERVED_BYTES);
            if (GLOBAL_RESERVED_BYTES <= budget &&
                ALL_TASKS[i].est_bytes <= (budget - GLOBAL_RESERVED_BYTES)) {
                GLOBAL_RESERVED_BYTES += ALL_TASKS[i].est_bytes;
                ALL_TASKS[i].state = TASK_STATE_RUNNING;
                ALL_TASKS[i].attempts++;
                TASK_PENDING_COUNT--;
                TASK_RUNNING_COUNT++;
                LAST_PROGRESS_TIME = omp_get_wtime();
                idx = i;
                budget_snapshot = budget;
                break;
            }
        }
    }
    omp_unset_lock(&GLOBAL_LOCK);

    if (idx != -1) {
        omp_set_lock(&LOG_LOCK);
        append_started_log(&ALL_TASKS[idx], budget_snapshot);
        omp_unset_lock(&LOG_LOCK);
        *out_idx = idx;
        return 1;
    }

    return -1;
}

static int maybe_defer_remaining_pending_tasks(void) {
    int should_defer = 0;
    int *indices = NULL;
    int count = 0;
    size_t budget_snapshot = 0;

    omp_set_lock(&GLOBAL_LOCK);
    if (TASK_PENDING_COUNT > 0 &&
        TASK_RUNNING_COUNT == 0 &&
        MEMORY_WAIT_SECONDS >= 0 &&
        (omp_get_wtime() - LAST_PROGRESS_TIME) >= (double)MEMORY_WAIT_SECONDS) {

        budget_snapshot = compute_usable_budget_bytes_unlocked(GLOBAL_RESERVED_BYTES);
        indices = (int *)xmalloc((size_t)TASK_PENDING_COUNT * sizeof(int));

        for (int i = 0; i < TASK_COUNT; i++) {
            if (ALL_TASKS[i].state == TASK_STATE_PENDING) {
                ALL_TASKS[i].state = TASK_STATE_DEFERRED;
                indices[count++] = i;
            }
        }

        TASK_DEFERRED_COUNT += count;
        TASK_PENDING_COUNT = 0;
        should_defer = 1;
        LAST_PROGRESS_TIME = omp_get_wtime();
    }
    omp_unset_lock(&GLOBAL_LOCK);

    if (should_defer) {
        omp_set_lock(&LOG_LOCK);
        for (int k = 0; k < count; k++) {
            append_deferred_log(&ALL_TASKS[indices[k]],
                                "not enough usable RAM before timeout",
                                budget_snapshot);
        }
        omp_unset_lock(&LOG_LOCK);
        free(indices);
        return 1;
    }

    return 0;
}

static void run_scheduler(void) {
    LAST_PROGRESS_TIME = omp_get_wtime();

    #pragma omp parallel num_threads(THREADS_TO_USE)
    {
        while (1) {
            int idx = -1;
            int got_task = try_acquire_next_task(&idx);

            if (got_task == 1) {
                char fail_reason[256] = "";
                size_t reserved_bytes = 0;
                TaskExecResult result = process_partition_task(&ALL_TASKS[idx],
                                                              &reserved_bytes,
                                                              fail_reason,
                                                              sizeof(fail_reason));

                release_reserved_bytes_after_task(reserved_bytes);

                omp_set_lock(&GLOBAL_LOCK);
                if (ALL_TASKS[idx].state == TASK_STATE_RUNNING) {
                    TASK_RUNNING_COUNT--;
                    if (result == TASK_EXEC_SUCCESS) {
                        ALL_TASKS[idx].state = TASK_STATE_DONE;
                        TASK_DONE_COUNT++;
                    } else {
                        ALL_TASKS[idx].state = TASK_STATE_FAILED;
                        TASK_FAILED_COUNT++;
                    }
                    LAST_PROGRESS_TIME = omp_get_wtime();
                }
                omp_unset_lock(&GLOBAL_LOCK);

                if (result != TASK_EXEC_SUCCESS) {
                    omp_set_lock(&LOG_LOCK);
                    append_failed_log(&ALL_TASKS[idx], fail_reason[0] ? fail_reason : "unknown");
                    omp_unset_lock(&LOG_LOCK);
                }
                continue;
            }

            int pending, running;
            omp_set_lock(&GLOBAL_LOCK);
            pending = TASK_PENDING_COUNT;
            running = TASK_RUNNING_COUNT;
            omp_unset_lock(&GLOBAL_LOCK);

            if (pending == 0 && running == 0) {
                break;
            }

            if (maybe_defer_remaining_pending_tasks()) {
                break;
            }

            sleep_millis(MEMORY_POLL_MILLISECONDS);
        }
    }
}

// ==========================================
// CLI
// ==========================================
static void print_usage(FILE *stream, const char *prog) {
    fprintf(stream,
        "Usage:\n"
        "  %s --partition 3_2_1 --dir data\n"
        "  %s --min-n 1 --max-n 8 --threads 1\n\n"
        "Options:\n"
        "  --help                    Show this help and exit\n"
        "  --partition <p>            Run exactly one partition (canonicalized up to conjugate)\n"
        "  --min-n <a>                Range mode lower bound (default %d)\n"
        "  --max-n <b>                Range mode upper bound (default %d)\n"
        "  --threads <t>              Number of OpenMP worker threads (default %d)\n"
        "  --dir <path>               Root directory for graphs and logs (default data)\n"
        "  --memory-fraction <x>      Fraction of usable RAM to target (default %.2f)\n"
        "  --memory-reserve-mb <m>    Fixed RAM reserve in MB (default %d)\n"
        "  --memory-wait-seconds <s>  Wait before deferring pending tasks (default %d)\n\n"
        "Supported n: 1..32. All canonical graphs are exported as CSR v3 (.bin).\n"
        "Range runs resume from completed_partitions.log; --partition always reruns.\n",
        prog, prog, MIN_N, MAX_N, DEFAULT_THREAD_COUNT, DEFAULT_MEMORY_FRACTION,
        DEFAULT_MEMORY_RESERVE_MB, DEFAULT_MEMORY_WAIT_SECONDS);
}

static int parse_integer(const char *s, long long min, long long max, long long *out) {
    if (!isdigit((unsigned char)*s)) return 0;
    char *end;
    errno = 0;
    long long value = strtoll(s, &end, 10);
    if (errno || *end || value < min || value > max) return 0;
    *out = value;
    return 1;
}

// ==========================================
// Main
// ==========================================
int main(int argc, char **argv) {
    if (argc == 1) {
        print_usage(stdout, argv[0]);
        return 0;
    }
    double start = omp_get_wtime();
    const char *single_partition_str = NULL;

    for (int i = 1; i < argc; i++) {
        const char *option = argv[i];
        if (strcmp(option, "--help") == 0) {
            print_usage(stdout, argv[0]);
            return 0;
        }
        if (i + 1 >= argc) {
            fprintf(stderr, "Missing value or unknown option: %s\n", option);
            print_usage(stderr, argv[0]);
            return 1;
        }
        const char *value = argv[++i];
        long long integer;
        if (strcmp(option, "--partition") == 0) {
            single_partition_str = value;
        } else if (strcmp(option, "--dir") == 0) {
            if (!*value) goto invalid_value;
            OUTPUT_DIR = value;
        } else if (strcmp(option, "--min-n") == 0 || strcmp(option, "--max-n") == 0) {
            if (!parse_integer(value, 1, MAX_SUPPORTED_N, &integer)) goto invalid_value;
            if (strcmp(option, "--min-n") == 0) RANGE_MIN_N = (int)integer;
            else RANGE_MAX_N = (int)integer;
        } else if (strcmp(option, "--threads") == 0) {
            if (!parse_integer(value, 1, INT_MAX, &integer)) goto invalid_value;
            THREADS_TO_USE = (int)integer;
        } else if (strcmp(option, "--memory-fraction") == 0) {
            char *end;
            errno = 0;
            MEMORY_FRACTION = strtod(value, &end);
            if (errno || end == value || *end || !isfinite(MEMORY_FRACTION) ||
                !(MEMORY_FRACTION > 0.0 && MEMORY_FRACTION <= 1.0)) goto invalid_value;
        } else if (strcmp(option, "--memory-reserve-mb") == 0) {
            if (!parse_integer(value, 0, (long long)(SIZE_MAX / (1024ULL * 1024ULL)), &integer)) goto invalid_value;
            MEMORY_RESERVE_BYTES = (size_t)integer * 1024ULL * 1024ULL;
        } else if (strcmp(option, "--memory-wait-seconds") == 0) {
            if (!parse_integer(value, 0, INT_MAX, &integer)) goto invalid_value;
            MEMORY_WAIT_SECONDS = (int)integer;
        } else {
            fprintf(stderr, "Unknown option: %s\n", option);
            print_usage(stderr, argv[0]);
            return 1;
        }
        continue;
invalid_value:
        fprintf(stderr, "Invalid value for %s: %s\n", option, value);
        return 1;
    }

    if (RANGE_MIN_N > RANGE_MAX_N) {
        fprintf(stderr, "Invalid range: min-n > max-n\n");
        return 1;
    }

    int part[64], len = 0, n = 0;
    if (single_partition_str && !parse_partition_string(single_partition_str, part, &len, &n)) {
        fprintf(stderr, "Invalid partition (positive descending parts, sum 1..32): %s\n", single_partition_str);
        return 1;
    }
    if (!ensure_output_root(OUTPUT_DIR)) {
        fprintf(stderr, "Could not create or enter output root %s: %s\n", OUTPUT_DIR, strerror(errno));
        return 1;
    }
    ALL_TASKS = (PartitionTask *)xmalloc(TASK_CAPACITY * sizeof(PartitionTask));
    load_completed_log();

    if (single_partition_str) {
        canonicalize_partition_lexmax(part, &len);
        FORCE_SINGLE_PARTITION = 1;
        collect_task(n, part, len);

        char canon[128];
        partition_to_string(part, len, canon, sizeof(canon));
        printf("Running only canonical partition %s (N=%d)\n", canon, n);
    } else {
        printf("Generating canonical task list for N=%d..%d...\n", RANGE_MIN_N, RANGE_MAX_N);
        int buffer[64];
        for (int n = RANGE_MIN_N; n <= RANGE_MAX_N; n++) {
            generate_partitions_recursive(n, n, buffer, 0, n);
        }
    }

    prepare_tasks_for_run();

    omp_init_lock(&GLOBAL_LOCK);
    omp_init_lock(&LOG_LOCK);

    size_t available_now_mb = get_available_memory_bytes() / (1024ULL * 1024ULL);
    size_t budget_now_mb = get_current_usable_budget_bytes() / (1024ULL * 1024ULL);
    size_t reserve_mb = MEMORY_RESERVE_BYTES / (1024ULL * 1024ULL);

    printf("Total Tasks Generated: %d\n", TASK_COUNT);
    printf("Completed log loaded entries: %d\n", COMPLETED_COUNT);
    printf("Threads to use: %d\n", THREADS_TO_USE);
    printf("Available RAM now: %zu MB\n", available_now_mb);
    printf("RAM policy: fraction=%.2f, reserve=%zu MB, wait=%d s\n",
           MEMORY_FRACTION, reserve_mb, MEMORY_WAIT_SECONDS);
    printf("Usable budget now: %zu MB\n", budget_now_mb);
    printf("Runnable tasks after completed/capacity filter: %d\n", TASK_PENDING_COUNT);

    run_scheduler();

    printf("\nAll Done. Total Time: %.2f s\n", omp_get_wtime() - start);
    printf("Summary: done=%d deferred=%d failed=%d still-pending=%d\n",
           TASK_DONE_COUNT, TASK_DEFERRED_COUNT, TASK_FAILED_COUNT, TASK_PENDING_COUNT);

    omp_destroy_lock(&GLOBAL_LOCK);
    omp_destroy_lock(&LOG_LOCK);

    free_completed_partitions();
    free(ALL_TASKS);
    return (TASK_FAILED_COUNT || TASK_DEFERRED_COUNT || TASK_PENDING_COUNT) ? 1 : 0;
}
