#define main wgraphgen_cli_main
#include "wgraphgen.c"
#undef main
#include <assert.h>

static uint64_t read_le(const uint8_t *bytes, size_t width) {
    uint64_t value = 0;
    for (size_t i = 0; i < width; i++) value |= (uint64_t)bytes[i] << (8 * i);
    return value;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <temporary-output.bin>\n", argv[0]);
        return 2;
    }

    const int part[] = {3, 1};
    Context ctx;
    init_context(&ctx, 4, part, 2, 0, 3);
    ctx.NUM_TABLEAUX = 3;
    ctx.FLAT_GRAPH = xcalloc(3, sizeof(VertexFlat));
    add_edge_flat(&ctx, 0, 2, 300);
    add_edge_flat(&ctx, 0, 1, 1);
    cache_vertex_weights(&ctx, 0);
    assert(ctx.WEIGHT_CACHE[2] == 300);
    assert(ctx.CACHE_TAGS[2] == ctx.GLOBAL_TAG);
    assert(ctx.WEIGHT_CACHE[0] == 1);

    int64_t sum = 0;
    assert(add_weight_product(&sum, 300, 300));
    assert(sum == 90000);
    sum = INT64_MAX;
    assert(!add_weight_product(&sum, 1, 1));
    sum = 0;
    assert(add_weight_product(&sum, INT32_MAX, INT32_MAX));
    assert(sum == (int64_t)INT32_MAX * INT32_MAX);
    assert(descent_bucket_count(32, 31) == 0);

    assert(export_csr_upper(&ctx, argv[1]));
    FILE *f = fopen(argv[1], "rb");
    assert(f);
    uint8_t bytes[88];
    assert(fread(bytes, 1, sizeof(bytes), f) == sizeof(bytes));
    assert(fgetc(f) == EOF);
    assert(fclose(f) == 0);
    assert(read_le(bytes, 4) == GRAPH_MAGIC);
    assert(read_le(bytes + 4, 4) == 3);
    assert(read_le(bytes + 8, 4) == 4);
    assert(read_le(bytes + 12, 4) == 2);
    assert(read_le(bytes + 16, 4) == 3);
    assert(read_le(bytes + 20, 4) == 0);
    assert(read_le(bytes + 24, 8) == 2);
    assert(read_le(bytes + 32, 4) == 3);
    assert(read_le(bytes + 36, 4) == 1);
    assert(read_le(bytes + 40, 8) == 0);
    for (size_t offset = 48; offset < 72; offset += 8) assert(read_le(bytes + offset, 8) == 2);
    assert(read_le(bytes + 72, 4) == 1);
    assert(read_le(bytes + 76, 4) == 2);
    assert(read_le(bytes + 80, 4) == 1);
    assert(read_le(bytes + 84, 4) == 300);
    free_context(&ctx);
    assert(remove(argv[1]) == 0);
    puts("weight-300 cache/export, sorted CSR v3, and int64 overflow checks passed");
    return 0;
}
