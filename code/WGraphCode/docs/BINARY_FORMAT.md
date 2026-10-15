# Binary graph format

Both implementations write version 3 of the upper-triangular CSR format.
The supported platforms are 64-bit little-endian Linux and macOS. The file
does not contain the tableau labels or descent sets; these are determined
by the partition and the common tableau enumeration order.

## Header

The header occupies 32 bytes. All integers use little-endian encoding.

| Byte offset | Type | Field |
| ---: | --- | --- |
| 0 | `uint32` | Magic number `0x55474C31` |
| 4 | `uint32` | Format version: `3` |
| 8 | `uint32` | `n`, the sum of partition parts |
| 12 | `uint32` | Number of partition parts |
| 16 | `uint32` | Number of vertices |
| 20 | 4 bytes | Reserved padding, zero |
| 24 | `uint64` | Number of stored edges |

The remaining arrays follow consecutively:

1. Partition parts: `uint32[partition_len]`.
2. CSR offsets: `uint64[num_vertices + 1]`.
3. Targets: `uint32[num_edges]`.
4. Weights: `int32[num_edges]`.

For a vertex `u`, its stored outgoing edges occupy positions
`offsets[u] .. offsets[u+1]`. Each corresponding target `v` satisfies
`u < v`, and its weight is positive. An edge is stored exactly once; use
both endpoints when reconstructing the full adjacency or degrees. The
first offset is zero and the last is `num_edges`.

Version 2 uses the same header and arrays except that its weights are
`uint8[num_edges]`. The graph-inspection tool and the Rust restriction
loader accept both versions.

## Vertex ordering

Vertices are zero-indexed standard Young tableaux of the given shape. The
first tableau is filled down columns from left to right. Equivalently, the
enumeration groups tableaux by the removable corner containing the largest
entry, scanning removable rows from top to bottom. Each such block contains
the tableaux of the remaining shape in the same recursive order. Its size
is the hook-length dimension of that remaining shape.

For `(3,2)`, vertex 0 is:

```text
1 3 5
2 4
```

The descent set consists of entries `i` such that `i+1` lies in a lower row
than `i`. The generator constructs this information internally.

## Validation and comparison

`tools/graph_info.py` checks the partition, hook-length dimension, exact
file size, CSR offsets, endpoint ranges, positive weights, and absence of
duplicate edges. It reports all weight frequencies and a canonical SHA-256
checksum. The checksum sorts targets within each source row, so it is
independent of adjacency insertion order and format version. The comparison
option checks equality of every weighted edge, including unit edges.
