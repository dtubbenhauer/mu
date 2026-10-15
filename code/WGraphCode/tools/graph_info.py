#!/usr/bin/env python3
"""Validate a WGraphGenerator CSR file and report its graph statistics."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
import mmap
from pathlib import Path
import struct


MAGIC = 0x55474C31
HEADER_SIZE = 32


def tableau_dimension(shape: tuple[int, ...]) -> int:
    denominator = 1
    for row, width in enumerate(shape):
        for col in range(width):
            below = sum(other_width > col for other_width in shape[row + 1 :])
            denominator *= width - col + below
    return math.factorial(sum(shape)) // denominator


class Graph:
    def __init__(self, path: Path):
        self.path = path
        self._file = path.open("rb")
        self._data = None
        try:
            if path.stat().st_size < HEADER_SIZE:
                raise ValueError(f"truncated header: {path}")
            self._data = mmap.mmap(self._file.fileno(), 0, access=mmap.ACCESS_READ)
            magic, self.version, self.n, shape_len, self.vertices = struct.unpack_from(
                "<IIIII", self._data
            )
            self.edges = struct.unpack_from("<Q", self._data, 24)[0]
            if magic != MAGIC or self.version not in (2, 3):
                raise ValueError(f"unsupported CSR header: {path}")
            if not (1 <= shape_len <= 64):
                raise ValueError(f"invalid partition length: {path}")
            self.shape = struct.unpack_from(f"<{shape_len}I", self._data, HEADER_SIZE)
            if (
                sum(self.shape) != self.n
                or min(self.shape) < 1
                or tuple(sorted(self.shape, reverse=True)) != self.shape
            ):
                raise ValueError(f"invalid partition: {path}")
            if self.vertices != tableau_dimension(self.shape):
                raise ValueError(f"vertex count disagrees with hook-length formula: {path}")
            self.offsets_start = HEADER_SIZE + 4 * shape_len
            self.targets_start = self.offsets_start + 8 * (self.vertices + 1)
            self.weights_start = self.targets_start + 4 * self.edges
            self.weight_size = 1 if self.version == 2 else 4
            expected_size = self.weights_start + self.weight_size * self.edges
            if expected_size != len(self._data):
                raise ValueError(f"CSR file size mismatch: {path}")
            if self.offset(0) != 0 or self.offset(self.vertices) != self.edges:
                raise ValueError(f"invalid first/last CSR offset: {path}")
        except Exception:
            self.close()
            raise

    def close(self) -> None:
        if self._data is not None:
            self._data.close()
        self._file.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def offset(self, vertex: int) -> int:
        return struct.unpack_from("<Q", self._data, self.offsets_start + 8 * vertex)[0]

    def row(self, vertex: int) -> list[tuple[int, int]]:
        start, end = self.offset(vertex), self.offset(vertex + 1)
        if not (0 <= start <= end <= self.edges):
            raise ValueError(f"invalid CSR offsets at vertex {vertex}: {self.path}")
        result = []
        for position in range(start, end):
            target = struct.unpack_from(
                "<I", self._data, self.targets_start + 4 * position
            )[0]
            weight = (
                self._data[self.weights_start + position]
                if self.version == 2
                else struct.unpack_from("<i", self._data, self.weights_start + 4 * position)[0]
            )
            if not (vertex < target < self.vertices) or weight <= 0:
                raise ValueError(f"invalid upper-CSR edge at {position}: {self.path}")
            result.append((target, weight))
        result.sort()
        if any(a[0] == b[0] for a, b in zip(result, result[1:])):
            raise ValueError(f"duplicate target at vertex {vertex}: {self.path}")
        return result

    def summary(self) -> dict:
        # Hash the canonical graph independently of file version and row order.
        digest = hashlib.sha256()
        digest.update(struct.pack("<IIIQ", self.n, len(self.shape), self.vertices, self.edges))
        digest.update(struct.pack(f"<{len(self.shape)}I", *self.shape))
        weights: Counter[int] = Counter()
        for vertex in range(self.vertices):
            row = self.row(vertex)
            digest.update(struct.pack("<I", len(row)))
            for target, weight in row:
                digest.update(struct.pack("<Ii", target, weight))
                weights[weight] += 1
        return {
            "n": self.n,
            "shape": list(self.shape),
            "vertices": self.vertices,
            "edges": self.edges,
            "special_edges": sum(count for weight, count in weights.items() if weight != 1),
            "weight_counts": {str(weight): count for weight, count in sorted(weights.items())},
            "canonical_sha256": digest.hexdigest(),
        }


def compare_graphs(first_path: Path, second_path: Path) -> dict:
    with Graph(first_path) as first, Graph(second_path) as second:
        if (first.n, first.shape, first.vertices, first.edges) != (
            second.n, second.shape, second.vertices, second.edges
        ):
            raise AssertionError(f"graph header mismatch: {first_path} / {second_path}")
        for vertex in range(first.vertices):
            first_row, second_row = first.row(vertex), second.row(vertex)
            if first_row != second_row:
                raise AssertionError(
                    f"graph edge mismatch at vertex {vertex}: "
                    f"{first_row[:12]} != {second_row[:12]}"
                )
        return first.summary()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", type=Path)
    parser.add_argument("--compare", type=Path, help="compare every weighted edge with a second graph")
    args = parser.parse_args()
    if args.compare:
        result = compare_graphs(args.graph, args.compare)
        result["graphs_match"] = True
    else:
        with Graph(args.graph) as graph:
            result = graph.summary()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
