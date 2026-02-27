# Verilator Benchmark

This directory contains a performance comparison environment for `veryl-simulator` and `Verilator`.
It uses Docker to provide a fair comparison with the same compiler optimizations (O3).

## Prerequisites

- Docker

## How to Run

To build and run the benchmarks (Verilator with Google Benchmark vs veryl-simulator with Criterion), execute the following commands from the **workspace root**:

```bash
# Build the benchmark container
docker build -t veryl-bench -f support/verilator_bench/Dockerfile .

# Run the benchmarks
docker run --rm veryl-bench
```

## Context

- **Verilator**: Built with `--cc`, `-O3`, and linked against Google Benchmark.
- **veryl-simulator**: Built with `--profile fast-bench` (opt-level 3, no LTO) and executed via Criterion.
- **Target**: A nested loop structure with reset logic (defined in `support/verilator_bench/src/Top.veryl`).

## Reference Performance

The following results were measured in the provided Docker environment.

### Environment

- **Date**: 2026-02-18
- **CPU**: 16 X 4699.88 MHz (AMD Ryzen 7 9800X3D)
- **Cache**: L1 48K/32K, L2 1024K, L3 96M
- **OS**: Ubuntu 22.04 (Docker on Windows)

### Results

| Simulator | Framework | Result (1 Step) | Result (1M Cycles) |
|-----------|-----------|-----------------|-------------------|
| Verilator (-O3) | Google Benchmark | **332.22 ns** | **331.15 ms** |
| veryl-simulator (Fast Bench) | Criterion | **101.16 ns** | **100.41 ms** |

> [!NOTE]
> `veryl-simulator` is now about 3.28x faster than Verilator for single steps and about 3.30x faster for 1M cycles.
