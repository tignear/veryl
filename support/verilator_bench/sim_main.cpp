#include "Vverilator_bench_Top.h"
#include "verilated.h"
#include <benchmark/benchmark.h>
#include <memory>

static void BM_VerilatorSimulation(benchmark::State& state) {
    auto top = std::make_unique<Vverilator_bench_Top>();

    // Initialize (Active Low Reset)
    top->rst = 0;
    top->clk = 0;
    top->eval();
    top->rst = 1;
    top->eval();

    for (auto _ : state) {
        top->clk = 1;
        top->eval();
        top->clk = 0;
        top->eval();
    }
}

static void BM_VerilatorSimulation_1M(benchmark::State& state) {
    auto top = std::make_unique<Vverilator_bench_Top>();

    // Initialize (Active Low Reset)
    top->rst = 0;
    top->clk = 0;
    top->eval();
    top->rst = 1;
    top->eval();

    for (auto _ : state) {
        for (int i = 0; i < 1000000; ++i) {
            top->clk = 1;
            top->eval();
            top->clk = 0;
            top->eval();
        }
    }
}

BENCHMARK(BM_VerilatorSimulation);
BENCHMARK(BM_VerilatorSimulation_1M);

BENCHMARK_MAIN();
