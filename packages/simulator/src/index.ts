/**
 * @veryl-lang/simulator
 *
 * TypeScript runtime for Veryl HDL simulation.
 * Provides zero-FFI signal I/O via SharedArrayBuffer + DataView,
 * with NAPI calls only for control operations (tick, runUntil, etc.).
 */

// Core types
export type {
  ModuleDefinition,
  PortInfo,
  SignalLayout,
  SimulatorOptions,
  EventHandle,
  CreateResult,
  NativeHandle,
  NativeSimulatorHandle,
  NativeSimulationHandle,
  FourStateValue,
} from "./types.js";

// 4-state helpers
export { X, Z, FourState, isFourStateValue } from "./types.js";

// Simulator (event-based)
export { Simulator } from "./simulator.js";

// Simulation (time-based)
export { Simulation } from "./simulation.js";

// DUT accessor (advanced / internal use)
export { createDut, readFourState } from "./dut.js";
export type { DirtyState } from "./dut.js";
