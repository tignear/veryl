use crate::{
    EventRef, IOContext, RuntimeErrorCode,
    backend::JitBackend,
    ir::{Program, SignalRef},
};
use malachite_bigint::BigUint;

mod builder;
mod error;

pub use builder::{SimulatorBuilder, SimulatorOptions};
pub use error::SimulatorError;

/// The core logic evaluation engine.
///
/// Encapsulates the JIT-compiled backend, the original SIR program,
/// and an optional VCD writer. Provides low-level, event-driven control.
pub struct Simulator {
    pub(crate) backend: JitBackend,
    pub(crate) program: Program,
    pub(crate) vcd_writer: Option<crate::vcd::VcdWriter>,
    pub(crate) dirty: bool,
}

impl std::fmt::Debug for Simulator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Simulator").finish()
    }
}

impl Simulator {
    pub fn builder<'a>(code: &'a str, top: &'a str) -> SimulatorBuilder<'a, Simulator> {
        SimulatorBuilder::<Simulator>::new(code, top)
    }

    pub(crate) fn with_backend_and_program(backend: JitBackend, program: Program) -> Self {
        Self {
            backend,
            program,
            vcd_writer: None,
            dirty: false,
        }
    }

    /// Captures the current state of all signals and writes them to the VCD file.
    pub fn dump(&mut self, timestamp: u64) {
        if self.dirty {
            self.backend.eval_comb().unwrap();
            self.dirty = false;
        }
        if let Some(ref mut writer) = self.vcd_writer {
            let backend = &self.backend;
            writer
                .dump(timestamp, |addr| {
                    let signal = backend.resolve_signal(addr);
                    backend.get(signal)
                })
                .unwrap();
        }
    }

    /// Modifies internal state via a callback and marks combinational logic as dirty.
    pub fn modify<F>(&mut self, f: F) -> Result<(), RuntimeErrorCode>
    where
        F: FnOnce(&mut IOContext),
    {
        let mut ctx = IOContext {
            backend: &mut self.backend,
        };
        f(&mut ctx);
        self.dirty = true;
        Ok(())
    }

    /// Manually triggers a clock or event to process sequential logic.
    pub fn tick(&mut self, event: EventRef) -> Result<(), RuntimeErrorCode> {
        if self.dirty {
            self.backend.eval_comb()?;
        }
        self.backend.eval_ff_at(event)?;
        self.backend.eval_comb()?;
        self.dirty = false;
        Ok(())
    }

    /// Resolves a signal path into a performance-optimized [`SignalRef`].
    /// This handle allows for direct memory access without `HashMap` lookups.
    pub fn signal(&self, path: &str) -> SignalRef {
        let addr = self.program.get_addr(&[], &[path]);
        self.backend.resolve_signal(&addr)
    }

    /// Resolve a port name to an [`EventRef`] handle.
    pub fn event(&self, port: &str) -> EventRef {
        let addr = self.program.get_addr(&[], &[port]);
        self.backend.resolve_event(&addr)
    }

    /// Retrieves the current value of a variable using a pre-resolved [`SignalRef`] handle.
    /// Lazily evaluates combinational logic if the state is dirty.
    pub fn get(&mut self, signal: SignalRef) -> BigUint {
        if self.dirty {
            self.backend.eval_comb().unwrap();
            self.dirty = false;
        }
        self.backend.get(signal)
    }

    /// Retrieves the current 4-state value (value, mask) of a variable using a [`SignalRef`] handle.
    /// Lazily evaluates combinational logic if the state is dirty.
    pub fn get_four_state(&mut self, signal: SignalRef) -> (BigUint, BigUint) {
        if self.dirty {
            self.backend.eval_comb().unwrap();
            self.dirty = false;
        }
        self.backend.get_four_state(signal)
    }

    /// Directly execute combinational logic evaluation.
    pub fn eval_comb(&mut self) -> Result<(), RuntimeErrorCode> {
        self.backend.eval_comb()?;
        self.dirty = false;
        Ok(())
    }
}
