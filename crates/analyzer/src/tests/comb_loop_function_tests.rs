use super::*;

fn ordered_function_actual_code(actual: &str) -> String {
    format!(
        r#"
        module Identity (i: input logic, o: output logic) {{
            assign o = i;
        }}
        module Top (independent: input logic, o: output logic) {{
            var x       : logic;
            var feedback: logic;
            function set_x (value: input logic) -> logic {{
                x = value;
                return 0;
            }}
            function middle (value: input logic<3>) -> logic {{
                return value[1];
            }}
            inst identity: Identity (
                i: middle({actual}),
                o: feedback,
            );
            assign o = feedback;
        }}
        "#
    )
}

#[test]
fn function_actual_projection_reads_the_version_at_each_syntax_occurrence() {
    assert_comb_loop(
        "a middle actual read sees the write that precedes that occurrence",
        &ordered_function_actual_code("{set_x(feedback), x, set_x(independent)}"),
        true,
    );
}

#[test]
fn following_function_actual_effect_does_not_retroactively_taint_a_read() {
    assert_comb_loop(
        "a write after a middle actual read cannot alter the captured value",
        &ordered_function_actual_code("{set_x(independent), x, set_x(feedback)}"),
        false,
    );
}

#[test]
fn sequential_early_return_paths_remain_persistent() {
    const STATEMENTS: usize = 512;
    let statements = (0..STATEMENTS)
        .map(|index| format!("if conditions[{index}] {{ return 0; }}\n"))
        .collect::<String>();
    let code = format!(
        r#"
        module Top (conditions: input logic<{STATEMENTS}>, o: output logic) {{
            function update () -> logic {{
                {statements}
                return 0;
            }}
            assign o = update();
        }}
        "#
    );
    crate::comb_loop_detect::reset_flow_scaling_counters();
    let errors = analyze(&code);
    assert!(errors.is_empty(), "{errors:#?}");
    let (materialized_constraints, snapshot_keys, revision_events, revision_inputs) =
        crate::comb_loop_detect::flow_scaling_counters();
    assert_eq!(materialized_constraints, 0);
    assert_eq!(snapshot_keys, 0);
    assert!(revision_events <= 4 * STATEMENTS + 4, "{revision_events}");
    assert!(revision_inputs <= STATEMENTS + 2, "{revision_inputs}");
}

#[test]
fn cumulative_unique_writes_and_early_returns_are_aggregated_linearly() {
    const STATEMENTS: usize = 512;
    let declarations = (0..STATEMENTS)
        .map(|index| format!("var value_{index}: logic;\n"))
        .collect::<String>();
    let statements = (0..STATEMENTS)
        .map(|index| format!("value_{index} = 0;\nif conditions[{index}] {{ return 0; }}\n"))
        .collect::<String>();
    let code = format!(
        r#"
        module Top (conditions: input logic<{STATEMENTS}>, o: output logic) {{
            function update () -> logic {{
                {declarations}
                {statements}
                return 0;
            }}
            assign o = update();
        }}
        "#
    );
    crate::comb_loop_detect::reset_flow_scaling_counters();
    crate::comb_loop_detect::reset_source_summary_state_visits();
    let errors = analyze(&code);
    assert!(errors.is_empty(), "{errors:#?}");
    let (materialized_constraints, snapshot_keys, revision_events, revision_inputs) =
        crate::comb_loop_detect::flow_scaling_counters();
    assert_eq!(materialized_constraints, 0);
    assert_eq!(snapshot_keys, 0);
    assert!(revision_events <= 6 * STATEMENTS + 4, "{revision_events}");
    assert!(revision_inputs <= 4 * STATEMENTS + 2, "{revision_inputs}");
    assert!(
        crate::comb_loop_detect::source_summary_state_visits() <= 4 * STATEMENTS,
        "function-local state must not expand the externally visible summary"
    );
}

#[test]
fn repeated_summary_application_reuses_graph_metadata() {
    const WIDTH: usize = 128;
    let declarations = (0..WIDTH)
        .map(|index| format!("var value_{index}: logic;"))
        .collect::<Vec<_>>()
        .join("\n");
    let chain = (0..WIDTH)
        .map(|index| {
            let source = if index == 0 {
                "input_value".to_owned()
            } else {
                format!("value_{}", index - 1)
            };
            format!("value_{index} = {source};")
        })
        .collect::<Vec<_>>()
        .join("\n");
    let calls = (0..WIDTH)
        .map(|_| "result = propagate(seed);")
        .collect::<Vec<_>>()
        .join("\n");
    let code = format!(
        r#"
        module Top (seed: input logic, o: output logic) {{
            var result: logic;
            function propagate (input_value: input logic) -> logic {{
                {declarations}
                {chain}
                return value_{};
            }}
            always_comb {{
                result = 0;
                {calls}
                o = result;
            }}
        }}
        "#,
        WIDTH - 1,
    );

    crate::comb_loop_detect::reset_function_evaluation_count();
    let errors = analyze(&code);
    assert!(
        errors.is_empty(),
        "repeated propagation is acyclic: {errors:#?}"
    );
    let visits = crate::comb_loop_detect::function_summary_metadata_visits();
    assert!(
        visits <= WIDTH * 4,
        "summary applications must use cached external-key/branch metadata: {visits}"
    );
}

#[test]
fn comb_loop_false_negative_early_return_controls_a_later_captured_write() {
    // update(stop) leaves value at zero on the return path and writes one on
    // the continuation path. Since stop = value, the captured write is in a
    // real control-dependency loop even though the function result is constant.
    let errors = analyze(
        r#"
        module Top (
            o: output logic,
        ) {
            var stop : logic;
            var value: logic;
            var dummy: logic;
            function update (condition: input logic) -> logic {
                value = 0;
                if condition {
                    return 0;
                }
                value = 1;
                return 0;
            }
            assign stop = value;
            always_comb {
                dummy = update(stop);
                o = value | dummy;
            }
        }
        "#,
    );
    assert!(
        errors
            .iter()
            .any(|error| matches!(error, AnalyzerError::CombinationalLoop { .. })),
        "an early return condition controls the captured final value: {errors:#?}"
    );
}

#[test]
fn comb_loop_condition_with_two_continuing_function_arms_does_not_control_later_write() {
    assert_comb_loop(
        "a condition does not control continuation when both function arms continue",
        r#"
        module Top (
            o: output logic,
        ) {
            var condition: logic;
            var value    : logic;
            var dummy    : logic;
            function update (select: input logic) -> logic {
                value = 0;
                if select {
                    dummy = 0;
                } else {
                    dummy = 1;
                }
                value = 1;
                return dummy;
            }
            assign condition = value;
            always_comb {
                o = update(condition);
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_nested_early_return_controls_a_later_captured_write() {
    assert_comb_loop(
        "an outer condition controls whether a nested early return reaches a later write",
        r#"
        module Top (
            b: input  logic,
            o: output logic,
        ) {
            var a    : logic;
            var value: logic;
            var dummy: logic;
            function update (ca: input logic, cb: input logic) -> logic {
                value = 0;
                if ca {
                    if cb {
                        return 0;
                    }
                }
                value = 1;
                return 0;
            }
            assign a = value;
            always_comb {
                dummy = update(a, b);
                o = value | dummy;
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_nested_complementary_returns_preserve_outer_control() {
    assert_comb_loop(
        "complementary nested exits must not make the outer condition disappear",
        r#"
        module Top (
            b: input  logic,
            o: output logic,
        ) {
            var a    : logic;
            var value: logic;
            var dummy: logic;
            function update (ca: input logic, cb: input logic) -> logic {
                value = 0;
                if ca {
                    if cb {
                        return 0;
                    }
                } else {
                    if !cb {
                        return 0;
                    }
                }
                value = 1;
                return 0;
            }
            assign a = value;
            always_comb {
                dummy = update(a, b);
                o = value | dummy;
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_identical_nested_returns_do_not_create_outer_control() {
    assert_comb_loop(
        "identical nested exits in both arms do not depend on the outer condition",
        r#"
        module Top (
            b: input  logic,
            o: output logic,
        ) {
            var a    : logic;
            var value: logic;
            var dummy: logic;
            function update (ca: input logic, cb: input logic) -> logic {
                value = 0;
                if ca {
                    if cb {
                        return 0;
                    }
                } else {
                    if cb {
                        return 0;
                    }
                }
                value = 1;
                return 0;
            }
            assign a = value;
            always_comb {
                dummy = update(a, b);
                o = value | dummy;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_runtime_for_return_controls_a_later_captured_write() {
    assert_comb_loop(
        "a runtime loop bound controls whether an early return reaches a later write",
        r#"
        module Top (o: output logic) {
            var n    : u32;
            var value: logic;
            var dummy: logic;
            function update () -> logic {
                value = 0;
                for _index in 0..n {
                    return 0;
                }
                value = 1;
                return 0;
            }
            assign n = value as u32;
            always_comb {
                dummy = update();
                o = value | dummy;
            }
        }
        "#,
        true,
    );
}

#[test]
fn runtime_bound_return_sees_prior_continuing_iterations() {
    assert_comb_loop(
        "a runtime-loop return is reached after the preceding iteration transfer",
        r#"
        module Top (n: input u32, o: output logic) {
            var feedback: logic;
            function delayed (seed: input logic) -> logic {
                var state: logic<2>;
                state = 0;
                state[0] = seed;
                for index in 0..n {
                    if index == 1 {
                        return state[1];
                    }
                    state = state << 1;
                }
                return 0;
            }
            assign o = delayed(feedback);
            assign feedback = o;
        }
        "#,
        true,
    );
}

#[test]
fn static_return_sees_prior_continuing_iterations() {
    assert_comb_loop(
        "the statically expanded form detects the same delayed feedback",
        r#"
        module Top (o: output logic) {
            var feedback: logic;
            function delayed (seed: input logic) -> logic {
                var state: logic<2>;
                state = 0;
                state[0] = seed;
                for index in 0..2 {
                    if index == 1 {
                        return state[1];
                    }
                    state = state << 1;
                }
                return 0;
            }
            assign o = delayed(feedback);
            assign feedback = o;
        }
        "#,
        true,
    );
}

#[test]
fn runtime_bound_immediate_return_does_not_invent_a_disjoint_bit_dependency() {
    assert_comb_loop(
        "a runtime-loop return keeps a disjoint state bit loop-free",
        r#"
        module Top (n: input u32, o: output logic) {
            var feedback: logic;
            function delayed (seed: input logic) -> logic {
                var state: logic<2>;
                state = 0;
                state[0] = seed;
                for _index in 0..n {
                    state = state << 1;
                    return state[0];
                }
                return 0;
            }
            assign o = delayed(feedback);
            assign feedback = o;
        }
        "#,
        false,
    );
}

#[test]
fn runtime_bound_return_lifts_a_captured_write_over_prior_iterations() {
    assert_comb_loop(
        "a captured write on return sees state from an earlier iteration",
        r#"
        module Top (n: input u32, o: output logic) {
            var feedback: logic;
            var captured: logic;
            var dummy   : logic;
            function delayed (seed: input logic) -> logic {
                var state: logic<2>;
                state = 0;
                state[0] = seed;
                for index in 0..n {
                    if index == 1 {
                        captured = state[1];
                        return 0;
                    }
                    state = state << 1;
                }
                return 0;
            }
            always_comb {
                captured = 0;
                dummy = delayed(feedback);
            }
            always_comb {
                feedback = captured;
            }
            assign o = feedback | dummy;
        }
        "#,
        true,
    );
}

#[test]
fn runtime_bound_mutually_exclusive_return_writes_are_not_composed() {
    assert_comb_loop(
        "writes from mutually exclusive return arms remain incompatible",
        r#"
        module Top (
            n     : input  u32,
            select: input  logic,
            o     : output logic,
        ) {
            var feedback: logic;
            var a       : logic;
            var b       : logic;
            var c       : logic;
            var dummy   : logic;
            function choose () -> logic {
                for _index in 0..n {
                    if select {
                        b = a;
                        return 0;
                    } else {
                        c = b;
                        return 0;
                    }
                }
                return 0;
            }
            always_comb {
                a = feedback;
                b = 0;
                c = 0;
                dummy = choose();
            }
            always_comb {
                feedback = c;
            }
            assign o = feedback | dummy;
        }
        "#,
        false,
    );
}

#[test]
fn nested_runtime_bound_return_sees_prior_inner_iterations() {
    assert_comb_loop(
        "a nested runtime-loop return retains the inner continuing transfer",
        r#"
        module Top (
            outer_bound: input u32,
            inner_bound: input u32,
            o          : output logic,
        ) {
            var feedback: logic;
            function delayed (seed: input logic) -> logic {
                var state: logic<2>;
                state = 0;
                state[0] = seed;
                for _outer in 0..outer_bound {
                    for inner in 0..inner_bound {
                        if inner == 1 {
                            return state[1];
                        }
                        state = state << 1;
                    }
                }
                return 0;
            }
            assign o = delayed(feedback);
            assign feedback = o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_break_and_fallthrough_do_not_control_after_loop_write() {
    assert_comb_loop(
        "break and body fallthrough reach the same statement after the loop",
        r#"
        module Top (o: output logic) {
            var select: logic;
            var value : logic;
            var dummy : logic;
            function update (condition: input logic) -> logic {
                for _index in 0..1 {
                    if condition {
                        break;
                    }
                }
                value = 1;
                return 0;
            }
            assign select = value;
            always_comb {
                dummy = update(select);
                o = value | dummy;
            }
        }
        "#,
        false,
    );
}

fn assert_comb_loop(case: &str, code: &str, expected: bool) {
    let errors = analyze(code);
    let actual = errors
        .iter()
        .any(|error| matches!(error, AnalyzerError::CombinationalLoop { .. }));
    assert_eq!(actual, expected, "{case}: {errors:?}");
}

fn assert_incomplete_assignment_without_comb_loop(case: &str, code: &str) {
    let errors = analyze(code);
    assert!(
        errors
            .iter()
            .any(|error| matches!(error, AnalyzerError::UncoveredBranch { .. })),
        "{case}: retained entry state must be diagnosed as an incomplete assignment: {errors:#?}"
    );
    assert!(
        errors
            .iter()
            .all(|error| !matches!(error, AnalyzerError::CombinationalLoop { .. })),
        "{case}: state retention is not combinational feedback: {errors:#?}"
    );
}

macro_rules! comb_loop_case {
    ($name:ident, $case:literal, $code:expr, $expected:expr) => {
        #[test]
        fn $name() {
            let code = $code;
            assert_comb_loop($case, code.as_ref(), $expected);
        }
    };
}

fn unaligned_instance_function_actual_code(actual: &str) -> String {
    format!(
        r#"
        module Child (i: input logic, o: output logic) {{ assign o = i; }}
        module Top (o: output logic) {{
            var feedback: logic;
            var passed: logic;
            function only_a (a: input logic, b: input logic) -> logic {{ return !a; }}
            inst u: Child (i: {actual}, o: passed);
            assign feedback = passed;
            assign o = passed;
        }}
        "#
    )
}

comb_loop_case!(
    comb_loop_instance_actual_function_retains_module_capture,
    "an instance actual function retains a module-scope capture",
    r#"
    module Child (i: input logic, o: output logic) { assign o = i; }
    module Top (o: output logic) {
        var x: logic;
        var passed: logic;
        function get_x () -> logic { return x; }
        inst u: Child (i: get_x(), o: passed);
        assign x = passed;
        assign o = passed;
    }
    "#,
    true
);

comb_loop_case!(
    comb_loop_instance_actual_function_keeps_disjoint_capture,
    "an instance actual function keeps a disjoint captured bit loop-free",
    r#"
    module Child (i: input logic, o: output logic) { assign o = i; }
    module Top (o: output logic) {
        var x: logic<2>;
        var passed: logic;
        function get_high () -> logic { return x[1]; }
        inst u: Child (i: get_high(), o: passed);
        assign x[0] = passed;
        assign x[1] = 0;
        assign o = passed;
    }
    "#,
    false
);

comb_loop_case!(
    comb_loop_unaligned_function_return_ignores_unused_actual,
    "an unaligned function return ignores an unused actual",
    unaligned_instance_function_actual_code("only_a(0, feedback)"),
    false
);

comb_loop_case!(
    comb_loop_unaligned_function_return_retains_used_actual,
    "an unaligned function return retains its used actual",
    unaligned_instance_function_actual_code("only_a(feedback, 0)"),
    true
);

#[test]
fn comb_loop_core_semantics_and_region_regressions_function_call_caller_side_feedthrough_links_read_x_write_x()
 {
    // Function call: caller-side feedthrough links read x -> write x.
    let code = r#"
    module ModuleA (
        a: input  logic<8>,
        b: output logic<8>,
    ) {
        function ident (
            x: input logic<8>,
        ) -> logic<8> {
            return x;
        }

        var c: logic<8>;
        assign b = ident(c);
        assign c = b;
    }
    "#;
    let errors = analyze(code);
    assert!(matches!(errors[0], AnalyzerError::CombinationalLoop { .. }));
}

#[test]
fn comb_loop_statement_order_and_observer_semantics_function_summaries_come_from_the_specialized_body_merely_evaluating_an()
 {
    // Function summaries come from the specialized body. Merely evaluating an
    // unused actual argument is not a signal-value dependency of the return.
    let code = r#"
    module Top (
        o: output logic,
    ) {
        function ignore (
            unused: input logic,
        ) -> logic {
            return 0;
        }
        var feedback: logic;
        assign o = ignore(feedback);
        assign feedback = o;
    }
    "#;
    let errors = analyze(code);
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, AnalyzerError::CombinationalLoop { .. })),
        "unused function argument formed a false loop: {errors:?}"
    );
}

#[test]
fn comb_loop_function_global_read_contributes_value_dependency_a_called_function_retains_a_captured_module_scope_read()
 {
    assert_comb_loop(
        "a called function retains a captured module-scope read",
        r#"
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function get_x () -> logic {
                return x;
            }
            always_comb {
                o = get_x();
            }
            always_comb {
                x = o;
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_global_read_contributes_value_dependency_a_captured_function_read_remains_feed_forward_without_a_return_path()
 {
    assert_comb_loop(
        "a captured function read remains feed-forward without a return path",
        r#"
        module Top (
            i: input  logic,
            o: output logic,
        ) {
            var x: logic;
            function get_x () -> logic {
                return x;
            }
            always_comb {
                o = get_x();
            }
            always_comb {
                x = i;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_function_global_write_contributes_procedural_effect_a_called_function_retains_a_captured_module_scope_write()
 {
    assert_comb_loop(
        "a called function retains a captured module-scope write",
        r#"
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function set_x (
                a: input logic,
            ) {
                x = a;
            }
            always_comb {
                set_x(o);
            }
            always_comb {
                o = x;
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_global_write_contributes_procedural_effect_a_captured_function_write_remains_feed_forward_without_a_return_path()
 {
    assert_comb_loop(
        "a captured function write remains feed-forward without a return path",
        r#"
        module Top (
            i: input  logic,
            o: output logic,
        ) {
            var x: logic;
            function set_x (
                a: input logic,
            ) {
                x = a;
            }
            always_comb {
                set_x(i);
            }
            always_comb {
                o = x;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_vector_function_return_bits_a_vector_function_return_preserves_bit_identity()
{
    assert_comb_loop(
        "a vector function return preserves bit identity",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            function identity (
                x: input logic<2>,
            ) -> logic<2> {
                return x;
            }
            var value: logic<2>;
            assign o = identity(value);
            assign value[0] = 0;
            assign value[1] = o[0];
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_vector_function_return_bits_a_vector_function_return_retains_same_bit_feedback()
 {
    assert_comb_loop(
        "a vector function return retains same-bit feedback",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            function identity (
                x: input logic<2>,
            ) -> logic<2> {
                return x;
            }
            var value: logic<2>;
            assign o = identity(value);
            assign value[0] = o[0];
            assign value[1] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_write_without_value_dependency_is_recorded() {
    // Why this case exists: clear_x writes x even though the written value has
    // no signal dependency. That write kills LiveOnEntry before o reads x;
    // omitting it invents x -> o -> x feedback.
    assert_comb_loop(
        "a constant captured function write participates in procedural order",
        r#"
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function clear_x () {
                x = 0;
            }
            always_comb {
                clear_x();
                o = x;
                x = o;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_observer_function_side_effect_is_recorded() {
    // Why this case exists: IEEE 1800-2023 11.3.5 preserves side effects of
    // evaluated expressions. touch(o) is evaluated as a display argument, and
    // 9.2.2.2 makes its captured x write part of the always_comb procedure.
    assert_comb_loop(
        "a display argument retains a called function global write",
        r#"
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return 0;
            }
            always_comb {
                $display("touch=%d", touch(o));
            }
            always_comb {
                o = x;
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_instance_actual_function_side_effect_is_recorded() {
    // Why this case exists: IEEE 1800-2023 4.9.6 models an input connection as
    // an implicit continuous assignment. Its actual expression is evaluated
    // even when the child has no output feedthrough, so touch(o) still writes x.
    assert_comb_loop(
        "an instance input actual retains a called function global write",
        r#"
        module Sink (
            i: input logic,
        ) {}
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return 0;
            }
            inst u: Sink (
                i: touch(o),
            );
            assign o = x;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_instance_actual_evaluates_an_unused_function_argument_once() {
    assert_comb_loop(
        "an unused outer argument retains its evaluated function side effect",
        r#"
        module Sink (
            i: input logic,
        ) {}
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return 0;
            }
            function ignore (
                unused: input logic,
            ) -> logic {
                return 0;
            }
            inst u: Sink (
                i: ignore(touch(o)),
            );
            assign o = x;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_vector_function_output_bits() {
    // Why this case exists: output argument y is a vector identity of x.
    // Broadcasting all x bits to all y bits invents value[1] -> o[0] feedback.
    assert_comb_loop(
        "a vector function output argument preserves bit identity",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            function copy (
                x: input  logic<2>,
                y: output logic<2>,
            ) {
                y = x;
            }
            var value: logic<2>;
            always_comb {
                copy(value, o);
            }
            assign value[0] = 0;
            assign value[1] = o[0];
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_function_output_state_does_not_leak_between_calls() {
    assert_comb_loop(
        "a conditionally assigned function output starts with fresh state on each call",
        r#"
        module Top (
            p: output logic,
            q: output logic,
        ) {
            function f (
                x: input  logic,
                y: output logic,
            ) {
                if x {
                    y = 1;
                }
            }
            var a: logic;
            var b: logic;
            always_comb {
                f(a, p);
                f(b, q);
            }
            assign a = q;
            assign b = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_function_output_retains_same_call_control_feedback() {
    assert_comb_loop(
        "a function output retains control feedback within the same call",
        r#"
        module Top (
            p: output logic,
            q: output logic,
        ) {
            function f (
                x: input  logic,
                y: output logic,
            ) {
                if x {
                    y = 1;
                }
            }
            var a: logic;
            var b: logic;
            always_comb {
                f(a, p);
                f(b, q);
            }
            assign a = 0;
            assign b = q;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_local_state_does_not_leak_between_calls() {
    assert_comb_loop(
        "a function local starts with fresh state on each call",
        r#"
        module Top (
            p: output logic,
            q: output logic,
        ) {
            function f (
                x: input  logic,
                y: output logic,
            ) {
                var temporary: logic;
                if x {
                    temporary = 1;
                }
                y = temporary;
            }
            var a: logic;
            var b: logic;
            always_comb {
                f(a, p);
                f(b, q);
            }
            assign a = q;
            assign b = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_function_return_state_does_not_leak_between_calls() {
    assert_comb_loop(
        "a function return starts with fresh state on each call",
        r#"
        module Top (
            p: output logic,
            q: output logic,
        ) {
            function f (
                x: input logic,
            ) -> logic {
                if x {
                    return 1;
                }
            }
            var a: logic;
            var b: logic;
            assign p = f(a);
            assign q = f(b);
            assign a = q;
            assign b = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_wide_function_output_bits_without_scalarization() {
    // Why this case exists: function boundary precision must come from
    // observed endpoint propagation, not a width-limited per-bit expansion.
    assert_comb_loop(
        "a wide function output keeps disjoint endpoint bits independent",
        r#"
        module Top (
            o: output logic<128>,
        ) {
            function copy (
                x: input  logic<128>,
                y: output logic<128>,
            ) {
                y = x;
            }
            var value: logic<128>;
            always_comb {
                copy(value, o);
            }
            assign value[126:0] = 0;
            assign value[127] = o[0];
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_wide_function_output_retains_matching_endpoint_feedback() {
    assert_comb_loop(
        "a wide function output retains feedback at the matching endpoint",
        r#"
        module Top (
            o: output logic<128>,
        ) {
            function copy (
                x: input  logic<128>,
                y: output logic<128>,
            ) {
                y = x;
            }
            var value: logic<128>;
            always_comb {
                copy(value, o);
            }
            assign value[126:0] = 0;
            assign value[127] = o[127];
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_split_destination_reuses_one_function_evaluation() {
    const WIDTH: usize = 256;
    let observed_bits = (0..WIDTH)
        .map(|bit| format!("assign observed[{bit}] = result[{bit}];"))
        .collect::<Vec<_>>()
        .join("\n");
    crate::comb_loop_detect::reset_function_evaluation_count();
    let errors = analyze(&format!(
        r#"
        module Top (
            i       : input  logic<{WIDTH}>,
            observed: output logic<{WIDTH}>,
        ) {{
            function identity (
                x: input logic<{WIDTH}>,
            ) -> logic<{WIDTH}> {{
                return x;
            }}
            var result: logic<{WIDTH}>;
            assign result = identity(i);
            {observed_bits}
        }}
        "#
    ));
    assert!(
        errors.is_empty(),
        "split observation of one function result is acyclic: {errors:#?}"
    );
    assert_eq!(
        crate::comb_loop_detect::function_evaluation_count(),
        1,
        "splitting the destination must not reevaluate the same function call"
    );
    assert_eq!(
        crate::comb_loop_detect::function_result_version_count(),
        WIDTH,
        "each split destination must request only its matching return region"
    );
    assert!(
        crate::comb_loop_detect::function_result_region_probe_count() <= WIDTH * 12,
        "return-region lookup must be logarithmic rather than scanning all regions per bit"
    );
}

#[test]
fn comb_loop_split_function_output_queries_only_matching_formal_regions() {
    const WIDTH: usize = 128;
    let copies = (0..WIDTH)
        .map(|bit| format!("y[{bit}] = x[{bit}];"))
        .collect::<Vec<_>>()
        .join("\n");
    let observations = (0..WIDTH)
        .map(|bit| format!("assign observed[{bit}] = result[{bit}];"))
        .collect::<Vec<_>>()
        .join("\n");
    crate::comb_loop_detect::reset_function_evaluation_count();
    let errors = analyze(&format!(
        r#"
        module Top (
            i       : input  logic<{WIDTH}>,
            observed: output logic<{WIDTH}>,
        ) {{
            function copy (
                x: input  logic<{WIDTH}>,
                y: output logic<{WIDTH}>,
            ) {{
                {copies}
            }}
            var result: logic<{WIDTH}>;
            always_comb {{
                copy(i, result);
            }}
            {observations}
        }}
        "#
    ));
    assert!(
        errors.is_empty(),
        "split function output is acyclic: {errors:#?}"
    );
    assert!(
        crate::comb_loop_detect::formal_output_region_probe_count() <= WIDTH * 16,
        "formal output lookup must not scan every formal region per destination"
    );
}

#[test]
fn comb_loop_static_loop_reevaluates_nested_function_actuals() {
    crate::comb_loop_detect::reset_function_evaluation_count();
    assert_comb_loop(
        "a nested call is reevaluated when its static-loop actual changes",
        r#"
        module Top (
            o: output logic,
        ) {
            function inner (
                x: input logic,
            ) -> logic {
                return x;
            }
            function outer (
                x: input logic<2>,
            ) -> logic {
                var result: logic;
                result = 0;
                for i in 0..2 {
                    if inner(x[i]) {
                        result = 1;
                    } else {
                        result = 0;
                    }
                }
                return result;
            }
            var feedback: logic;
            assign o = outer({feedback, 1'b0});
            assign feedback = o;
        }
        "#,
        true,
    );
    assert_eq!(
        crate::comb_loop_detect::function_barrier_evaluation_count(),
        2,
        "both static-loop invocations must cross the callee cache barrier"
    );
}

#[test]
fn comb_loop_preserves_split_function_return_bits() {
    // Why this case exists: {high, low}[0] is low. Returning o[0] to high is
    // acyclic when low is constant, even though the return uses two regions.
    assert_comb_loop(
        "a concatenated function return preserves each source bit",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            function combine_bits (
                high: input logic,
                low : input logic,
            ) -> logic<2> {
                return {high, low};
            }
            var high: logic;
            var low: logic;
            assign o = combine_bits(high, low);
            assign high = o[0];
            assign low = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_distinguishes_generic_function_specializations() {
    // Why this case exists: recurse::<2> and recurse::<1> are distinct finite
    // specializations. Elaboration reduces the call to passed = feedback, so
    // treating the second specialization as infinite recursion hides a real SCC.
    let errors = analyze_with_large_stack(
        r#"
        module Top (
            o: output logic,
        ) {
            function recurse::<N: u32> (
                x: input logic,
            ) -> logic {
                gen M: u32 = N - 1;
                if N == 1 {
                    return x;
                } else {
                    return recurse::<M>(x);
                }
            }
            var feedback: logic;
            var passed: logic;
            assign passed = recurse::<2>(feedback);
            assign feedback = passed;
            assign o = feedback;
        }
        "#,
    );
    let actual = errors
        .iter()
        .any(|error| matches!(error, AnalyzerError::CombinationalLoop { .. }));
    assert!(
        actual,
        "finite generic recursion retains the specialized feedthrough: {errors:?}"
    );
}

#[test]
fn function_summary_shift_fanout_stays_structural() {
    const DEPTH: usize = 14;
    const WIDTH: usize = 1 << DEPTH;
    let mut functions =
        format!("function f0 (x: input logic<{WIDTH}>) -> logic<{WIDTH}> {{ return x; }}\n");
    for depth in 1..=DEPTH {
        let previous = depth - 1;
        let shift = 1usize << previous;
        functions.push_str(&format!(
            "function f{depth} (x: input logic<{WIDTH}>) -> logic<{WIDTH}> {{ return f{previous}(x) | (f{previous}(x) << {shift}); }}\n"
        ));
    }
    let code = format!(
        "module Top (i: input logic<{WIDTH}>, o: output logic<{WIDTH}>) {{ {functions} assign o = f{DEPTH}(i); }}"
    );
    crate::comb_loop_detect::reset_function_evaluation_count();
    assert!(
        analyze(&code)
            .iter()
            .all(|error| !matches!(error, AnalyzerError::CombinationalLoop { .. }))
    );
    assert!(crate::comb_loop_detect::function_summary_graph_node_count() < 100);
}

#[test]
fn function_summary_rejects_a_cycle_whose_intermediate_shift_is_out_of_range() {
    assert_comb_loop(
        "opposite offsets do not form a loop when the intermediate value is outside the vector",
        r#"
        module Top (o: output logic) {
            function left (x: input logic<2>) -> logic<2> { return x << 1; }
            function right (x: input logic<2>) -> logic<2> { return x >> 1; }
            var a: logic<2>;
            var b: logic<2>;
            var c: logic<2>;
            assign a = left(b);
            assign c = right(a);
            assign b[1] = c[1];
            assign b[0] = 0;
            assign o = a[0] | b[0] | c[0];
        }
        "#,
        false,
    );
}

#[test]
fn function_summary_retains_a_cycle_with_feasible_intermediate_shifts() {
    assert_comb_loop(
        "opposite offsets retain the low-bit path that stays inside the vector",
        r#"
        module Top (o: output logic) {
            function left (x: input logic<2>) -> logic<2> { return x << 1; }
            function right (x: input logic<2>) -> logic<2> { return x >> 1; }
            var a: logic<2>;
            var b: logic<2>;
            var c: logic<2>;
            assign a = left(b);
            assign c = right(a);
            assign b[0] = c[0];
            assign b[1] = 0;
            assign o = a[0] | b[0] | c[0];
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_short_circuits_instance_actual_side_effects_a_constant_dead_instance_actual_branch_has_no_function_side_effect()
 {
    assert_comb_loop(
        "a constant-dead instance actual branch has no function side effect",
        r#"
        module Sink (
            i: input logic,
        ) {}
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return 0;
            }
            inst u: Sink (
                i: if 1'b1 ? 0 : touch(o),
            );
            assign o = x;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_short_circuits_instance_actual_side_effects_a_constant_taken_instance_actual_branch_retains_its_function_side_effect()
 {
    assert_comb_loop(
        "a constant-taken instance actual branch retains its function side effect",
        r#"
        module Sink (
            i: input logic,
        ) {}
        module Top (
            o: output logic,
        ) {
            var x: logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return 0;
            }
            inst u: Sink (
                i: if 1'b0 ? 0 : touch(o),
            );
            assign o = x;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_ternary_positions_across_boundaries_a_function_ternary_actual_keeps_a_disjoint_bit_loop_free()
 {
    assert_comb_loop(
        "a function ternary actual keeps a disjoint bit loop-free",
        r#"
        module Top (
            sel: input  logic,
            o  : output logic,
        ) {
            function low (
                x: input logic<2>,
            ) -> logic {
                return x[0];
            }
            var value: logic<2>;
            assign o = low(if sel ? value : 0);
            assign value[0] = 0;
            assign value[1] = o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_ternary_positions_across_boundaries_a_function_ternary_actual_detects_its_corresponding_bit_loop()
 {
    assert_comb_loop(
        "a function ternary actual detects its corresponding-bit loop",
        r#"
        module Top (
            sel: input  logic,
            o  : output logic,
        ) {
            function low (
                x: input logic<2>,
            ) -> logic {
                return x[0];
            }
            var value: logic<2>;
            assign o = low(if sel ? value : 0);
            assign value[0] = o;
            assign value[1] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_unpacked_function_actual_positions_an_unpacked_function_actual_keeps_disjoint_elements_loop_free()
 {
    assert_comb_loop(
        "an unpacked function actual keeps disjoint elements loop-free",
        r#"
        module Top (
            o: output logic,
        ) {
            function high (
                x: input logic [2],
            ) -> logic {
                return x[1];
            }
            var value: logic [2];
            assign o = high(value);
            assign value[0] = o;
            assign value[1] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_unpacked_function_actual_positions_an_unpacked_function_actual_detects_same_element_feedback()
 {
    assert_comb_loop(
        "an unpacked function actual detects same-element feedback",
        r#"
        module Top (
            o: output logic,
        ) {
            function high (
                x: input logic [2],
            ) -> logic {
                return x[1];
            }
            var value: logic [2];
            assign o = high(value);
            assign value[0] = 0;
            assign value[1] = o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_function_actual_shift_positions_a_function_actual_left_shift_keeps_its_inserted_bit_loop_free()
 {
    assert_comb_loop(
        "a function actual left shift keeps its inserted bit loop-free",
        r#"
        module Top (
            o: output logic,
        ) {
            function low (
                x: input logic<4>,
            ) -> logic {
                return x[0];
            }
            var value: logic<4>;
            assign o = low(value << 1);
            assign value[0] = 0;
            assign value[1] = o;
            assign value[3:2] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_function_actual_shift_positions_a_function_actual_left_shift_detects_its_live_shifted_bit()
 {
    assert_comb_loop(
        "a function actual left shift detects its live shifted bit",
        r#"
        module Top (
            o: output logic,
        ) {
            function bit_one (
                x: input logic<4>,
            ) -> logic {
                return x[1];
            }
            var value: logic<4>;
            assign o = bit_one(value << 1);
            assign value[0] = o;
            assign value[3:1] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_function_concat_output_positions_a_concatenated_function_output_keeps_a_disjoint_bit_loop_free()
 {
    assert_comb_loop(
        "a concatenated function output keeps a disjoint bit loop-free",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            function copy (
                x: input  logic<2>,
                y: output logic<2>,
            ) {
                y = x;
            }
            var value: logic<2>;
            always_comb {
                copy(value, {o[1], o[0]});
            }
            assign value[0] = 0;
            assign value[1] = o[0];
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_function_concat_output_positions_a_concatenated_function_output_detects_its_corresponding_bit_loop()
 {
    assert_comb_loop(
        "a concatenated function output detects its corresponding-bit loop",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            function copy (
                x: input  logic<2>,
                y: output logic<2>,
            ) {
                y = x;
            }
            var value: logic<2>;
            always_comb {
                copy(value, {o[1], o[0]});
            }
            assign value[0] = o[0];
            assign value[1] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_statement_order_and_control_flow_regressions_function_local_partial_writes_are_ordered()
 {
    assert_comb_loop(
        "function local partial writes are ordered",
        r#"
        module Top (
            d: input  logic<8>,
            q: output logic<8>,
        ) {
            function swap_nibbles (
                x: input logic<8>,
            ) -> logic<8> {
                var tmp: logic<8>;
                tmp[7:4] = x[3:0];
                tmp[3:0] = x[7:4];
                return tmp;
            }
            assign q = swap_nibbles(d);
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_statement_order_and_control_flow_regressions_nested_function_summary_preserves_a_real_cycle()
 {
    assert_comb_loop(
        "nested function summary preserves a real cycle",
        r#"
        module Top (
            o: output logic,
        ) {
            function inner (x: input logic) -> logic {
                return x;
            }
            function outer (x: input logic) -> logic {
                return inner(x);
            }
            assign o = outer(o);
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_blocking_assignment_chain_uses_the_immediately_preceding_definition()
 {
    assert_comb_loop(
        "blocking assignment chain uses the immediately preceding definition",
        r#"
        module Top (
            a: input  logic<8>,
            o: output logic<8>,
        ) {
            var tmp: logic<8>;
            always_comb {
                tmp = a;
                tmp = tmp + 8'd1;
                tmp = tmp << 1;
                o = tmp;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_a_later_full_overwrite_kills_an_earlier_partial_entry_read()
 {
    assert_comb_loop(
        "a later full overwrite kills an earlier partial entry read",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            always_comb {
                o[0] = o[1];
                o = 0;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_a_full_overwrite_dominates_a_later_partial_read()
 {
    assert_comb_loop(
        "a full overwrite dominates a later partial read",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            always_comb {
                o = 0;
                o[0] = o[1];
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_both_branch_arms_define_the_value_consumed_after_the_merge()
 {
    assert_comb_loop(
        "both branch arms define the value consumed after the merge",
        r#"
        module Top (
            sel: input  logic,
            a  : input  logic,
            b  : input  logic,
            o  : output logic,
        ) {
            var selected: logic;
            always_comb {
                if sel {
                    selected = a;
                } else {
                    selected = b;
                }
                o = selected;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_function_local_copy_retains_bit_precision_at_the_return()
 {
    assert_comb_loop(
        "function local copy retains bit precision at the return",
        r#"
        module Top (
            o: output logic,
        ) {
            function low (x: input logic<8>) -> logic {
                var tmp: logic<8>;
                tmp = x;
                return tmp[0];
            }
            var value: logic<8>;
            assign o = low(value);
            assign value[7] = o;
            assign value[6:0] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_function_branch_condition_is_a_control_dependency_of_its_return()
 {
    assert_comb_loop(
        "function branch condition is a control dependency of its return",
        r#"
        module Top (
            o: output logic,
        ) {
            function gated (x: input logic<8>) -> logic {
                if x[7] {
                    return x[0];
                } else {
                    return 0;
                }
            }
            var value: logic<8>;
            assign o = gated(value);
            assign value[7] = o;
            assign value[6:0] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_function_branch_ignores_a_bit_absent_from_value_and_control_flow()
 {
    assert_comb_loop(
        "function branch ignores a bit absent from value and control flow",
        r#"
        module Top (
            o: output logic,
        ) {
            function gated (x: input logic<8>) -> logic {
                if x[7] {
                    return x[0];
                } else {
                    return 0;
                }
            }
            var value: logic<8>;
            assign o = gated(value);
            assign value[6] = o;
            assign value[7] = 0;
            assign value[5:0] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_function_output_writeback_participates_in_procedural_order()
 {
    assert_comb_loop(
        "function output writeback participates in procedural order",
        r#"
        module Top (
            o: output logic,
        ) {
            function copy (
                x: input  logic,
                y: output logic,
            ) {
                y = x;
            }
            var tmp: logic;
            always_comb {
                copy(o, tmp);
                o = tmp;
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_static_array_elements_remain_distinct_regions()
{
    assert_comb_loop(
        "static array elements remain distinct regions",
        r#"
        module Top (
            a: input  logic<8>,
            o: output logic<8>,
        ) {
            var mem: logic<8> [2];
            always_comb {
                mem[0] = a;
                mem[1] = mem[0];
                o = mem[1];
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_read_before_write_across_static_array_elements_is_a_real_loop()
 {
    assert_comb_loop(
        "read-before-write across static array elements is a real loop",
        r#"
        module Top (
            o: output logic<8>,
        ) {
            var mem: logic<8> [2];
            always_comb {
                mem[0] = mem[1];
                mem[1] = mem[0];
                o = mem[1];
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_static_struct_members_remain_distinct_regions()
{
    assert_comb_loop(
        "static struct members remain distinct regions",
        r#"
        module Top (
            a: input  logic<8>,
            o: output logic<8>,
        ) {
            struct Pair {
                low : logic<8>,
                high: logic<8>,
            }
            var pair: Pair;
            always_comb {
                pair.low = a;
                pair.high = pair.low;
                o = pair.high;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_sparse_accesses_do_not_scale_with_a_huge_declared_width()
 {
    assert_comb_loop(
        "sparse accesses do not scale with a huge declared width",
        r#"
        module Top (
            a: input  logic,
            o: output logic,
        ) {
            var huge: logic<1000000>;
            always_comb {
                huge[0] = a;
                o = huge[999999];
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_region_and_function_mapping_regressions_dynamic_same_object_aliasing_uses_the_whole_longest_static_prefix()
 {
    assert_comb_loop(
        "dynamic same-object aliasing uses the whole longest static prefix",
        r#"
        module Top (
            index: input  logic<2>,
            o    : output logic,
        ) {
            var values: logic [4];
            always_comb {
                values[index] = o;
                o = values[0];
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_alias_and_opaque_effect_boundaries_function_bit_select_must_not_taint_a_disjoint_actual_bit()
 {
    assert_comb_loop(
        "function bit-select must not taint a disjoint actual bit",
        r#"
        module Top (
            o: output logic,
        ) {
            function bit_zero (x: input logic<8>) -> logic {
                return x[0];
            }
            var value: logic<8>;
            assign o = bit_zero(value);
            assign value[0] = 0;
            assign value[7] = o;
            assign value[6:1] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_alias_and_opaque_effect_boundaries_function_bit_select_must_retain_same_bit_feedback()
{
    assert_comb_loop(
        "function bit-select must retain same-bit feedback",
        r#"
        module Top (
            o: output logic,
        ) {
            function bit_zero (x: input logic<8>) -> logic {
                return x[0];
            }
            var value: logic<8>;
            assign o = bit_zero(value);
            assign value[0] = o;
            assign value[7:1] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_alias_and_opaque_effect_boundaries_function_bit_select_through_concatenation_ignores_high_operands()
 {
    assert_comb_loop(
        "function bit-select through concatenation ignores high operands",
        r#"
        module Top (
            o: output logic,
        ) {
            function bit_zero (x: input logic<8>) -> logic {
                return x[0];
            }
            var value: logic<7>;
            assign o = bit_zero({value, 1'b0});
            assign value[6] = o;
            assign value[5:0] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_alias_and_opaque_effect_boundaries_function_bit_select_through_concatenation_retains_low_operand()
 {
    assert_comb_loop(
        "function bit-select through concatenation retains low operand",
        r#"
        module Top (
            o: output logic,
        ) {
            function bit_zero (x: input logic<8>) -> logic {
                return x[0];
            }
            assign o = bit_zero({7'b0, o});
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_alias_and_opaque_effect_boundaries_function_bit_select_through_an_actual_slice_uses_its_low_bit()
 {
    assert_comb_loop(
        "function bit-select through an actual slice uses its low bit",
        r#"
        module Top (
            o: output logic,
        ) {
            function bit_zero (x: input logic<8>) -> logic {
                return x[0];
            }
            var value: logic<16>;
            assign o = bit_zero(value[15:8]);
            assign value[15] = o;
            assign value[14:0] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_alias_and_opaque_effect_boundaries_function_bit_select_through_an_actual_slice_retains_its_low_bit_feedback()
 {
    assert_comb_loop(
        "function bit-select through an actual slice retains its low-bit feedback",
        r#"
        module Top (
            o: output logic,
        ) {
            function bit_zero (x: input logic<8>) -> logic {
                return x[0];
            }
            var value: logic<16>;
            assign o = bit_zero(value[15:8]);
            assign value[8] = o;
            assign value[15:9] = 0;
            assign value[7:0] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_alias_and_opaque_effect_boundaries_function_region_crossing_a_concatenation_boundary_retains_both_operands()
 {
    assert_comb_loop(
        "function region crossing a concatenation boundary retains both operands",
        r#"
        module Top (
            o: output logic<2>,
        ) {
            function middle (x: input logic<8>) -> logic<2> {
                return x[4:3];
            }
            var high: logic<4>;
            var low : logic<4>;
            assign o = middle({high, low});
            assign high[0] = o[1];
            assign high[3:1] = 0;
            assign low = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_capture_coverage_obeys_caller_order() {
    // Why this case exists: a function's module-scope write is part of its
    // caller procedure. A dominating default or a later full write supplies
    // every preserved bit, so function-local weak-write coverage must not be
    // finalized before the caller MemorySSA reaches its exit.
    for body in [
        "value = 0; write_selected(index);",
        "write_selected(index); value = 0;",
    ] {
        let errors = analyze(&format!(
            r#"
            module Top (
                index: input  logic<2>,
                o    : output logic,
            ) {{
                var value: logic<4>;
                function write_selected (
                    index: input logic<2>,
                ) {{
                    value[index] = 1;
                }}
                always_comb {{
                    {body}
                    o = value[0];
                }}
            }}
            "#
        ));
        assert!(errors.is_empty(), "caller ordering is valid: {errors:#?}");
    }
}

#[test]
#[ignore = "SSA latch coverage follow-up after comb-loop migration: captured function write"]
fn comb_loop_function_capture_without_default_retains_coverage() {
    // Why this case exists: the caller-order kill controls above need a
    // positive control. Without a caller default, a captured dynamic write
    // still leaves unselected bits unassigned at the always_comb exit.
    assert_incomplete_assignment_without_comb_loop(
        "a captured weak write without a caller default remains incomplete",
        r#"
        module Top (
            index: input  logic<2>,
            o    : output logic,
        ) {
            var value: logic<4>;
            function write_selected (
                index: input logic<2>,
            ) {
                value[index] = 1;
            }
            always_comb {
                write_selected(index);
                o = value[0];
            }
        }
        "#,
    );
}

#[test]
#[ignore = "SSA latch coverage follow-up after comb-loop migration: uncalled function output"]
fn comb_loop_uncalled_function_still_checks_output_coverage() {
    // Why this case exists: output-argument completeness is a property of the
    // function definition, not of whether an always_comb happens to call it.
    // A runtime loop may execute zero times and leave the output unassigned.
    assert_incomplete_assignment_without_comb_loop(
        "an uncalled function still has to assign its output on every path",
        r#"
        module Top (
            o: output logic,
        ) {
            function maybe_write (
                n    : input  logic<32>,
                value: output logic,
            ) {
                for _index in 0..n {
                    value = 1;
                }
            }
            assign o = 0;
        }
        "#,
    );
}

#[test]
fn comb_loop_function_summary_fanout_is_memoized() {
    // Why this case exists: each function calls the previous specialization
    // twice, so per-call recursive analysis grows as 2^N. The source contains
    // only N unique function bodies and must be analyzed in O(N) summaries.
    let mut functions = String::from(
        r#"
        function f0 (
            x: input logic,
        ) -> logic {
            return x;
        }
        "#,
    );
    for depth in 1..=14 {
        functions.push_str(&format!(
            r#"
            function f{depth} (
                x: input logic,
            ) -> logic {{
                return f{previous}(x) ^ f{previous}(x);
            }}
            "#,
            previous = depth - 1,
        ));
    }
    crate::comb_loop_detect::reset_function_evaluation_count();
    let errors = analyze(&format!(
        r#"
        module Top (
            i: input  logic,
            o: output logic,
        ) {{
            {functions}
            assign o = f14(i);
        }}
        "#
    ));
    assert!(
        errors.is_empty(),
        "acyclic function fanout is valid: {errors:#?}"
    );
    assert_eq!(crate::comb_loop_detect::function_evaluation_count(), 29);
}

#[test]
fn function_summaries_reuse_module_metadata() {
    const COUNT: usize = 16;
    let padding = (0..COUNT)
        .map(|index| format!("var padding_{index}: logic;"))
        .collect::<Vec<_>>()
        .join("\n");
    let mut functions = String::new();
    let mut calls = String::new();
    for index in 0..COUNT {
        functions.push_str(&format!(
            "function function_{index} (value: input logic) -> logic {{ return value; }}\n"
        ));
        calls.push_str(&format!("padding_{index} = function_{index}(seed);\n"));
    }
    let code = format!(
        r#"
        module Top (seed: input logic, o: output logic) {{
            {padding}
            {functions}
            always_comb {{
                {calls}
                o = padding_0;
            }}
        }}
        "#
    );

    crate::comb_loop_detect::reset_module_context_entries();
    let errors = analyze(&code);
    assert!(
        errors.is_empty(),
        "independent calls are acyclic: {errors:#?}"
    );
    assert!(
        crate::comb_loop_detect::module_context_entries() <= COUNT * 7,
        "function summaries must share their module metadata: {}",
        crate::comb_loop_detect::module_context_entries(),
    );
}

#[test]
fn comb_loop_early_return_excludes_unreachable_function_dependency() {
    assert_comb_loop(
        "a return makes the following function dependency unreachable",
        r#"
        module Top (
            o: output logic,
        ) {
            function choose (
                feedback: input logic,
            ) -> logic {
                return 0;
                return feedback;
            }
            var feedback: logic;
            assign o = choose(feedback);
            assign feedback = o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_early_branch_return_preserves_its_reachable_dependency() {
    assert_comb_loop(
        "an early branch return remains an alternative to the fallback return",
        r#"
        module Top (
            select: input  logic,
            o     : output logic,
        ) {
            function choose (
                select  : input logic,
                feedback: input logic,
            ) -> logic {
                if select {
                    return feedback;
                }
                return 0;
            }
            var feedback: logic;
            assign o = choose(select, feedback);
            assign feedback = o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_all_branch_returns_exclude_following_dependency() {
    assert_comb_loop(
        "no path reaches a statement after both branches return",
        r#"
        module Top (
            select: input  logic,
            o     : output logic,
        ) {
            function choose (
                select  : input logic,
                feedback: input logic,
            ) -> logic {
                if select {
                    return 0;
                } else {
                    return 0;
                }
                return feedback;
            }
            var feedback: logic;
            assign o = choose(select, feedback);
            assign feedback = o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_branch_returns_preserve_reachable_function_dependency() {
    assert_comb_loop(
        "a reachable branch return preserves its feedback dependency",
        r#"
        module Top (
            select: input  logic,
            o     : output logic,
        ) {
            function choose (
                select  : input logic,
                feedback: input logic,
            ) -> logic {
                if select {
                    return feedback;
                } else {
                    return 0;
                }
            }
            var feedback: logic;
            assign o = choose(select, feedback);
            assign feedback = o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_formal_high_bit_ignores_short_unsigned_actual() {
    assert_comb_loop(
        "a function formal high bit does not read an unsigned short actual",
        r#"
        module Top (o: output logic) {
            var value: logic<2>;
            function high (i: input logic<4>) -> logic { return i[3]; }
            assign o = high(value);
            assign value[0] = o;
            assign value[1] = 0;
        }
        "#,
        false,
    );
}

fn signed_function_input_widening_code(source_bit: usize) -> String {
    format!(
        r#"
        module Top (o: output logic) {{
            var feedback: signed logic<2>;
            function high (i: input logic<4>) -> logic {{
                return i[3];
            }}
            assign o = high(feedback);
            assign feedback[{source_bit}] = o;
            assign feedback[{}] = 0;
        }}
        "#,
        1 - source_bit
    )
}

#[test]
fn comb_loop_function_signed_input_widening_replicates_sign_bit() {
    assert_comb_loop(
        "a signed function actual extends its sign bit into a wider formal",
        &signed_function_input_widening_code(1),
        true,
    );
}

#[test]
fn comb_loop_function_signed_input_widening_excludes_non_sign_bit() {
    assert_comb_loop(
        "a signed function actual does not extend a non-sign bit",
        &signed_function_input_widening_code(0),
        false,
    );
}

#[test]
fn comb_loop_function_unsigned_cast_prevents_signed_input_extension() {
    assert_comb_loop(
        "an unsigned cast prevents a signed function actual from sign-extending",
        r#"
        module Top (o: output logic) {
            var feedback: signed logic<2>;
            function high (i: input logic<4>) -> logic {
                return i[3];
            }
            assign o = high($unsigned(feedback));
            assign feedback[1] = o;
            assign feedback[0] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_function_signed_concat_input_extends_its_sign_bit() {
    assert_comb_loop(
        "a signed cast makes a concatenated function actual sign-extend",
        r#"
        module Top (o: output logic) {
            var feedback: logic<2>;
            function high (i: input logic<4>) -> logic {
                return i[3];
            }
            assign o = high($signed({feedback}));
            assign feedback[1] = o;
            assign feedback[0] = 0;
        }
        "#,
        true,
    );
}

fn signed_array_function_input_widening_code(source_element: usize) -> String {
    format!(
        r#"
        module Top (o: output logic) {{
            var feedback: signed logic<2> [2];
            function high (i: input logic<4> [2]) -> logic {{
                return i[0][3];
            }}
            assign o = high(feedback);
            assign feedback[{source_element}][1] = o;
            assign feedback[{source_element}][0] = 0;
            assign feedback[{}] = 0;
        }}
        "#,
        1 - source_element
    )
}

#[test]
fn comb_loop_function_signed_input_widening_preserves_array_element() {
    assert_comb_loop(
        "signed input widening retains the matching unpacked-array element",
        &signed_array_function_input_widening_code(0),
        true,
    );
}

#[test]
fn comb_loop_function_signed_input_widening_keeps_array_elements_disjoint() {
    assert_comb_loop(
        "signed input widening keeps sibling unpacked-array elements disjoint",
        &signed_array_function_input_widening_code(1),
        false,
    );
}

fn function_output_coercion_code(
    formal_type: &str,
    actual_type: &str,
    formal_width: usize,
    source_bit: usize,
    actual_bit: usize,
) -> String {
    let clears = (0..formal_width)
        .filter(|bit| *bit != source_bit)
        .map(|bit| format!("assign feedback[{bit}] = 0;"))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        r#"
        module Top (o: output logic) {{
            var feedback: logic<{formal_width}>;
            var passed: {actual_type};
            function copy (
                i: input logic<{formal_width}>,
                y: output {formal_type},
            ) {{
                y = i;
            }}
            always_comb {{
                copy(feedback, passed);
            }}
            assign feedback[{source_bit}] = passed[{actual_bit}];
            {clears}
            assign o = passed[0];
        }}
        "#
    )
}

#[test]
fn comb_loop_function_signed_output_widening_replicates_sign_bit() {
    assert_comb_loop(
        "a signed function output extends its sign bit into a wider actual",
        &function_output_coercion_code("signed logic<2>", "logic<4>", 2, 1, 3),
        true,
    );
}

#[test]
fn comb_loop_function_signed_output_widening_excludes_non_sign_bit() {
    assert_comb_loop(
        "a signed function output does not extend a non-sign bit",
        &function_output_coercion_code("signed logic<2>", "logic<4>", 2, 0, 3),
        false,
    );
}

#[test]
fn comb_loop_function_unsigned_output_widening_zero_extends_high_bit() {
    assert_comb_loop(
        "an unsigned function output does not feed a zero-extended actual bit",
        &function_output_coercion_code("logic<2>", "logic<4>", 2, 1, 3),
        false,
    );
}

#[test]
fn comb_loop_function_unsigned_output_zero_extends_into_signed_actual() {
    assert_comb_loop(
        "an unsigned function output zero-extends even when the wider actual is signed",
        &function_output_coercion_code("logic<2>", "signed logic<4>", 2, 1, 3),
        false,
    );
}

#[test]
fn comb_loop_function_output_narrowing_retains_low_bit() {
    assert_comb_loop(
        "a narrowed function output retains a copied low bit",
        &function_output_coercion_code("signed logic<4>", "logic<2>", 4, 0, 0),
        true,
    );
}

#[test]
fn comb_loop_function_output_narrowing_discards_high_bit() {
    assert_comb_loop(
        "a narrowed function output discards a formal high bit",
        &function_output_coercion_code("signed logic<4>", "logic<2>", 4, 3, 0),
        false,
    );
}

fn signed_array_function_output_widening_code(source_element: usize) -> String {
    format!(
        r#"
        module Top (o: output logic) {{
            var feedback: logic<2> [2];
            var passed: logic<4> [2];
            function copy (
                i: input logic<2> [2],
                y: output signed logic<2> [2],
            ) {{
                y = i;
            }}
            always_comb {{
                copy(feedback, passed);
            }}
            assign feedback[{source_element}][1] = passed[0][3];
            assign feedback[{source_element}][0] = 0;
            assign feedback[{}] = 0;
            assign o = passed[0][0];
        }}
        "#,
        1 - source_element
    )
}

#[test]
fn comb_loop_function_signed_output_widening_preserves_array_element() {
    assert_comb_loop(
        "signed output widening retains the matching unpacked-array element",
        &signed_array_function_output_widening_code(0),
        true,
    );
}

#[test]
fn comb_loop_function_signed_output_widening_keeps_array_elements_disjoint() {
    assert_comb_loop(
        "signed output widening keeps sibling unpacked-array elements disjoint",
        &signed_array_function_output_widening_code(1),
        false,
    );
}

fn signed_function_output_concat_code(source_bit: usize) -> String {
    format!(
        r#"
        module Top (o: output logic) {{
            var feedback: logic<2>;
            var high: logic<2>;
            var low: logic<2>;
            function copy (
                i: input logic<2>,
                y: output signed logic<2>,
            ) {{
                y = i;
            }}
            always_comb {{
                copy(feedback, {{high, low}});
            }}
            assign feedback[{source_bit}] = high[0];
            assign feedback[{}] = 0;
            assign o = low[0];
        }}
        "#,
        1 - source_bit
    )
}

#[test]
fn comb_loop_function_signed_output_extension_maps_concat_high_fragment() {
    assert_comb_loop(
        "signed output extension maps into a concatenated high fragment",
        &signed_function_output_concat_code(1),
        true,
    );
}

#[test]
fn comb_loop_function_signed_output_concat_excludes_non_sign_bit() {
    assert_comb_loop(
        "signed output extension into a concat excludes a non-sign bit",
        &signed_function_output_concat_code(0),
        false,
    );
}

#[test]
fn comb_loop_function_nested_summary_retains_signed_input_extension() {
    assert_comb_loop(
        "a nested function summary retains signed widening at its inner boundary",
        r#"
        module Top (o: output logic) {
            var feedback: signed logic<2>;
            function high (i: input logic<4>) -> logic {
                return i[3];
            }
            function nested (i: input signed logic<2>) -> logic {
                return high(i);
            }
            assign o = nested(feedback);
            assign feedback[1] = o;
            assign feedback[0] = 0;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_nested_summary_retains_signed_output_extension() {
    assert_comb_loop(
        "a nested function summary retains signed widening during copy-out",
        r#"
        module Top (o: output logic) {
            var feedback: logic<2>;
            var passed: logic<4>;
            function inner (
                i: input logic<2>,
                y: output signed logic<2>,
            ) {
                y = i;
            }
            function outer (
                i: input logic<2>,
                y: output logic<4>,
            ) {
                inner(i, y);
            }
            always_comb {
                outer(feedback, passed);
            }
            assign feedback[1] = passed[3];
            assign feedback[0] = 0;
            assign o = passed[0];
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_if_expression_arms_are_mutually_exclusive() {
    // Each function invocation selects one feed-forward equation. Flattening
    // both result alternatives into one source set invents the reverse edge.
    assert_comb_loop(
        "a function summary must not combine mutually exclusive expression arms",
        r#"
        module Identity (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            assign o = i;
        }
        module Top (
            sel: input  logic,
            o  : output logic,
        ) {
            function choose (
                state: input logic<2>,
                sel  : input logic,
            ) -> logic<2> {
                return if sel ? {state[0], 1'b0} : {1'b0, state[1]};
            }
            var state: logic<2>;
            inst passthrough: Identity (
                i: choose(state, sel),
                o: state,
            );
            assign o = |state;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_function_onehot_runtime_input_detects_feedback() {
    // `$onehot(value)` is synthesized from the runtime value. Therefore the
    // two assignments form value -> o -> value feedback through the function.
    assert_comb_loop(
        "a runtime system function in a user function carries its input dependency",
        r#"
        module Top (
            o: output logic,
        ) {
            function exactly_one (
                value: input logic<2>,
            ) -> logic {
                return $onehot(value);
            }
            var value: logic<2>;
            assign o = exactly_one(value);
            assign value[0] = o;
            assign value[1] = 1'b0;
        }
        "#,
        true,
    );
}

#[test]
fn function_summary_snapshots_actuals_in_source_order_false_negative() {
    assert_comb_loop(
        "a later actual side effect cannot replace an earlier captured value",
        r#"
        module Top (o: output bit) {
            var x       : bit;
            var y       : bit;
            var feedback: bit;
            function clear_x () -> bit {
                x = 0;
                return 0;
            }
            function first (
                value  : input bit,
                ignored: input bit,
            ) -> bit {
                return value;
            }
            assign feedback = x;
            always_comb {
                x = feedback;
                y = first(x, clear_x());
                x = y;
                o = x;
            }
        }
        "#,
        true,
    );
}

#[test]
fn function_summary_snapshots_actuals_in_source_order_false_positive() {
    assert_comb_loop(
        "a later actual side effect cannot taint an earlier captured value",
        r#"
        module Top (
            i: input  bit,
            o: output bit,
        ) {
            var x       : bit;
            var y       : bit;
            var feedback: bit;
            function write_x (value: input bit) -> bit {
                x = value;
                return 0;
            }
            function first (
                value  : input bit,
                ignored: input bit,
            ) -> bit {
                return value;
            }
            assign feedback = y;
            always_comb {
                x = i;
                y = first(x, write_x(feedback));
                x = 0;
                o = y;
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_function_output_destination_selector_controls_copyback() {
    assert_comb_loop(
        "a function output copyback is controlled by its dynamic destination selector",
        r#"
        module Top (o: output logic) {
            var selector: logic;
            var value   : logic<2>;
            function set (v: output logic) {
                v = 1;
            }
            assign selector = value[0];
            always_comb {
                value = 0;
                set(value[selector]);
                o = |value;
            }
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_output_destination_selector_accepts_independent_input() {
    assert_comb_loop(
        "an independent function output selector does not create feedback",
        r#"
        module Top (selector: input logic, o: output logic) {
            var value: logic<2>;
            function set (v: output logic) {
                v = 1;
            }
            always_comb {
                value = 0;
                set(value[selector]);
                o = |value;
            }
        }
        "#,
        false,
    );
}

fn dynamic_function_output_interleaved_static_coordinate_code(feedback_middle: usize) -> String {
    format!(
        r#"
        module Top (
            first: input  u32,
            last : input  u32,
            o    : output logic,
        ) {{
            var feedback: logic;
            var bus: logic [2, 2, 2];
            function copy (
                i: input  logic,
                y: output logic,
            ) {{
                y = i;
            }}
            always_comb {{
                bus[0][0][0] = 0;
                bus[0][0][1] = 0;
                bus[0][1][0] = 0;
                bus[0][1][1] = 0;
                bus[1][0][0] = 0;
                bus[1][0][1] = 0;
                bus[1][1][0] = 0;
                bus[1][1][1] = 0;
                copy(feedback, bus[first][0][last]);
                o = feedback;
            }}
            assign feedback = bus[0][{feedback_middle}][0];
        }}
        "#,
    )
}

#[test]
fn comb_loop_dynamic_function_output_preserves_an_interleaved_static_coordinate() {
    let code = dynamic_function_output_interleaved_static_coordinate_code(0);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "function copyback reaches the selected interleaved static coordinate",
        &code,
        true,
    );
}

#[test]
fn comb_loop_dynamic_function_output_keeps_an_interleaved_static_coordinate_disjoint() {
    let code = dynamic_function_output_interleaved_static_coordinate_code(1);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "function copyback cannot cross an interleaved static coordinate",
        &code,
        false,
    );
}

fn dynamic_function_output_interleaved_static_coordinate_with_dynamic_packed_select_code(
    feedback_middle: usize,
) -> String {
    format!(
        r#"
        module Top (
            first    : input  u32,
            last     : input  u32,
            bit_index: input  u32,
            o        : output logic,
        ) {{
            var feedback: logic;
            var bus: logic<2> [2, 2, 2];
            function copy (
                i: input  logic,
                y: output logic,
            ) {{
                y = i;
            }}
            always_comb {{
                bus[0][0][0] = 0;
                bus[0][0][1] = 0;
                bus[0][1][0] = 0;
                bus[0][1][1] = 0;
                bus[1][0][0] = 0;
                bus[1][0][1] = 0;
                bus[1][1][0] = 0;
                bus[1][1][1] = 0;
                copy(feedback, bus[first][0][last][bit_index]);
                o = feedback;
            }}
            assign feedback = bus[0][{feedback_middle}][0][0];
        }}
        "#,
    )
}

#[test]
fn comb_loop_dynamic_function_output_with_a_dynamic_packed_select_preserves_an_interleaved_static_coordinate()
 {
    let code =
        dynamic_function_output_interleaved_static_coordinate_with_dynamic_packed_select_code(0);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "dynamic packed function copyback reaches its selected interleaved array coordinate",
        &code,
        true,
    );
}

#[test]
fn comb_loop_dynamic_function_output_with_a_dynamic_packed_select_keeps_an_interleaved_static_coordinate_disjoint()
 {
    let code =
        dynamic_function_output_interleaved_static_coordinate_with_dynamic_packed_select_code(1);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "dynamic packed function copyback cannot cross an interleaved static array coordinate",
        &code,
        false,
    );
}

#[test]
fn comb_loop_dynamic_function_output_does_not_control_an_unreachable_periodic_gap() {
    assert_comb_loop(
        "function copyback to the odd suffix cannot write the even selector bit",
        r#"
        module Top (o: output logic) {
            var index: logic;
            var bus  : logic [2, 2];
            function set (y: output logic) {
                y = 0;
            }
            assign index = bus[0][0];
            always_comb {
                bus[0][0] = 0;
                bus[0][1] = 0;
                bus[1][0] = 0;
                bus[1][1] = 0;
                set(bus[index][1]);
                o = bus[0][0] | bus[0][1] | bus[1][0] | bus[1][1];
            }
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_dynamic_function_output_controls_a_reachable_periodic_candidate() {
    assert_comb_loop(
        "function copyback retains selector feedback for a reachable suffix bit",
        r#"
        module Top (o: output logic) {
            var index: logic;
            var bus  : logic [2, 2];
            function set (y: output logic) {
                y = 0;
            }
            assign index = bus[0][1];
            always_comb {
                bus[0][0] = 0;
                bus[0][1] = 0;
                bus[1][0] = 0;
                bus[1][1] = 0;
                set(bus[index][1]);
                o = bus[0][0] | bus[0][1] | bus[1][0] | bus[1][1];
            }
        }
        "#,
        true,
    );
}

fn dynamic_function_output_code(
    nested: bool,
    packed: bool,
    destination: &str,
    feedback_source: &str,
) -> String {
    let bus_type = if packed {
        "logic<2> [2, 2]"
    } else {
        "logic [2, 2]"
    };
    let nested_function = nested.then_some(
        r#"
        function nested_copy (
            i: input logic,
            y: output logic,
        ) {
            copy(i, y);
        }
        "#,
    );
    let callee = if nested { "nested_copy" } else { "copy" };
    format!(
        r#"
        module Top (
            index: input u32,
            o    : output logic,
        ) {{
            var feedback: logic;
            var bus: {bus_type};
            function copy (
                i: input logic,
                y: output logic,
            ) {{
                y = i;
            }}
            {nested_function}
            always_comb {{
                bus[0][0] = 0;
                bus[0][1] = 0;
                bus[1][0] = 0;
                bus[1][1] = 0;
                {callee}(feedback, {destination});
                o = feedback;
            }}
            assign feedback = {feedback_source};
        }}
        "#,
        nested_function = nested_function.unwrap_or_default(),
    )
}

#[test]
fn comb_loop_dynamic_function_output_reaches_every_candidate_in_static_prefix() {
    let code = dynamic_function_output_code(false, false, "bus[0][index]", "bus[0][1]");
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "a dynamic function output reaches every candidate below its static prefix",
        &code,
        true,
    );
}

#[test]
fn comb_loop_dynamic_function_output_keeps_outer_prefixes_disjoint() {
    assert_comb_loop(
        "a dynamic function output cannot escape its static outer prefix",
        &dynamic_function_output_code(false, false, "bus[0][index]", "bus[1][0]"),
        false,
    );
}

#[test]
fn comb_loop_dynamic_function_output_preserves_packed_position() {
    assert_comb_loop(
        "a dynamic unpacked output retains its selected packed bit",
        &dynamic_function_output_code(false, true, "bus[1][index][0]", "bus[1][1][0]"),
        true,
    );
}

#[test]
fn comb_loop_dynamic_function_output_keeps_packed_bits_disjoint() {
    assert_comb_loop(
        "a dynamic unpacked output does not taint a disjoint packed bit",
        &dynamic_function_output_code(false, true, "bus[1][index][0]", "bus[1][1][1]"),
        false,
    );
}

#[test]
fn comb_loop_dynamic_function_output_survives_a_nested_summary() {
    let code = dynamic_function_output_code(true, false, "bus[0][index]", "bus[0][1]");
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "a dynamic function output candidate survives a nested function summary",
        &code,
        true,
    );
}

#[test]
fn comb_loop_dynamic_function_output_summary_keeps_outer_prefixes_disjoint() {
    assert_comb_loop(
        "a summarized dynamic function output retains its static outer prefix",
        &dynamic_function_output_code(true, false, "bus[0][index]", "bus[1][0]"),
        false,
    );
}

fn dynamic_function_output_static_suffix_code(feedback_element: usize) -> String {
    format!(
        r#"
        module Top (
            index: input  u32,
            o    : output logic,
        ) {{
            var feedback: logic;
            var bus: logic [2, 2];
            function copy (
                i: input  logic,
                y: output logic,
            ) {{
                y = i;
            }}
            always_comb {{
                bus[0][0] = 0;
                bus[0][1] = 0;
                bus[1][0] = 0;
                bus[1][1] = 0;
                copy(feedback, bus[index][0]);
                o = feedback;
            }}
            assign feedback = bus[0][{feedback_element}];
        }}
        "#,
    )
}

#[test]
fn comb_loop_dynamic_function_output_preserves_static_suffix_feedback() {
    let code = dynamic_function_output_static_suffix_code(0);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "a dynamic function output retains feedback through its static suffix",
        &code,
        true,
    );
}

#[test]
fn comb_loop_dynamic_function_output_keeps_other_static_suffix_disjoint() {
    let code = dynamic_function_output_static_suffix_code(1);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "a dynamic function output does not taint another static suffix",
        &code,
        false,
    );
}

fn dynamic_function_array_output_code(feedback_element: usize) -> String {
    format!(
        r#"
        module Top (
            index: input u32,
            o    : output logic,
        ) {{
            var feedback: logic;
            var bus: logic [2, 2];
            function place (
                i: input logic,
                y: output logic [2],
            ) {{
                y[0] = i;
                y[1] = 0;
            }}
            always_comb {{
                bus[0][0] = 0;
                bus[0][1] = 0;
                bus[1][0] = 0;
                bus[1][1] = 0;
                place(feedback, bus[index]);
                o = feedback;
            }}
            assign feedback = bus[1][{feedback_element}];
        }}
        "#,
    )
}

#[test]
fn comb_loop_dynamic_function_array_output_preserves_trailing_element_position() {
    let code = dynamic_function_array_output_code(0);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "a dynamic function array output preserves its trailing element position",
        &code,
        true,
    );
}

#[test]
fn comb_loop_dynamic_function_array_output_keeps_trailing_elements_disjoint() {
    let code = dynamic_function_array_output_code(1);
    assert!(comb_loop_analysis_is_complete(&code));
    assert_comb_loop(
        "a dynamic function array output does not taint another trailing element",
        &code,
        false,
    );
}

#[test]
fn expression_snapshot_preserves_nested_function_return_dependencies() {
    assert_comb_loop(
        "an effects pass cannot discard a nested call used by the cached return value",
        r#"
        module Top (o: output bit) {
            function inner (value: input bit) -> bit {
                return value;
            }
            function outer (value: input bit) -> bit {
                return inner(value);
            }
            always_comb {
                o = outer(o);
            }
        }
        "#,
        true,
    );
}

#[test]
fn repeated_calls_reuse_the_function_write_footprint() {
    const WIDTH: usize = 128;
    let writes = (0..WIDTH)
        .map(|bit| format!("state[{bit}] = 0;"))
        .collect::<Vec<_>>()
        .join("\n");
    let calls = (0..WIDTH)
        .map(|_| "clear();")
        .collect::<Vec<_>>()
        .join("\n");
    let code = format!(
        r#"
        module Top (o: output logic) {{
            var state: logic<{WIDTH}>;
            function clear () {{
                {writes}
            }}
            always_comb {{
                {calls}
            }}
            assign o = |state;
        }}
        "#
    );

    crate::comb_loop_detect::reset_function_evaluation_count();
    let errors = analyze(&code);
    assert!(
        errors.is_empty(),
        "repeated constant writes are acyclic: {errors:#?}"
    );
    let visits = crate::comb_loop_detect::write_footprint_statement_visits();
    assert!(
        visits <= WIDTH * 4 + 8,
        "a shared function body must be walked once, not once per call site: {visits}"
    );
}

#[test]
fn recursive_function_summary_contexts_clone_only_referenced_metadata() {
    const COUNT: usize = 16;
    let padding = (0..COUNT)
        .map(|index| format!("var padding_{index}: logic;"))
        .collect::<Vec<_>>()
        .join("\n");
    let padding_assignments = (0..COUNT)
        .map(|index| format!("padding_{index} = seed;"))
        .collect::<Vec<_>>()
        .join("\n");
    let padding_uses = (0..COUNT)
        .map(|index| format!("padding_{index}"))
        .collect::<Vec<_>>()
        .join(" | ");
    let mut functions = String::new();
    for index in (0..COUNT).rev() {
        let value = if index + 1 == COUNT {
            "value".to_owned()
        } else {
            format!("function_{}(value)", index + 1)
        };
        functions.push_str(&format!(
            "function function_{index} (value: input logic) -> logic {{ return {value}; }}\n"
        ));
    }
    let code = format!(
        r#"
        module Top (seed: input logic, o: output logic) {{
            {padding}
            {functions}
            always_comb {{
                {padding_assignments}
                o = function_0(seed) | {padding_uses};
            }}
        }}
        "#
    );

    crate::comb_loop_detect::reset_module_context_entries();
    let errors = analyze(&code);
    assert!(
        errors.is_empty(),
        "the function chain is acyclic: {errors:#?}"
    );
    assert!(
        crate::comb_loop_detect::module_context_entries() <= COUNT * 12,
        "each summary depth must clone only its local metadata: {}",
        crate::comb_loop_detect::module_context_entries(),
    );
}
