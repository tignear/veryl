use super::*;

fn assert_comb_loop(case: &str, code: &str, expected: bool) {
    let errors = analyze(code);
    let actual = errors
        .iter()
        .any(|error| matches!(error, AnalyzerError::CombinationalLoop { .. }));
    assert_eq!(actual, expected, "{case}: {errors:?}");
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

fn whole_unpacked_instance_code(output_index: usize) -> String {
    format!(
        r#"
        module Identity (
            i: input logic [200000], o: output logic [200000],
        ) {{ assign o = i; }}
        module Top (o: output logic) {{
            var feedback: logic [200000];
            var passed: logic [200000];
            inst u: Identity (i: feedback, o: passed);
            assign feedback[123456] = passed[{output_index}];
            assign o = passed[0];
        }}
        "#
    )
}

fn assert_unaligned_unpacked_instance_input(target: usize, expected: bool) {
    assert_comb_loop(
        "an unaligned unpacked instance input preserves element identity",
        &format!(
            r#"
            module Child (i: input logic [2], o: output logic) {{ assign o = !i[1]; }}
            module Top (o: output logic) {{
                var value: logic [2];
                var passed: logic;
                inst u: Child (i: value, o: passed);
                assign value[{target}] = passed;
                assign value[{}] = 0;
                assign o = passed;
            }}
            "#,
            1 - target
        ),
        expected,
    );
}

comb_loop_case!(
    comb_loop_whole_unpacked_matching_element_retains_feedback,
    "a distant matching element retains feedback",
    whole_unpacked_instance_code(123_456),
    true
);

comb_loop_case!(
    comb_loop_whole_unpacked_disjoint_elements_remain_independent,
    "distant disjoint elements remain independent",
    whole_unpacked_instance_code(65_432),
    false
);

fn periodic_repeat_code(through_instance: bool, count: usize, index: usize, bit: usize) -> String {
    let body = if through_instance {
        "inst u: Broadcast (i: feedback, o: passed);".to_string()
    } else {
        format!("assign passed = '{{feedback repeat {count}}};")
    };
    format!(
        r#"
        module Broadcast (i: input logic<2>, o: output logic<2> [{count}]) {{
            assign o = '{{i repeat {count}}};
        }}
        module Top (o: output logic) {{
            var feedback: logic<2>;
            var passed: logic<2> [{count}];
            {body}
            assign feedback[0] = passed[{index}][{bit}];
            assign feedback[1] = 0;
            assign o = passed[0][0];
        }}
        "#
    )
}

fn periodic_repeat_two_level_code(bit: usize) -> String {
    format!(
        r#"
        module Broadcast (i: input logic<2>, o: output logic<2> [64]) {{
            assign o = '{{i repeat 64}};
        }}
        module Wrapper (
            i: input logic<2>, o: output logic<2> [64], tap: output logic,
        ) {{
            inst u: Broadcast (i: i, o: o);
            assign tap = i[0];
        }}
        module Top (o: output logic) {{
            var feedback: logic<2>;
            var passed: logic<2> [64];
            var tap: logic;
            inst u: Wrapper (i: feedback, o: passed, tap: tap);
            assign feedback[0] = passed[42][{bit}];
            assign feedback[1] = 0;
            assign o = tap;
        }}
        "#
    )
}

comb_loop_case!(
    comb_loop_instance_repeat_retains_matching_phase_at_scale,
    "instance repeat retains matching phase feedback",
    periodic_repeat_code(true, 200_000, 123_456, 0),
    true
);

comb_loop_case!(
    comb_loop_instance_repeat_keeps_different_phase_disjoint,
    "instance repeat keeps a different phase disjoint",
    periodic_repeat_code(true, 64, 42, 1),
    false
);

comb_loop_case!(
    comb_loop_periodic_phase_survives_two_module_summaries,
    "a periodic phase survives two module summaries",
    periodic_repeat_two_level_code(0),
    true
);

comb_loop_case!(
    comb_loop_periodic_disjoint_phase_survives_two_module_summaries,
    "a disjoint periodic phase survives two module summaries",
    periodic_repeat_two_level_code(1),
    false
);

fn packed_repeat_code(body: &str, count: usize, phase: usize) -> String {
    let width = count * 4;
    format!(
        r#"
        module Top (o: output logic) {{
            var feedback: logic<4>;
            var passed: logic<{width}>;
            {body}
            assign feedback[0] = passed[{phase}];
            assign feedback[3:1] = 0;
            assign o = passed[0];
        }}
        "#
    )
}

comb_loop_case!(
    comb_loop_local_packed_repeat_retains_matching_phase,
    "a broad local packed repeat retains matching phase feedback",
    packed_repeat_code("assign passed = {feedback repeat 64};", 64, 0),
    true
);

comb_loop_case!(
    comb_loop_local_packed_repeat_keeps_disjoint_phase,
    "a broad local packed repeat keeps a disjoint phase independent",
    packed_repeat_code("assign passed = {feedback repeat 64};", 64, 1),
    false
);

comb_loop_case!(
    comb_loop_nested_packed_repeats_with_a_shifted_source_are_loop_free_at_scale,
    "nested broad repeats retain the shifted source's nonzero displacement",
    r#"
    module Top (o: output logic) {
        const N: u32 = 5000;
        var x: logic<105 * N>;
        assign x = {{{(x >> 2) as u32, 3'b0} repeat N} repeat 3};
        assign o = x[0];
    }
    "#,
    false
);

fn function_packed_repeat_code(phase: usize) -> String {
    format!(
        r#"
        module Top (o: output logic) {{
            var feedback: logic<4>;
            var passed: logic<256>;
            function broadcast (x: input logic<4>) -> logic<256> {{
                return {{x repeat 64}};
            }}
            assign passed = broadcast(feedback);
            assign feedback[0] = passed[{phase}];
            assign feedback[3:1] = 0;
            assign o = passed[0];
        }}
        "#
    )
}

comb_loop_case!(
    comb_loop_function_packed_repeat_retains_matching_phase,
    "a packed repeat remains positional through a function summary",
    function_packed_repeat_code(0),
    true
);

comb_loop_case!(
    comb_loop_function_packed_repeat_keeps_disjoint_phase,
    "a function summary keeps disjoint packed-repeat phases independent",
    function_packed_repeat_code(1),
    false
);

fn child_packed_repeat_code(internal_temporary: bool, count: usize, phase: usize) -> String {
    let width = count * 4;
    let body = if internal_temporary {
        format!(
            "var repeated: logic<{width}>; assign repeated = {{i repeat {count}}}; assign o = repeated;"
        )
    } else {
        format!("assign o = {{i repeat {count}}};")
    };
    format!(
        r#"
        module Broadcast (i: input logic<4>, o: output logic<{width}>) {{
            {body}
        }}
        module Top (o: output logic) {{
            var feedback: logic<4>;
            var passed: logic<{width}>;
            inst u: Broadcast (i: feedback, o: passed);
            assign feedback[0] = passed[{phase}];
            assign feedback[3:1] = 0;
            assign o = passed[0];
        }}
        "#
    )
}

comb_loop_case!(
    comb_loop_child_packed_repeat_retains_matching_phase_at_scale,
    "a 200k-copy packed repeat retains matching phase through a module summary",
    child_packed_repeat_code(false, 200_000, 0),
    true
);

comb_loop_case!(
    comb_loop_child_packed_repeat_keeps_disjoint_phase_at_scale,
    "a 200k-copy packed repeat keeps a disjoint phase independent",
    child_packed_repeat_code(false, 200_000, 1),
    false
);

comb_loop_case!(
    comb_loop_child_temporary_packed_repeat_retains_matching_phase,
    "an internal temporary preserves matching packed-repeat phase",
    child_packed_repeat_code(true, 64, 0),
    true
);

comb_loop_case!(
    comb_loop_child_temporary_packed_repeat_keeps_disjoint_phase,
    "an internal temporary preserves disjoint packed-repeat phase",
    child_packed_repeat_code(true, 64, 1),
    false
);

fn child_array_repeat_code(element: usize) -> String {
    format!(
        r#"
        module Broadcast (i: input logic [2], o: output logic [64, 2]) {{
            assign o = '{{i repeat 64}};
        }}
        module Top (o: output logic) {{
            var feedback: logic [2];
            var passed: logic [64, 2];
            inst u: Broadcast (i: feedback, o: passed);
            assign feedback[0] = passed[42][{element}];
            assign feedback[1] = 0;
            assign o = passed[0][0];
        }}
        "#
    )
}

comb_loop_case!(
    comb_loop_child_array_repeat_retains_matching_element_phase,
    "an array repeat retains the matching source-element residue",
    child_array_repeat_code(0),
    true
);

comb_loop_case!(
    comb_loop_child_array_repeat_keeps_disjoint_element_phase,
    "an array repeat keeps a disjoint source-element residue independent",
    child_array_repeat_code(1),
    false
);

fn multidimensional_repeat_code(source_element: usize, packed_phase: usize) -> String {
    format!(
        r#"
        module Broadcast (
            i: input logic<2> [2],
            o: output logic<128> [8, 8, 2],
        ) {{
            var tile: logic<128> [2];
            var repeated_tile: logic<128> [8, 2];
            assign tile[0] = {{i[0] repeat 64}};
            assign tile[1] = {{i[1] repeat 64}};
            assign repeated_tile = '{{tile repeat 8}};
            assign o = '{{repeated_tile repeat 8}};
        }}
        module Top (o: output logic) {{
            var feedback: logic<2> [2];
            var passed: logic<128> [8, 8, 2];
            inst u: Broadcast (i: feedback, o: passed);
            assign feedback[0][0] = passed[6][4][{source_element}][{packed_phase}];
            assign feedback[0][1] = 0;
            assign feedback[1] = 0;
            assign o = passed[0][0][0][0];
        }}
        "#
    )
}

comb_loop_case!(
    comb_loop_multidimensional_repeat_retains_matching_phase,
    "nested repeats retain matching unpacked and packed phases",
    multidimensional_repeat_code(0, 0),
    true
);

comb_loop_case!(
    comb_loop_multidimensional_repeat_keeps_disjoint_array_phase,
    "nested repeats keep a disjoint unpacked phase independent",
    multidimensional_repeat_code(1, 0),
    false
);

comb_loop_case!(
    comb_loop_multidimensional_repeat_keeps_disjoint_packed_phase,
    "nested repeats keep a disjoint packed phase independent",
    multidimensional_repeat_code(0, 1),
    false
);

#[test]
fn comb_loop_core_semantics_and_region_regressions_module_instance_feedthrough_child_has_assign_out_in_parent()
 {
    // Module instance feedthrough: child has `assign out = in;`. Parent
    // closes the loop with `assign x = y`. Should detect.
    let code = r#"
    module Buf (
        i: input  logic<8>,
        o: output logic<8>,
    ) {
        assign o = i;
    }

    module Top (
        a: input  logic<8>,
        b: output logic<8>,
    ) {
        var x: logic<8>;
        var y: logic<8>;
        inst u: Buf (
            i: x,
            o: y,
        );
        assign x = y;
        assign b = y;
    }
    "#;
    let errors = analyze(code);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, AnalyzerError::CombinationalLoop { .. }))
    );
}

#[test]
fn comb_loop_core_semantics_and_region_regressions_module_instance_with_ff_driven_output_no_loop_should_be_detected()
 {
    // Module instance with FF-driven output: no loop should be detected.
    let code = r#"
    module Reg (
        clk: input  clock,
        i:   input  logic<8>,
        o:   output logic<8>,
    ) {
        always_ff (clk) {
            o = i;
        }
    }

    module Top (
        clk: input  clock,
        a:   input  logic<8>,
        b:   output logic<8>,
    ) {
        var x: logic<8>;
        var y: logic<8>;
        inst u: Reg (
            clk: clk,
            i: x,
            o: y,
        );
        assign x = y;
        assign b = y;
    }
    "#;
    let errors = analyze(code);
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, AnalyzerError::CombinationalLoop { .. }))
    );
}

#[test]
fn comb_loop_dynamic_region_survives_module_summary() {
    // Why this case exists: an instance port is a SystemVerilog data path, so
    // a child wildcard output must remain a wildcard through every summary.
    // For idx == 0 the Top-level feedback path is realizable and structural.
    assert_comb_loop(
        "a dynamic child output preserves feedback across two summaries",
        r#"
        module Leaf (
            i: input  logic,
            o: output logic,
        ) {
            assign o = i;
        }

        module Middle (
            i  : input  logic,
            idx: input  logic,
            o  : output logic<2>,
        ) {
            inst u: Leaf (
                i: i,
                o: o[idx],
            );
        }

        module Top (
            idx: input  logic,
            o  : output logic,
        ) {
            var feedback: logic;
            var bus     : logic<2>;
            inst u: Middle (
                i  : feedback,
                idx: idx,
                o  : bus,
            );
            assign feedback = bus[0];
            assign o = feedback;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_module_summary_positions_a_vector_identity_module_preserves_disjoint_bit_positions()
 {
    assert_comb_loop(
        "a vector identity module preserves disjoint bit positions",
        r#"
        module Child (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            assign o = i;
        }
        module Top (
            o: output logic<2>,
        ) {
            var child_i: logic<2>;
            var child_o: logic<2>;
            inst u: Child (
                i: child_i,
                o: child_o,
            );
            assign child_i[0] = child_o[1];
            assign child_i[1] = 0;
            assign o = child_o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_module_summary_positions_a_vector_identity_module_retains_same_bit_feedback()
{
    assert_comb_loop(
        "a vector identity module retains same-bit feedback",
        r#"
        module Child (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            assign o = i;
        }
        module Top (
            o: output logic<2>,
        ) {
            var child_i: logic<2>;
            var child_o: logic<2>;
            inst u: Child (
                i: child_i,
                o: child_o,
            );
            assign child_i[0] = child_o[0];
            assign child_i[1] = 0;
            assign o = child_o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_module_summary_preserves_multidimensional_array_elements() {
    assert_comb_loop(
        "a multidimensional identity keeps distinct elements independent",
        r#"
        module Child (
            i: input  logic<2> [2, 3],
            o: output logic<2> [2, 3],
        ) {
            assign o = i;
        }
        module Top (o: output logic) {
            var child_i: logic<2> [2, 3];
            var child_o: logic<2> [2, 3];
            inst u: Child (i: child_i, o: child_o);
            assign child_i[0][1][0] = child_o[1][1][0];
            assign child_i[0][1][1] = 0;
            assign o = child_o[0][0][0];
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_summary_detects_multidimensional_same_element_feedback() {
    assert_comb_loop(
        "a multidimensional identity retains the same element and bit",
        r#"
        module Child (
            i: input  logic<2> [2, 3],
            o: output logic<2> [2, 3],
        ) {
            assign o = i;
        }
        module Top (o: output logic) {
            var child_i: logic<2> [2, 3];
            var child_o: logic<2> [2, 3];
            inst u: Child (i: child_i, o: child_o);
            assign child_i[0][1][0] = child_o[0][1][0];
            assign child_i[0][1][1] = 0;
            assign o = child_o[0][0][0];
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_module_summary_preserves_packed_struct_members() {
    assert_comb_loop(
        "a packed struct identity keeps distinct members independent",
        r#"
        package Types {
            struct Pair { low: logic, high: logic, }
        }
        module Child (
            i: input  Types::Pair,
            o: output Types::Pair,
        ) {
            assign o = i;
        }
        module Top (o: output logic) {
            var child_i: Types::Pair;
            var child_o: Types::Pair;
            inst u: Child (i: child_i, o: child_o);
            assign child_i.low = child_o.high;
            assign child_i.high = 0;
            assign o = child_o.low;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_summary_detects_packed_struct_member_feedback() {
    assert_comb_loop(
        "a packed struct identity retains the same member",
        r#"
        package Types {
            struct Pair { low: logic, high: logic, }
        }
        module Child (
            i: input  Types::Pair,
            o: output Types::Pair,
        ) {
            assign o = i;
        }
        module Top (o: output logic) {
            var child_i: Types::Pair;
            var child_o: Types::Pair;
            inst u: Child (i: child_i, o: child_o);
            assign child_i.low = child_o.low;
            assign child_i.high = 0;
            assign o = child_o.low;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_instance_output_address_contributes_dependency() {
    // Why this case exists: idx selects the instance output destination and
    // is itself read from one candidate destination. This is the same address
    // feedback already detected for a procedural bus[idx] assignment.
    assert_comb_loop(
        "a dynamic instance output retains address feedback",
        r#"
        module Child (
            i: input  logic,
            o: output logic,
        ) {
            assign o = i;
        }
        module Top (
            seed: input  logic,
            o   : output logic,
        ) {
            var idx: logic;
            var bus: logic [2];
            inst u: Child (
                i: seed,
                o: bus[idx],
            );
            assign idx = bus[0];
            assign o = idx;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_dynamic_instance_output_considers_a_nonzero_unpacked_element() {
    assert_comb_loop(
        "a dynamic instance output can select a nonzero unpacked element",
        r#"
        module Child (i: input logic, o: output logic) {
            assign o = i;
        }
        module Top (o: output logic) {
            var index: logic;
            var bus  : logic [2];
            inst child: Child (
                i: index,
                o: bus[index],
            );
            assign index = bus[1];
            assign o = index;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_large_dynamic_instance_output_stays_sparse() {
    let code = r#"
        module Child (i: input logic, o: output logic) {
            assign o = i;
        }
        module Top (index: input u32, o: output logic) {
            var feedback: logic;
            var bus     : logic [1000000];
            inst child: Child (
                i: feedback,
                o: bus[index],
            );
            assign feedback = bus[999999];
            assign o = feedback;
        }
    "#;
    assert!(comb_loop_analysis_is_complete(code));
    assert_comb_loop(
        "a large dynamic output retains a distant candidate without expanding the array",
        code,
        true,
    );
}

fn multidimensional_dynamic_instance_output_code(selector_source: &str) -> String {
    format!(
        r#"
        module Child (i: input logic, o: output logic) {{
            assign o = i;
        }}
        module Top (o: output logic) {{
            var index: logic;
            var bus  : logic [2, 2];
            inst child: Child (
                i: index,
                o: bus[1][index],
            );
            assign index = {selector_source};
            assign o = index;
        }}
        "#
    )
}

#[test]
fn comb_loop_dynamic_instance_output_preserves_a_multidimensional_static_prefix() {
    assert_comb_loop(
        "a dynamic inner coordinate can select every element below its static prefix",
        &multidimensional_dynamic_instance_output_code("bus[1][1]"),
        true,
    );
}

#[test]
fn comb_loop_dynamic_instance_output_keeps_multidimensional_prefixes_disjoint() {
    assert_comb_loop(
        "a dynamic inner coordinate cannot escape its static outer prefix",
        &multidimensional_dynamic_instance_output_code("bus[0][1]"),
        false,
    );
}

fn packed_dynamic_instance_output_code(selector_source: &str) -> String {
    format!(
        r#"
        module Child (i: input logic<2>, o: output logic<2>) {{
            assign o = i;
        }}
        module Top (o: output logic) {{
            var index: logic;
            var bus  : logic<4> [2];
            inst child: Child (
                i: {{index, index}},
                o: bus[1][index+:2],
            );
            assign bus[0] = 0;
            assign index = {selector_source};
            assign o = index;
        }}
        "#
    )
}

#[test]
fn comb_loop_dynamic_instance_output_considers_every_packed_part_select_candidate() {
    assert_comb_loop(
        "an indexed packed part-select can include a bit beyond its zero-based window",
        &packed_dynamic_instance_output_code("bus[1][2]"),
        true,
    );
}

#[test]
fn comb_loop_dynamic_instance_output_keeps_packed_array_elements_disjoint() {
    assert_comb_loop(
        "a dynamic packed select cannot escape its selected unpacked element",
        &packed_dynamic_instance_output_code("bus[0][2]"),
        false,
    );
}

fn summarized_dynamic_instance_output_code(selector_source: &str) -> String {
    format!(
        r#"
        module Leaf (i: input logic, o: output logic) {{
            assign o = i;
        }}
        module Middle (selector: input logic, o: output logic) {{
            var bus: logic [2, 2];
            inst leaf: Leaf (
                i: selector,
                o: bus[1][selector],
            );
            assign o = {selector_source};
        }}
        module Top (o: output logic) {{
            var feedback: logic;
            inst middle: Middle (
                selector: feedback,
                o       : feedback,
            );
            assign o = feedback;
        }}
        "#
    )
}

#[test]
fn comb_loop_dynamic_instance_output_dependency_survives_a_module_summary() {
    assert_comb_loop(
        "a dynamic output address remains a dependency through a module summary",
        &summarized_dynamic_instance_output_code("bus[1][1]"),
        true,
    );
}

#[test]
fn comb_loop_dynamic_instance_output_summary_keeps_static_prefixes_disjoint() {
    assert_comb_loop(
        "a summarized dynamic output remains confined to its static prefix",
        &summarized_dynamic_instance_output_code("bus[0][1]"),
        false,
    );
}

fn packed_concat_conditional_actual_code(first: &str, second: &str) -> String {
    format!(
        r#"
        module Identity (i: input logic<2>, o: output logic<2>) {{
            assign o = i;
        }}
        module Top (
            c0: input logic,
            c1: input logic,
            o : output logic,
        ) {{
            var a     : logic;
            var b     : logic;
            var passed: logic<2>;
            inst identity: Identity (
                i: {{{first}, {second}}},
                o: passed,
            );
            assign a = passed[0];
            assign b = passed[1];
            assign o = a | b;
        }}
        "#
    )
}

fn ordered_instance_actual_code(actual: &str) -> String {
    format!(
        r#"
        module PickMiddle (i: input logic<3>, o: output logic) {{
            assign o = i[1];
        }}
        module Top (independent: input logic, o: output logic) {{
            var x       : logic;
            var feedback: logic;
            function set_x (value: input logic) -> logic {{
                x = value;
                return 0;
            }}
            inst pick: PickMiddle (
                i: {actual},
                o: feedback,
            );
            assign o = feedback;
        }}
        "#
    )
}

#[test]
fn instance_actual_projection_reads_the_version_at_each_syntax_occurrence() {
    crate::comb_loop_detect::reset_function_evaluation_count();
    assert_comb_loop(
        "a projected actual read sees the side effect that precedes its occurrence",
        &ordered_instance_actual_code("{set_x(feedback), x, set_x(independent)}"),
        true,
    );
    assert_eq!(
        crate::comb_loop_detect::function_evaluation_count(),
        2,
        "each syntactic side-effecting call in the actual is evaluated exactly once",
    );
}

#[test]
fn actual_branch_layout_walk_is_linear_in_syntactic_calls() {
    const CALLS: usize = 10_000;
    let actual = (0..CALLS)
        .map(|_| "identity(i)")
        .collect::<Vec<_>>()
        .join(", ");
    crate::comb_loop_detect::reset_function_evaluation_count();
    let errors = analyze(&format!(
        r#"
        module Sink (i: input logic<{CALLS}>, o: output logic) {{ assign o = |i; }}
        module Top (i: input logic, o: output logic) {{
            function identity (value: input logic) -> logic {{ return value; }}
            inst sink: Sink (i: {{{actual}}}, o: o);
        }}
        "#
    ));
    assert!(
        errors.is_empty(),
        "large call layout remains acyclic: {errors:#?}"
    );
    assert!(
        crate::comb_loop_detect::expression_layout_visit_count() <= CALLS * 4 + 16,
        "the preorder layout walk must visit each syntactic expression only a constant number of times",
    );
}

#[test]
fn pure_instance_actual_is_classified_once_before_its_linear_walk() {
    const TERMS: usize = 1_024;
    let mut level = vec!["i".to_string(); TERMS];
    while level.len() > 1 {
        level = level
            .chunks_exact(2)
            .map(|pair| format!("({} | {})", pair[0], pair[1]))
            .collect();
    }
    let actual = level.pop().expect("the expression has at least one term");
    crate::comb_loop_detect::reset_guarded_expression_probes();
    let errors = analyze(&format!(
        r#"
        module Sink (i: input logic, o: output logic) {{ assign o = i; }}
        module Top (i: input logic, o: output logic) {{
            inst sink: Sink (i: {actual}, o: o);
        }}
        "#
    ));
    assert!(
        errors.is_empty(),
        "deep pure actual is acyclic: {errors:#?}"
    );
    assert!(
        crate::comb_loop_detect::guarded_expression_probes() <= TERMS * 3 + 16,
        "guarded-expression classification must visit the actual only once",
    );
}

#[test]
fn following_instance_actual_effect_does_not_retroactively_taint_a_read() {
    assert_comb_loop(
        "a later actual side effect cannot alter an already captured middle bit",
        &ordered_instance_actual_code("{set_x(independent), x, set_x(feedback)}"),
        false,
    );
}

#[test]
fn nested_instance_actual_projection_preserves_source_order() {
    assert_comb_loop(
        "nested concat layout projects an occurrence-time value",
        &ordered_instance_actual_code("{{set_x(feedback), x}, set_x(independent)}"),
        true,
    );
}

#[test]
fn unpacked_instance_actual_projection_preserves_source_order() {
    assert_comb_loop(
        "unpacked literal layout projects an occurrence-time value",
        r#"
        module PickMiddle (i: input logic [3], o: output logic) {
            assign o = i[1];
        }
        module Top (independent: input logic, o: output logic) {
            var x       : logic;
            var feedback: logic;
            function set_x (value: input logic) -> logic {
                x = value;
                return 0;
            }
            inst pick: PickMiddle (
                i: '{set_x(feedback), x, set_x(independent)},
                o: feedback,
            );
            assign o = feedback;
        }
        "#,
        true,
    );
}

#[test]
fn struct_instance_actual_projection_preserves_source_order() {
    assert_comb_loop(
        "structure layout projects an occurrence-time member value",
        r#"
        package Types {
            struct Triple { high: logic, mid: logic, low: logic, }
        }
        module PickMiddle (i: input Types::Triple, o: output logic) {
            assign o = i.mid;
        }
        module Top (independent: input logic, o: output logic) {
            var x       : logic;
            var feedback: logic;
            function set_x (value: input logic) -> logic {
                x = value;
                return 0;
            }
            inst pick: PickMiddle (
                i: Types::Triple'{
                    high: set_x(feedback),
                    mid : x,
                    low : set_x(independent),
                },
                o: feedback,
            );
            assign o = feedback;
        }
        "#,
        true,
    );
}

#[test]
fn instance_actual_effect_and_value_share_the_same_branch_identity() {
    assert_comb_loop(
        "side effects and values from opposite ternary arms cannot form one cycle",
        r#"
        module Identity (i: input logic, o: output logic) {
            assign o = i;
        }
        module Top (select: input logic, o: output logic) {
            var x       : logic;
            var feedback: logic;
            function set_x (value: input logic) -> logic {
                x = value;
                return 0;
            }
            inst identity: Identity (
                i: if select ? set_x(feedback) : x,
                o: feedback,
            );
            assign o = feedback | x;
        }
        "#,
        false,
    );
}

#[test]
fn an_instance_actual_branch_with_direct_feedback_remains_a_loop() {
    assert_comb_loop(
        "one feasible ternary arm still retains its direct feedback",
        r#"
        module Identity (i: input logic, o: output logic) {
            assign o = i;
        }
        module Top (select: input logic, o: output logic) {
            var x       : logic;
            var feedback: logic;
            function set_x (value: input logic) -> logic {
                x = value;
                return 0;
            }
            inst identity: Identity (
                i: if select ? set_x(x) : feedback,
                o: feedback,
            );
            assign o = feedback | x;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_packed_concat_gives_each_conditional_a_stable_syntax_identity() {
    for (first, second) in [
        ("if c0 ? a : 1'b0", "if c1 ? b : 1'b0"),
        ("if c0 ? a : 1'b0", "if c1 ? 1'b0 : b"),
        ("if c0 ? 1'b0 : a", "if c1 ? b : 1'b0"),
        ("if c0 ? 1'b0 : a", "if c1 ? 1'b0 : b"),
    ] {
        assert_comb_loop(
            "each pair of independently selectable arms contains a realizable feedback cycle",
            &packed_concat_conditional_actual_code(first, second),
            true,
        );
    }
}

#[test]
fn comb_loop_one_packed_ternary_keeps_its_arms_mutually_exclusive() {
    assert_comb_loop(
        "one vector ternary cannot combine dependencies from its opposite arms",
        r#"
        module Identity (i: input logic<2>, o: output logic<2>) {
            assign o = i;
        }
        module Top (select: input logic, o: output logic) {
            var a     : logic;
            var b     : logic;
            var passed: logic<2>;
            inst identity: Identity (
                i: if select ? {a, 1'b0} : {1'b0, b},
                o: passed,
            );
            assign a = passed[0];
            assign b = passed[1];
            assign o = a | b;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_unpacked_literal_conditional_regions_do_not_regress() {
    assert_comb_loop(
        "separate unpacked literal elements retain independently selectable feedback",
        r#"
        module Identity (i: input logic [2], o: output logic [2]) {
            assign o = i;
        }
        module Top (
            c0: input logic,
            c1: input logic,
            o : output logic,
        ) {
            var a     : logic;
            var b     : logic;
            var passed: logic [2];
            inst identity: Identity (
                i: '{if c0 ? a : 0, if c1 ? 0 : b},
                o: passed,
            );
            assign a = passed[1];
            assign b = passed[0];
            assign o = a | b;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_conditional_function_calls_in_separate_concat_regions_keep_their_ids() {
    assert_comb_loop(
        "function-summary branches are remapped by syntactic call identity, not visit order",
        r#"
        module Identity (i: input logic<2>, o: output logic<2>) {
            assign o = i;
        }
        module Top (
            c0: input logic,
            c1: input logic,
            o : output logic,
        ) {
            function when_true (value: input logic, select: input logic) -> logic {
                return if select ? value : 0;
            }
            function when_false (value: input logic, select: input logic) -> logic {
                return if select ? 0 : value;
            }
            var a     : logic;
            var b     : logic;
            var passed: logic<2>;
            inst identity: Identity (
                i: {when_true(a, c0), when_false(b, c1)},
                o: passed,
            );
            assign a = passed[0];
            assign b = passed[1];
            assign o = a | b;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_function_summary_preserves_one_ternarys_arm_exclusivity_across_regions() {
    assert_comb_loop(
        "one summarized vector ternary cannot combine its opposite arms",
        r#"
        module Identity (i: input logic<2>, o: output logic<2>) {
            assign o = i;
        }
        module Top (select: input logic, o: output logic) {
            function choose (
                a     : input logic,
                b     : input logic,
                select: input logic,
            ) -> logic<2> {
                return if select ? {a, 1'b0} : {1'b0, b};
            }
            var a     : logic;
            var b     : logic;
            var passed: logic<2>;
            inst identity: Identity (
                i: choose(a, b, select),
                o: passed,
            );
            assign a = passed[0];
            assign b = passed[1];
            assign o = a | b;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_generated_actual_clones_have_distinct_branch_namespaces() {
    assert_comb_loop(
        "actuals cloned from one source range keep independent branch choices",
        r#"
        module Gate (i: input logic, o: output logic) {
            assign o = i;
        }
        module Top (select: input logic<2>, o: output logic) {
            var state : logic<2>;
            var passed: logic<2>;
            for i in 0..2 :gates {
                inst gate: Gate (
                    i: if i == 0 ?
                        (if select[i] ? state[i] : 0) :
                        (if select[i] ? 0 : state[i]),
                    o: passed[i],
                );
            }
            assign state[0] = passed[1];
            assign state[1] = passed[0];
            assign o = |state;
        }
        "#,
        true,
    );
}

fn conditional_instance_input_side_effect_code(return_value: &str) -> String {
    format!(
        r#"
        module Identity (i: input logic<2>, o: output logic<2>) {{
            assign o = i;
        }}
        module Top (c: input logic, o: output logic) {{
            var a     : logic;
            var x     : logic;
            var passed: logic<2>;
            function capture (value: input logic) -> logic {{
                x = value;
                return {return_value};
            }}
            inst identity: Identity (
                i: {{if c ? capture(a) : x, 1'b0}},
                o: passed,
            );
            assign a = passed[1];
            assign o = x;
        }}
        "#
    )
}

#[test]
fn comb_loop_instance_actual_does_not_join_opposite_side_effect_arms() {
    assert_comb_loop(
        "a packed actual cannot combine a true-arm write with a false-arm value dependency",
        &conditional_instance_input_side_effect_code("0"),
        false,
    );
}

#[test]
fn comb_loop_instance_actual_retains_a_same_arm_side_effect_loop() {
    assert_comb_loop(
        "the same packed actual still detects feedback wholly inside its true arm",
        &conditional_instance_input_side_effect_code("value"),
        true,
    );
}

fn conditional_instance_output_selector_side_effect_code(return_value: &str) -> String {
    format!(
        r#"
        module Source (o: output logic) {{
            assign o = 0;
        }}
        module Top (c: input logic, o: output logic) {{
            var a  : logic;
            var x  : logic;
            var bus: logic<2>;
            function capture (value: input logic) -> logic {{
                x = value;
                return {return_value};
            }}
            inst source: Source (
                o: bus[if c ? capture(a) : x],
            );
            assign a = bus[0];
            assign o = x;
        }}
        "#
    )
}

#[test]
fn comb_loop_instance_output_selector_does_not_join_opposite_side_effect_arms() {
    assert_comb_loop(
        "an output selector cannot combine its true-arm write with its false-arm address",
        &conditional_instance_output_selector_side_effect_code("0"),
        false,
    );
}

#[test]
fn comb_loop_instance_output_selector_retains_a_same_arm_side_effect_loop() {
    assert_comb_loop(
        "an output selector still detects feedback wholly inside its true arm",
        &conditional_instance_output_selector_side_effect_code("value"),
        true,
    );
}

fn short_circuit_instance_actual_code(expression: &str, return_value: &str) -> String {
    format!(
        r#"
        module Identity (i: input logic, o: output logic) {{
            assign o = i;
        }}
        module Top (c: input logic, o: output logic) {{
            var a     : logic;
            var x     : logic;
            var passed: logic;
            function capture (value: input logic) -> logic {{
                x = value;
                return {return_value};
            }}
            inst identity: Identity (
                i: {expression},
                o: passed,
            );
            assign a = passed;
            assign o = x;
        }}
        "#
    )
}

#[test]
fn comb_loop_short_circuit_actuals_keep_dead_function_results_loop_free() {
    for (expression, return_value) in [("c && capture(a)", "0"), ("c || capture(a)", "1")] {
        assert_comb_loop(
            "a dynamic short-circuit call with a constant result has no return path",
            &short_circuit_instance_actual_code(expression, return_value),
            false,
        );
    }
}

#[test]
fn comb_loop_short_circuit_actuals_retain_live_function_result_feedback() {
    for expression in ["c && capture(a)", "c || capture(a)"] {
        assert_comb_loop(
            "a dynamic short-circuit call retains feedback in its evaluated arm",
            &short_circuit_instance_actual_code(expression, "value"),
            true,
        );
    }
}

#[test]
fn comb_loop_instance_input_selector_side_effect_is_recorded() {
    // Why this case exists: an otherwise plain instance actual still evaluates
    // the expressions in its selectors. Skipping the observer for mem[touch(o)]
    // would lose touch's module-scope write and hide the x -> o -> x cycle.
    assert_comb_loop(
        "an instance input selector retains a called function global write",
        r#"
        module Sink (
            i: input logic,
        ) {}
        module Top (
            mem: input  logic<2>,
            o  : output logic,
        ) {
            var x: logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return 0;
            }
            inst u: Sink (
                i: mem[touch(o)],
            );
            assign o = x;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_instance_output_selector_side_effect_is_recorded() {
    // Why this case exists: an output connection evaluates the selector in its
    // destination. The observer must retain touch(o)'s module-scope write even
    // though the child output value itself is constant.
    assert_comb_loop(
        "an instance output selector retains a called function global write",
        r#"
        module Source (
            o: output logic,
        ) {
            assign o = 0;
        }
        module Top (
            o: output logic,
        ) {
            var bus: logic<2>;
            var x  : logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return 0;
            }
            inst u: Source (
                o: bus[touch(o)],
            );
            assign o = x;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_instance_output_selector_without_a_return_path_is_feed_forward() {
    // The selector controls the output destination and its function writes x,
    // but neither dependency returns to the selector. Recording both effects
    // must not manufacture a cycle.
    assert_comb_loop(
        "an independent instance output selector remains feed-forward",
        r#"
        module Source (
            o: output logic,
        ) {
            assign o = 0;
        }
        module Top (
            index: input  logic,
            seed : input  logic,
            o    : output logic,
        ) {
            var bus: logic<2>;
            var x  : logic;
            function touch (
                a: input logic,
            ) -> logic {
                x = a;
                return index;
            }
            inst u: Source (
                o: bus[touch(seed)],
            );
            assign o = x;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_instance_shift_positions_an_instance_actual_left_shift_keeps_its_inserted_bit_loop_free()
 {
    assert_comb_loop(
        "an instance actual left shift keeps its inserted bit loop-free",
        r#"
        module Child (
            i: input  logic<4>,
            o: output logic<4>,
        ) {
            assign o = i;
        }
        module Top (
            o: output logic<4>,
        ) {
            var value: logic<4>;
            var passed: logic<4>;
            inst u: Child (
                i: value << 1,
                o: passed,
            );
            assign value[0] = 0;
            assign value[1] = passed[0];
            assign value[3:2] = 0;
            assign o = passed;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_instance_shift_positions_an_instance_actual_left_shift_detects_its_live_shifted_bit()
 {
    assert_comb_loop(
        "an instance actual left shift detects its live shifted bit",
        r#"
        module Child (
            i: input  logic<4>,
            o: output logic<4>,
        ) {
            assign o = i;
        }
        module Top (
            o: output logic<4>,
        ) {
            var value: logic<4>;
            var passed: logic<4>;
            inst u: Child (
                i: value << 1,
                o: passed,
            );
            assign value[0] = passed[1];
            assign value[3:1] = 0;
            assign o = passed;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_instance_repeat_positions_an_instance_repeat_actual_keeps_an_unrelated_operand_loop_free()
 {
    assert_comb_loop(
        "an instance repeat actual keeps an unrelated operand loop-free",
        r#"
        module Child (
            i: input  logic<3>,
            o: output logic,
        ) {
            assign o = i[2];
        }
        module Top (
            o: output logic,
        ) {
            var high: logic;
            var low: logic;
            var child_o: logic;
            inst u: Child (
                i: {high repeat 2, low},
                o: child_o,
            );
            assign high = 0;
            assign low = child_o;
            assign o = child_o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_instance_repeat_positions_an_instance_repeat_actual_detects_its_selected_repeated_operand()
 {
    assert_comb_loop(
        "an instance repeat actual detects its selected repeated operand",
        r#"
        module Child (
            i: input  logic<3>,
            o: output logic,
        ) {
            assign o = i[2];
        }
        module Top (
            o: output logic,
        ) {
            var high: logic;
            var low: logic;
            var child_o: logic;
            inst u: Child (
                i: {high repeat 2, low},
                o: child_o,
            );
            assign high = child_o;
            assign low = 0;
            assign o = child_o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_distinguishes_generic_module_specializations_an_enabled_generic_module_specialization_retains_its_feedthrough()
 {
    assert_comb_loop(
        "an enabled generic-module specialization retains its feedthrough",
        r#"
        module Child #(
            param ENABLE: u32 = 0,
        )(
            i: input  logic,
            o: output logic,
        ) {
            if ENABLE :g_enabled {
                assign o = i;
            } else {
                assign o = 0;
            }
        }
        module Top (
            o: output logic,
        ) {
            var feedback: logic;
            var passed: logic;
            inst u: Child #(
                ENABLE: 1,
            )(
                i: feedback,
                o: passed,
            );
            assign feedback = passed;
            assign o = feedback;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_distinguishes_generic_module_specializations_a_disabled_generic_module_specialization_does_not_inherit_feedthrough()
 {
    assert_comb_loop(
        "a disabled generic-module specialization does not inherit feedthrough",
        r#"
        module Child #(
            param ENABLE: u32 = 1,
        )(
            i: input  logic,
            o: output logic,
        ) {
            if ENABLE :g_enabled {
                assign o = i;
            } else {
                assign o = 0;
            }
        }
        module Top (
            o: output logic,
        ) {
            var feedback: logic;
            var passed: logic;
            inst u: Child #(
                ENABLE: 0,
            )(
                i: feedback,
                o: passed,
            );
            assign feedback = passed;
            assign o = feedback;
        }
        "#,
        false,
    );
}

fn instance_logical_actual_code(expression: &str) -> String {
    format!(
        r#"
                module Pass (
                    i: input  logic,
                    o: output logic,
                ) {{
                    assign o = i;
                }}
                module Top (
                    o: output logic,
                ) {{
                    var feedback: logic;
                    var passed: logic;
                    inst u: Pass (
                        i: {expression},
                        o: passed,
                    );
                    assign feedback = passed;
                    assign o = passed;
                }}
                "#
    )
}

#[test]
fn comb_loop_false_logical_and_instance_actual_drops_rhs() {
    assert_comb_loop(
        "a false logical-and instance actual drops its dead RHS",
        &instance_logical_actual_code("1'b0 && feedback"),
        false,
    );
}

#[test]
fn comb_loop_true_logical_or_instance_actual_drops_rhs() {
    assert_comb_loop(
        "a true logical-or instance actual drops its dead RHS",
        &instance_logical_actual_code("1'b1 || feedback"),
        false,
    );
}

#[test]
fn comb_loop_true_logical_and_instance_actual_retains_rhs() {
    assert_comb_loop(
        "a true logical-and instance actual retains its live RHS",
        &instance_logical_actual_code("1'b1 && feedback"),
        true,
    );
}

#[test]
fn comb_loop_false_logical_or_instance_actual_retains_rhs() {
    assert_comb_loop(
        "a false logical-or instance actual retains its live RHS",
        &instance_logical_actual_code("1'b0 || feedback"),
        true,
    );
}

#[test]
fn comb_loop_preserves_ternary_positions_across_boundaries_an_instance_ternary_actual_keeps_a_disjoint_bit_loop_free()
 {
    assert_comb_loop(
        "an instance ternary actual keeps a disjoint bit loop-free",
        r#"
        module Low (
            i: input  logic<2>,
            o: output logic,
        ) {
            assign o = i[0];
        }
        module Top (
            sel: input  logic,
            o  : output logic,
        ) {
            var value: logic<2>;
            var passed: logic;
            inst u: Low (
                i: if sel ? value : 0,
                o: passed,
            );
            assign value[0] = 0;
            assign value[1] = passed;
            assign o = passed;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_ternary_positions_across_boundaries_an_instance_ternary_actual_detects_its_corresponding_bit_loop()
 {
    assert_comb_loop(
        "an instance ternary actual detects its corresponding-bit loop",
        r#"
        module Low (
            i: input  logic<2>,
            o: output logic,
        ) {
            assign o = i[0];
        }
        module Top (
            sel: input  logic,
            o  : output logic,
        ) {
            var value: logic<2>;
            var passed: logic;
            inst u: Low (
                i: if sel ? value : 0,
                o: passed,
            );
            assign value[0] = passed;
            assign value[1] = 0;
            assign o = passed;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_preserves_unpacked_port_element_positions_an_unpacked_array_module_port_keeps_disjoint_elements_loop_free()
 {
    assert_comb_loop(
        "an unpacked-array module port keeps disjoint elements loop-free",
        r#"
        module Child (
            i: input  logic [2],
            o: output logic [2],
        ) {
            assign o[0] = i[0];
            assign o[1] = i[1];
        }
        module Top (
            o: output logic,
        ) {
            var child_i: logic [2];
            var child_o: logic [2];
            inst u: Child (
                i: child_i,
                o: child_o,
            );
            assign child_i[0] = child_o[1];
            assign child_i[1] = 0;
            assign o = child_o[0];
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_preserves_unpacked_port_element_positions_an_unpacked_array_module_port_detects_same_element_feedback()
 {
    assert_comb_loop(
        "an unpacked-array module port detects same-element feedback",
        r#"
        module Child (
            i: input  logic [2],
            o: output logic [2],
        ) {
            assign o[0] = i[0];
            assign o[1] = i[1];
        }
        module Top (
            o: output logic,
        ) {
            var child_i: logic [2];
            var child_o: logic [2];
            inst u: Child (
                i: child_i,
                o: child_o,
            );
            assign child_i[0] = child_o[0];
            assign child_i[1] = 0;
            assign o = child_o[0];
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_a_child_port_summary_must_not_turn_bit_disjoint_feedthrough_into_a_loop()
 {
    assert_comb_loop(
        "a child port summary must not turn bit-disjoint feedthrough into a loop",
        r#"
        module Child (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            assign o[0] = i[1];
            assign o[1] = 0;
        }

        module Top (
            o: output logic<2>,
        ) {
            var child_i: logic<2>;
            var child_o: logic<2>;
            inst u: Child (
                i: child_i,
                o: child_o,
            );
            assign child_i[0] = child_o[0];
            assign child_i[1] = 0;
            assign o = child_o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_a_region_preserving_child_feedthrough_still_reports_a_real_loop()
 {
    assert_comb_loop(
        "a region-preserving child feedthrough still reports a real loop",
        r#"
        module Child (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            assign o[0] = i[0];
            assign o[1] = 0;
        }

        module Top (
            o: output logic<2>,
        ) {
            var child_i: logic<2>;
            var child_o: logic<2>;
            inst u: Child (
                i: child_i,
                o: child_o,
            );
            assign child_i[0] = child_o[0];
            assign child_i[1] = 0;
            assign o = child_o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_an_opaque_systemverilog_component_cannot_prove_a_hard_loop()
 {
    assert_comb_loop(
        "an opaque SystemVerilog component cannot prove a hard loop",
        r#"
        module Top (
            o: output logic,
        ) {
            var into_sv : logic;
            var from_sv : logic;
            inst u: $sv::Ext (
                i_data: into_sv,
                o_data: from_sv,
            );
            assign into_sv = from_sv;
            assign o = from_sv;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_a_top_input_to_output_path_has_no_inferred_environment_return_edge()
 {
    assert_comb_loop(
        "a top input-to-output path has no inferred environment return edge",
        r#"
        module Top (
            i: input  logic,
            o: output logic,
        ) {
            assign o = i;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_bit_precision_survives_two_module_boundaries() {
    assert_comb_loop(
        "bit precision survives two module boundaries",
        r#"
        module Leaf (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            assign o[0] = i[1];
            assign o[1] = 0;
        }

        module Middle (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            inst u_leaf: Leaf (
                i: i,
                o: o,
            );
        }

        module Top (
            o: output logic<2>,
        ) {
            var middle_i: logic<2>;
            var middle_o: logic<2>;
            inst u_middle: Middle (
                i: middle_i,
                o: middle_o,
            );
            assign middle_i[0] = middle_o[0];
            assign middle_i[1] = 0;
            assign o = middle_o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_a_real_loop_survives_two_region_preserving_summaries() {
    assert_comb_loop(
        "a real loop survives two region-preserving summaries",
        r#"
        module Leaf (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            assign o[0] = i[0];
            assign o[1] = 0;
        }

        module Middle (
            i: input  logic<2>,
            o: output logic<2>,
        ) {
            inst u_leaf: Leaf (
                i: i,
                o: o,
            );
        }

        module Top (
            o: output logic<2>,
        ) {
            var middle_i: logic<2>;
            var middle_o: logic<2>;
            inst u_middle: Middle (
                i: middle_i,
                o: middle_o,
            );
            assign middle_i[0] = middle_o[0];
            assign middle_i[1] = 0;
            assign o = middle_o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_a_concatenated_instance_input_preserves_its_low_bit_source()
 {
    assert_comb_loop(
        "a concatenated instance input preserves its low-bit source",
        r#"
        module Child (
            i: input  logic<2>,
            o: output logic,
        ) {
            assign o = i[0];
        }

        module Top (
            o: output logic,
        ) {
            var high    : logic;
            var low     : logic;
            var child_o : logic;
            inst u: Child (
                i: {high, low},
                o: child_o,
            );
            assign high = child_o;
            assign low = 0;
            assign o = child_o;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_a_concatenated_instance_input_does_not_hide_a_real_low_bit_loop()
 {
    assert_comb_loop(
        "a concatenated instance input does not hide a real low-bit loop",
        r#"
        module Child (
            i: input  logic<2>,
            o: output logic,
        ) {
            assign o = i[0];
        }

        module Top (
            o: output logic,
        ) {
            var high    : logic;
            var low     : logic;
            var child_o : logic;
            inst u: Child (
                i: {high, low},
                o: child_o,
            );
            assign high = 0;
            assign low = child_o;
            assign o = child_o;
        }
        "#,
        true,
    );
}

#[test]
fn comb_loop_module_boundary_region_mapping_a_static_slice_connection_does_not_contaminate_its_sibling_bit()
 {
    assert_comb_loop(
        "a static slice connection does not contaminate its sibling bit",
        r#"
        module Child (
            i: input  logic,
            o: output logic,
        ) {
            assign o = i;
        }

        module Top (
            o: output logic<2>,
        ) {
            var bus: logic<2>;
            inst u: Child (
                i: bus[1],
                o: bus[0],
            );
            assign bus[1] = 0;
            assign o = bus;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_instance_summary_region_mapping_is_reused() {
    // Why this case exists: every child output depends on every child input,
    // so its summary contains a Cartesian product with the same input and
    // output regions repeated many times. Mapping those regions into the
    // parent's actuals must be proportional to the distinct regions, while
    // the exact all-to-all dependencies still retain the feedback below.
    const WIDTH: usize = 32;
    let reduction = (0..WIDTH)
        .map(|index| format!("x[{index}]"))
        .collect::<Vec<_>>()
        .join(" ^ ");
    let outputs = (0..WIDTH)
        .map(|index| format!("assign o[{index}] = mix(i);"))
        .collect::<Vec<_>>()
        .join("\n");
    let clears = (1..WIDTH)
        .map(|index| format!("assign feedback[{index}] = 0;"))
        .collect::<Vec<_>>()
        .join("\n");
    crate::comb_loop_detect::reset_instance_request_edge_probes();
    assert_comb_loop(
        "an instance summary Cartesian product retains parent feedback",
        &format!(
            r#"
            module Child (
                i: input  logic<{WIDTH}>,
                o: output logic<{WIDTH}>,
            ) {{
                function mix (
                    x: input logic<{WIDTH}>,
                ) -> logic {{
                    return {reduction};
                }}
                {outputs}
            }}

            module Top (
                o: output logic<{WIDTH}>,
            ) {{
                var feedback: logic<{WIDTH}>;
                var passed  : logic<{WIDTH}>;
                inst u: Child (
                    i: feedback,
                    o: passed,
                );
                assign feedback[0] = passed[0];
                {clears}
                assign o = passed;
            }}
            "#
        ),
        true,
    );
    assert!(
        crate::comb_loop_detect::instance_request_edge_probes() <= WIDTH * WIDTH * 3,
        "request discovery must scan summary edges a constant number of times",
    );
}

#[test]
fn instance_actual_regions_share_source_summary_walks() {
    const WIDTH: usize = 128;
    let child_outputs = (0..WIDTH)
        .map(|bit| format!("assign o[{bit}] = i[{bit}];"))
        .collect::<Vec<_>>()
        .join("\n");
    let clears = (1..WIDTH)
        .map(|bit| format!("assign feedback[{bit}] = 0;"))
        .collect::<Vec<_>>()
        .join("\n");
    crate::comb_loop_detect::reset_source_summary_state_visits();
    assert_comb_loop(
        "many requested regions reuse shared SSA source summaries",
        &format!(
            r#"
            module Child (
                i: input logic<{WIDTH}>,
                o: output logic<{WIDTH}>,
            ) {{
                {child_outputs}
            }}
            module Top (
                independent: input  logic<{WIDTH}>,
                o          : output logic<{WIDTH}>,
            ) {{
                var feedback: logic<{WIDTH}>;
                var passed  : logic<{WIDTH}>;
                inst child: Child (
                    i: feedback + independent,
                    o: passed,
                );
                assign feedback[0] = passed[0];
                {clears}
                assign o = passed;
            }}
            "#
        ),
        true,
    );
    assert!(
        crate::comb_loop_detect::source_summary_state_visits() <= WIDTH * 20,
        "region queries must share walks of the same SSA versions",
    );
}

#[test]
fn comb_loop_module_formal_high_bit_ignores_short_unsigned_actual() {
    assert_comb_loop(
        "a module formal high bit does not read an unsigned short actual",
        r#"
        module High (i: input logic<4>, o: output logic) { assign o = i[3]; }
        module Top (o: output logic) {
            var value: logic<2>;
            inst u: High (i: value, o: o);
            assign value[0] = o;
            assign value[1] = 0;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_unaligned_unpacked_instance_element_zero_is_disjoint() {
    assert_unaligned_unpacked_instance_input(0, false);
}

#[test]
fn comb_loop_unaligned_unpacked_instance_element_one_retains_feedback() {
    assert_unaligned_unpacked_instance_input(1, true);
}

#[test]
fn many_comb_declarations_build_the_module_context_once() {
    const COUNT: usize = 256;
    let variables = (0..COUNT)
        .map(|index| format!("var value_{index}: logic;"))
        .collect::<Vec<_>>()
        .join("\n");
    let assignments = (0..COUNT)
        .map(|index| format!("assign value_{index} = 0;"))
        .collect::<Vec<_>>()
        .join("\n");
    crate::comb_loop_detect::reset_module_context_entries();
    assert_comb_loop(
        "independent declarations reuse immutable module metadata",
        &format!(
            r#"
            module Top (o: output logic) {{
                {variables}
                {assignments}
                assign o = value_0;
            }}
            "#,
        ),
        false,
    );
    assert!(
        crate::comb_loop_detect::module_context_entries() <= COUNT + 4,
        "module variable/function maps must not be cloned per declaration",
    );
}

#[test]
fn comb_loop_module_summary_preserves_if_expression_arm_exclusivity() {
    assert_comb_loop(
        "a child summary must not combine mutually exclusive expression arms",
        r#"
        module Conditional (
            i  : input  logic<2>,
            sel: input  logic,
            o  : output logic<2>,
        ) {
            assign o = if sel ? {i[0], 1'b0} : {1'b0, i[1]};
        }
        module Top (
            sel: input  logic,
            o  : output logic,
        ) {
            var state: logic<2>;
            inst conditional: Conditional (
                i  : state,
                sel: sel,
                o  : state,
            );
            assign o = |state;
        }
        "#,
        false,
    );
}

#[test]
fn comb_loop_module_summary_retains_feedback_reachable_in_one_expression_arm() {
    assert_comb_loop(
        "a child summary retains feedback reachable in one expression arm",
        r#"
        module Conditional (
            i  : input  logic,
            sel: input  logic,
            o  : output logic,
        ) {
            assign o = if sel ? i : 1'b0;
        }
        module Top (
            sel: input  logic,
            o  : output logic,
        ) {
            var state: logic;
            inst conditional: Conditional (
                i  : state,
                sel: sel,
                o  : state,
            );
            assign o = state;
        }
        "#,
        true,
    );
}

fn shifted_recurrence_module_code(feedback_output: usize, feedback_input: usize) -> String {
    let clears = (0..4)
        .filter(|index| *index != feedback_input)
        .map(|index| format!("assign child_i[{index}] = 0;"))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        r#"
        module ShiftClosure (
            i: input  logic<4>,
            o: output logic<4>,
        ) {{
            var x: logic<4>;
            assign x = (x << 1) | i;
            assign o = x;
        }}
        module Top (o: output logic) {{
            var child_i: logic<4>;
            var child_o: logic<4>;
            inst u: ShiftClosure (i: child_i, o: child_o);
            assign child_i[{feedback_input}] = child_o[{feedback_output}];
            {clears}
            assign o = child_o[0];
        }}
        "#,
    )
}

#[test]
fn comb_loop_module_summary_shift_closure_terminates_without_wraparound() {
    assert_comb_loop(
        "a truncated left-shift recurrence does not wrap its high input to its low output",
        &shifted_recurrence_module_code(0, 3),
        false,
    );
}

#[test]
fn comb_loop_module_summary_shift_closure_retains_reachable_feedback() {
    assert_comb_loop(
        "a left-shift recurrence retains transitive low-to-high feedthrough",
        &shifted_recurrence_module_code(3, 0),
        true,
    );
}

#[test]
fn comb_loop_wide_module_summary_shift_closure_is_sparse() {
    assert_comb_loop(
        "a wide truncated-shift recurrence must not enumerate its declared width",
        r#"
        module ShiftClosure (
            i: input  logic<1000000>,
            o: output logic<1000000>,
        ) {
            var x: logic<1000000>;
            assign x = (x << 1) | i;
            assign o = x;
        }
        module Top (o: output logic) {
            var child_o: logic<1000000>;
            inst u: ShiftClosure (i: 0, o: child_o);
            assign o = child_o[0];
        }
        "#,
        false,
    );
}
