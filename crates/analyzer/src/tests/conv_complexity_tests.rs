use super::*;
use std::sync::Arc;

const ITEM_COUNT: usize = 32;

fn convert(code: &str) -> Ir {
    symbol_table::clear();
    attribute_table::clear();
    doc_comment_table::clear();

    let metadata = Metadata::create_default("prj").unwrap();
    let parser = Parser::parse(code, &"").unwrap();
    let analyzer = Analyzer::new(&metadata);
    let mut context = Context::default();
    let mut ir = Ir::default();
    let _ = analyzer.analyze_pass1("prj", &parser.veryl);
    let _ = Analyzer::analyze_post_pass1();
    let _ = analyzer.analyze_pass2(&parser.veryl, &mut context, Some(&mut ir));
    ir
}

#[test]
fn receiver_method_import_work_is_linear() {
    let fields = (0..ITEM_COUNT)
        .map(|i| format!("var field_{i}: logic;"))
        .collect::<Vec<_>>()
        .join("\n");
    let methods = (0..ITEM_COUNT)
        .map(|i| format!("function method_{i} () -> logic {{\n    return field_{i};\n}}"))
        .collect::<Vec<_>>()
        .join("\n");
    let sinks = (0..ITEM_COUNT)
        .map(|i| format!("var sink_{i}: logic;"))
        .collect::<Vec<_>>()
        .join("\n");
    let calls = (0..ITEM_COUNT)
        .map(|i| format!("assign sink_{i} = bus[0].method_{i}();"))
        .collect::<Vec<_>>()
        .join("\n");
    let code = format!(
        r#"
        interface Bus {{
            {fields}
            {methods}
        }}
        module Top {{
            inst bus: Bus[2];
            {sinks}
            {calls}
        }}
        "#
    );

    Context::reset_receiver_path_prefix_comparisons();
    let ir = convert(&code);
    let comparisons = Context::receiver_path_prefix_comparisons();
    assert!(
        comparisons <= ITEM_COUNT * 8,
        "receiver path work grew non-linearly: {comparisons} prefix comparisons for {ITEM_COUNT} methods"
    );

    let top = ir
        .components
        .iter()
        .find_map(|component| match component {
            crate::ir::Component::Module(module) if module.name.to_string() == "Top" => {
                Some(module)
            }
            _ => None,
        })
        .expect("Top module");
    assert_eq!(top.functions.len(), ITEM_COUNT);
    let mut functions = top.functions.values();
    let first = functions.next().expect("receiver method");
    assert_eq!(first.receiver_variables.len(), ITEM_COUNT);
    assert_eq!(first.receiver_prefixes.len(), 1);
    for function in functions {
        assert_eq!(function.receiver_variables.len(), ITEM_COUNT);
        assert_eq!(function.receiver_prefixes.len(), 1);
        assert!(Arc::ptr_eq(
            &first.receiver_variables,
            &function.receiver_variables
        ));
    }
}

#[test]
fn modport_instance_binding_work_is_linear() {
    let child_ports = (0..ITEM_COUNT)
        .map(|i| format!("lane_{i}: modport Lane::sink"))
        .collect::<Vec<_>>()
        .join(",\n");
    let interfaces = (0..ITEM_COUNT)
        .map(|i| format!("inst lane_{i}: Lane;"))
        .collect::<Vec<_>>()
        .join("\n");
    let connects = (0..ITEM_COUNT)
        .map(|i| format!("lane_{i}: lane_{i}"))
        .collect::<Vec<_>>()
        .join(",\n");
    let code = format!(
        r#"
        interface Lane {{
            var value: logic;
            modport sink {{
                value: input,
            }}
        }}
        module Child (
            {child_ports},
        ) {{}}
        module Top {{
            {interfaces}
            inst child: Child (
                {connects},
            );
        }}
        "#
    );

    Context::reset_interface_binding_prefix_comparisons();
    let _errors = analyze(&code);
    let comparisons = Context::interface_binding_prefix_comparisons();
    assert!(
        comparisons <= ITEM_COUNT * 12,
        "modport binding work grew non-linearly: {comparisons} prefix comparisons for {ITEM_COUNT} ports"
    );
}

#[test]
fn collecting_non_modport_ports_does_not_compare_every_path_to_every_port() {
    let ports = (0..ITEM_COUNT)
        .map(|i| format!("port_{i}: input logic"))
        .collect::<Vec<_>>()
        .join(",\n");
    let code = format!(
        r#"
        module Top (
            {ports},
        ) {{}}
        "#
    );

    crate::conv::ir::reset_interface_member_port_candidates();
    let ir = convert(&code);
    let candidates = crate::conv::ir::interface_member_port_candidates();
    assert_eq!(
        candidates, ITEM_COUNT,
        "interface-member collection examined {candidates} port candidates for {ITEM_COUNT} ordinary ports"
    );

    let top = ir
        .components
        .iter()
        .find_map(|component| match component {
            crate::ir::Component::Module(module) if module.name.to_string() == "Top" => {
                Some(module)
            }
            _ => None,
        })
        .expect("Top module");
    assert_eq!(top.port_types.len(), ITEM_COUNT);
    assert!(top.interface_members.is_empty());
}
