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
