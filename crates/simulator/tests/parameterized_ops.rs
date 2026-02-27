use test_case::test_case;
use veryl_simulator::{BigUint, Simulator};

// ---------------------------------------------------------------------------
// Helper: combinational binary operator  (assign o = a {op} b)
// ---------------------------------------------------------------------------
fn check_comb_binary(op: &str, in_type: &str, out_type: &str, a: u64, b: u64, expected: u64) {
    let code = format!(
        r#"
        module Top (a: input {in_type}, b: input {in_type}, o: output {out_type}) {{
            assign o = a {op} b;
        }}
    "#
    );
    let mut sim = Simulator::builder(&code, "Top").build().unwrap();
    let sig_a = sim.signal("a");
    let sig_b = sim.signal("b");
    let sig_o = sim.signal("o");

    sim.modify(|io| {
        io.set_wide(sig_a, BigUint::from(a));
        io.set_wide(sig_b, BigUint::from(b));
    })
    .unwrap();

    assert_eq!(
        sim.get(sig_o),
        BigUint::from(expected),
        "comb {op}: {a} {op} {b} — expected {expected}"
    );
}

// ---------------------------------------------------------------------------
// Helper: ff binary operator  (always_ff { r = a {op} b; })
// ---------------------------------------------------------------------------
fn check_ff_binary(op: &str, in_type: &str, out_type: &str, a: u64, b: u64, expected: u64) {
    let code = format!(
        r#"
        module Top (clk: input clock, a: input {in_type}, b: input {in_type}, o: output {out_type}) {{
            var r: {out_type};
            always_ff (clk) {{
                r = a {op} b;
            }}
            assign o = r;
        }}
    "#
    );
    let mut sim = Simulator::builder(&code, "Top").build().unwrap();
    let clk = sim.event("clk");
    let sig_a = sim.signal("a");
    let sig_b = sim.signal("b");
    let sig_o = sim.signal("o");

    sim.modify(|io| {
        io.set_wide(sig_a, BigUint::from(a));
        io.set_wide(sig_b, BigUint::from(b));
    })
    .unwrap();
    sim.tick(clk).unwrap();

    assert_eq!(
        sim.get(sig_o),
        BigUint::from(expected),
        "ff {op}: {a} {op} {b} — expected {expected}"
    );
}

// ---------------------------------------------------------------------------
// Helper: combinational unary operator  (assign o = {op}a)
// ---------------------------------------------------------------------------
fn check_comb_unary(op: &str, in_type: &str, out_type: &str, a: u64, expected: u64) {
    let code = format!(
        r#"
        module Top (a: input {in_type}, o: output {out_type}) {{
            assign o = {op}a;
        }}
    "#
    );
    let mut sim = Simulator::builder(&code, "Top").build().unwrap();
    let sig_a = sim.signal("a");
    let sig_o = sim.signal("o");

    sim.modify(|io| io.set_wide(sig_a, BigUint::from(a)))
        .unwrap();

    assert_eq!(
        sim.get(sig_o),
        BigUint::from(expected),
        "comb unary {op}: {op}{a} — expected {expected}"
    );
}

// ---------------------------------------------------------------------------
// Helper: ff unary operator  (always_ff { r = {op}a; })
// ---------------------------------------------------------------------------
fn check_ff_unary(op: &str, in_type: &str, out_type: &str, a: u64, expected: u64) {
    let code = format!(
        r#"
        module Top (clk: input clock, a: input {in_type}, o: output {out_type}) {{
            var r: {out_type};
            always_ff (clk) {{
                r = {op}a;
            }}
            assign o = r;
        }}
    "#
    );
    let mut sim = Simulator::builder(&code, "Top").build().unwrap();
    let clk = sim.event("clk");
    let sig_a = sim.signal("a");
    let sig_o = sim.signal("o");

    sim.modify(|io| io.set_wide(sig_a, BigUint::from(a)))
        .unwrap();
    sim.tick(clk).unwrap();

    assert_eq!(
        sim.get(sig_o),
        BigUint::from(expected),
        "ff unary {op}: {op}{a} — expected {expected}"
    );
}

// ===================================================================
// Arithmetic (unsigned) — comb
// ===================================================================

#[test_case("+",  "logic<8>", "logic<8>", 100, 55, 155  ; "add basic")]
#[test_case("+",  "logic<8>", "logic<8>", 200, 100, 44  ; "add overflow wraps")]
#[test_case("+",  "logic<8>", "logic<8>", 0, 0, 0       ; "add zeros")]
#[test_case("-",  "logic<8>", "logic<8>", 200, 55, 145  ; "sub basic")]
#[test_case("-",  "logic<8>", "logic<8>", 5, 10, 251    ; "sub underflow wraps")]
#[test_case("-",  "logic<8>", "logic<8>", 0, 0, 0       ; "sub zeros")]
#[test_case("*",  "logic<8>", "logic<8>", 7, 6, 42      ; "mul basic")]
#[test_case("*",  "logic<8>", "logic<8>", 16, 16, 0     ; "mul overflow wraps")]
#[test_case("*",  "logic<8>", "logic<8>", 255, 1, 255   ; "mul identity")]
#[test_case("/",  "logic<16>", "logic<16>", 100, 7, 14  ; "div basic")]
#[test_case("/",  "logic<16>", "logic<16>", 255, 16, 15 ; "div truncates")]
#[test_case("/",  "logic<16>", "logic<16>", 0, 5, 0     ; "div zero dividend")]
#[test_case("%",  "logic<16>", "logic<16>", 100, 7, 2   ; "rem basic")]
#[test_case("%",  "logic<16>", "logic<16>", 255, 16, 15 ; "rem basic 2")]
#[test_case("%",  "logic<16>", "logic<16>", 42, 5, 2    ; "rem small")]
fn comb_arith_unsigned(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_comb_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Arithmetic (unsigned) — ff (representative subset)
// ===================================================================

#[test_case("+",  "logic<8>", "logic<8>", 100, 55, 155  ; "ff add")]
#[test_case("-",  "logic<8>", "logic<8>", 200, 55, 145  ; "ff sub")]
#[test_case("*",  "logic<8>", "logic<8>", 7, 6, 42      ; "ff mul")]
#[test_case("/",  "logic<16>", "logic<16>", 100, 7, 14  ; "ff div")]
#[test_case("%",  "logic<16>", "logic<16>", 100, 7, 2   ; "ff rem")]
fn ff_arith_unsigned(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_ff_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Bitwise — comb
// ===================================================================

#[test_case("&",  "logic<8>", "logic<8>", 0xA5, 0x5A, 0x00  ; "and complementary")]
#[test_case("&",  "logic<8>", "logic<8>", 0xFF, 0xA5, 0xA5  ; "and with all ones")]
#[test_case("|",  "logic<8>", "logic<8>", 0xA5, 0x5A, 0xFF  ; "or complementary")]
#[test_case("|",  "logic<8>", "logic<8>", 0x00, 0xA5, 0xA5  ; "or with zero")]
#[test_case("^",  "logic<8>", "logic<8>", 0xA5, 0x5A, 0xFF  ; "xor complementary")]
#[test_case("^",  "logic<8>", "logic<8>", 0xFF, 0xFF, 0x00  ; "xor same cancels")]
#[test_case("~^", "logic<8>", "logic<8>", 0xF0, 0xFF, 0xF0  ; "xnor basic")]
#[test_case("~^", "logic<8>", "logic<8>", 0xAA, 0x55, 0x00  ; "xnor complementary")]
fn comb_bitwise(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_comb_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Bitwise — ff (representative)
// ===================================================================

#[test_case("&",  "logic<8>", "logic<8>", 0xFF, 0xA5, 0xA5  ; "ff and")]
#[test_case("|",  "logic<8>", "logic<8>", 0xA5, 0x5A, 0xFF  ; "ff or")]
#[test_case("^",  "logic<8>", "logic<8>", 0xA5, 0x5A, 0xFF  ; "ff xor")]
#[test_case("~^", "logic<8>", "logic<8>", 0xF0, 0xFF, 0xF0  ; "ff xnor")]
fn ff_bitwise(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_ff_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Shift — comb (unsigned)
// ===================================================================

#[test_case("<<",  "logic<8>", "logic<8>", 0x01, 4, 0x10   ; "shl basic")]
#[test_case("<<",  "logic<8>", "logic<8>", 0x80, 1, 0x00   ; "shl overflow")]
#[test_case(">>",  "logic<8>", "logic<8>", 0x80, 2, 0x20   ; "shr basic")]
#[test_case(">>",  "logic<8>", "logic<8>", 0x01, 1, 0x00   ; "shr underflow")]
#[test_case(">>>", "logic<8>", "logic<8>", 0x80, 2, 0x20   ; "sar unsigned same as shr")]
fn comb_shift_unsigned(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_comb_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Shift — comb (signed arithmetic right shift)
// ===================================================================

#[test_case(">>>", "i8", "i8", 0x80, 2, 0xE0 ; "sar negative sign extends")]
#[test_case(">>>", "i8", "i8", 0x40, 2, 0x10 ; "sar positive no extend")]
#[test_case(">>>", "i8", "i8", 0xFF, 4, 0xFF ; "sar all ones stays")]
fn comb_shift_signed(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_comb_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Shift — ff (representative)
// ===================================================================

#[test_case("<<",  "logic<8>", "logic<8>", 0x01, 4, 0x10   ; "ff shl")]
#[test_case(">>",  "logic<8>", "logic<8>", 0x80, 2, 0x20   ; "ff shr")]
#[test_case(">>>", "i8", "i8", 0x80, 2, 0xE0               ; "ff sar signed")]
fn ff_shift(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_ff_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Comparison (unsigned) — comb
// ===================================================================

#[test_case("<:",  "logic<8>", "logic", 10, 20, 1  ; "lt true")]
#[test_case("<:",  "logic<8>", "logic", 20, 10, 0  ; "lt false")]
#[test_case("<:",  "logic<8>", "logic", 10, 10, 0  ; "lt equal")]
#[test_case("<=",  "logic<8>", "logic", 10, 20, 1  ; "le true")]
#[test_case("<=",  "logic<8>", "logic", 10, 10, 1  ; "le equal")]
#[test_case("<=",  "logic<8>", "logic", 20, 10, 0  ; "le false")]
#[test_case(">:",  "logic<8>", "logic", 20, 10, 1  ; "gt true")]
#[test_case(">:",  "logic<8>", "logic", 10, 20, 0  ; "gt false")]
#[test_case(">:",  "logic<8>", "logic", 10, 10, 0  ; "gt equal")]
#[test_case(">=",  "logic<8>", "logic", 20, 10, 1  ; "ge true")]
#[test_case(">=",  "logic<8>", "logic", 10, 10, 1  ; "ge equal")]
#[test_case("==",  "logic<8>", "logic", 42, 42, 1  ; "eq true")]
#[test_case("==",  "logic<8>", "logic", 42, 43, 0  ; "eq false")]
#[test_case("!=",  "logic<8>", "logic", 42, 43, 1  ; "ne true")]
#[test_case("!=",  "logic<8>", "logic", 42, 42, 0  ; "ne false")]
fn comb_compare_unsigned(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_comb_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Comparison (signed) — comb
// ===================================================================

#[test_case("<:",  "i8", "logic", 0xFB, 0x02, 1  ; "signed lt neg vs pos")]
#[test_case("<:",  "i8", "logic", 0x02, 0xFB, 0  ; "signed lt pos vs neg")]
#[test_case(">:",  "i8", "logic", 0x02, 0xFB, 1  ; "signed gt pos vs neg")]
#[test_case(">=",  "i8", "logic", 0xFB, 0xFB, 1  ; "signed ge equal neg")]
#[test_case("==",  "i8", "logic", 0xFF, 0xFF, 1  ; "signed eq neg ones")]
#[test_case("!=",  "i8", "logic", 0xFF, 0x01, 1  ; "signed ne neg vs pos")]
fn comb_compare_signed(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_comb_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Logical — comb
// ===================================================================

#[test_case("&&", "logic<8>", "logic", 0x55, 0x00, 0  ; "and true false")]
#[test_case("&&", "logic<8>", "logic", 0x55, 0xAA, 1  ; "and true true")]
#[test_case("&&", "logic<8>", "logic", 0x00, 0x00, 0  ; "and false false")]
#[test_case("||", "logic<8>", "logic", 0x55, 0x00, 1  ; "or true false")]
#[test_case("||", "logic<8>", "logic", 0x00, 0x00, 0  ; "or false false")]
#[test_case("||", "logic<8>", "logic", 0x01, 0x01, 1  ; "or true true")]
fn comb_logical(op: &str, in_ty: &str, out_ty: &str, a: u64, b: u64, exp: u64) {
    check_comb_binary(op, in_ty, out_ty, a, b, exp);
}

// ===================================================================
// Unary — comb
// ===================================================================

#[test_case("~", "logic<8>", "logic<8>", 0x55, 0xAA ; "bitnot basic")]
#[test_case("~", "logic<8>", "logic<8>", 0x00, 0xFF ; "bitnot zeros")]
#[test_case("~", "logic<8>", "logic<8>", 0xFF, 0x00 ; "bitnot ones")]
#[test_case("!", "logic<8>", "logic",    0x55, 0    ; "lognot nonzero")]
#[test_case("!", "logic<8>", "logic",    0x00, 1    ; "lognot zero")]
#[test_case("+", "logic<8>", "logic<8>", 0xA5, 0xA5 ; "unary plus passthrough")]
fn comb_unary(op: &str, in_ty: &str, out_ty: &str, a: u64, exp: u64) {
    check_comb_unary(op, in_ty, out_ty, a, exp);
}

// ===================================================================
// Unary — ff (representative)
// ===================================================================

#[test_case("~", "logic<8>", "logic<8>", 0x55, 0xAA ; "ff bitnot")]
#[test_case("!", "logic<8>", "logic",    0x55, 0    ; "ff lognot nonzero")]
#[test_case("!", "logic<8>", "logic",    0x00, 1    ; "ff lognot zero")]
#[test_case("+", "logic<8>", "logic<8>", 0xA5, 0xA5 ; "ff unary plus")]
fn ff_unary(op: &str, in_ty: &str, out_ty: &str, a: u64, exp: u64) {
    check_ff_unary(op, in_ty, out_ty, a, exp);
}

// ===================================================================
// Reduction — comb
// ===================================================================

#[test_case("&",  "logic<8>", "logic", 0xFF, 1 ; "red and all ones")]
#[test_case("&",  "logic<8>", "logic", 0xFE, 0 ; "red and not all ones")]
#[test_case("&",  "logic<4>", "logic", 0x0F, 1 ; "red and 4bit all ones")]
#[test_case("|",  "logic<8>", "logic", 0x00, 0 ; "red or all zeros")]
#[test_case("|",  "logic<8>", "logic", 0x01, 1 ; "red or one bit")]
#[test_case("^",  "logic<8>", "logic", 0x01, 1 ; "red xor odd parity")]
#[test_case("^",  "logic<8>", "logic", 0x03, 0 ; "red xor even parity")]
#[test_case("~&", "logic<8>", "logic", 0xFF, 0 ; "red nand all ones")]
#[test_case("~&", "logic<8>", "logic", 0xFE, 1 ; "red nand not all ones")]
#[test_case("~|", "logic<8>", "logic", 0x00, 1 ; "red nor all zeros")]
#[test_case("~|", "logic<8>", "logic", 0x01, 0 ; "red nor has bit")]
#[test_case("~^", "logic<8>", "logic", 0x00, 1 ; "red xnor even zero")]
#[test_case("~^", "logic<8>", "logic", 0x01, 0 ; "red xnor odd one")]
#[test_case("~^", "logic<8>", "logic", 0x03, 1 ; "red xnor even two")]
fn comb_reduction(op: &str, in_ty: &str, out_ty: &str, a: u64, exp: u64) {
    check_comb_unary(op, in_ty, out_ty, a, exp);
}

// ===================================================================
// Reduction — ff (representative)
// ===================================================================

#[test_case("&",  "logic<8>", "logic", 0xFF, 1 ; "ff red and all ones")]
#[test_case("&",  "logic<8>", "logic", 0xFE, 0 ; "ff red and not all ones")]
#[test_case("|",  "logic<8>", "logic", 0x00, 0 ; "ff red or zeros")]
#[test_case("~&", "logic<8>", "logic", 0xFF, 0 ; "ff red nand all ones")]
#[test_case("~|", "logic<8>", "logic", 0x00, 1 ; "ff red nor zeros")]
#[test_case("~^", "logic<8>", "logic", 0x03, 1 ; "ff red xnor even")]
fn ff_reduction(op: &str, in_ty: &str, out_ty: &str, a: u64, exp: u64) {
    check_ff_unary(op, in_ty, out_ty, a, exp);
}
