#[test]
fn tests() {
    let test_cases = trybuild::TestCases::new();
    test_cases.pass("tests/01-parse.rs");
    test_cases.pass("tests/02-contract-impl.rs");
    test_cases.pass("tests/03-create-caller.rs");
    test_cases.pass("tests/04-entry-points.rs");
    test_cases.pass("tests/05-caller-impl-interface.rs");
    test_cases.pass("tests/06-contract-test-interface.rs");
}
