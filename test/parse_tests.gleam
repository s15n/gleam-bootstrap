import gleeunit/should

import gleam/iterator

import ast.{SrcSpan}
import parse
import parse/error.{LexicalError, ParseError}
import parse/lexer
import parse/token

fn should_err(src: String, error) {
  let assert Error(result) = parse.parse_statement_sequence(src)
  result
  |> should.equal(error)
}

fn should_any_err(src: String) {
  let result = parse.parse_statement_sequence(src)
  result
  |> should.be_error
}

fn should_parse(src: String) {
  let result = parse.parse_statement_sequence(src)
  result
  |> should.be_ok
}

fn should_parse_module(src: String) {
  let result = parse.parse_module(src)
  result
  |> should.be_ok
}

fn should_module_err(src: String) {
  let result = parse.parse_module(src)
  result
  |> should.be_error
}

// TODO: https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/parse/tests.rs

pub fn ints_test() {
  // bad binary digit
  "0b012"
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.DigitOutOfRadix,
      location: SrcSpan(start: 4, end: 4),
    )),
    location: SrcSpan(start: 4, end: 4),
  ))
  // bad octal digit
  "0o12345678"
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.DigitOutOfRadix,
      location: SrcSpan(start: 9, end: 9),
    )),
    location: SrcSpan(start: 9, end: 9),
  ))
  // no int value
  "0x"
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.RadixIntNoValue,
      location: SrcSpan(start: 1, end: 1),
    )),
    location: SrcSpan(start: 1, end: 1),
  ))
  // trailing underscore
  "1_000_"
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.NumTrailingUnderscore,
      location: SrcSpan(start: 5, end: 5),
    )),
    location: SrcSpan(start: 5, end: 5),
  ))
}

pub fn string_bad_character_escape_test() {
  "\"\\g\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.BadStringEscape,
      location: SrcSpan(start: 1, end: 2),
    )),
    location: SrcSpan(start: 1, end: 2),
  ))
}

pub fn string_bad_character_escape_leading_backslash_test() {
  "\"\\\\\\g\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.BadStringEscape,
      location: SrcSpan(start: 3, end: 4),
    )),
    location: SrcSpan(start: 3, end: 4),
  ))
}

pub fn string_freestanding_unicode_escape_sequence_test() {
  "\"\\u\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.InvalidUnicodeEscape(error.MissingOpeningBrace),
      location: SrcSpan(start: 2, end: 3),
    )),
    location: SrcSpan(start: 2, end: 3),
  ))
}

pub fn string_unicode_escape_sequence_no_braces_test() {
  "\"\\u65\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.InvalidUnicodeEscape(error.MissingOpeningBrace),
      location: SrcSpan(start: 2, end: 3),
    )),
    location: SrcSpan(start: 2, end: 3),
  ))
}

pub fn string_unicode_escape_sequence_invalid_hex_test() {
  "\"\\u{z}\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.InvalidUnicodeEscape(error.ExpectedHexDigitOrCloseBrace),
      location: SrcSpan(start: 4, end: 5),
    )),
    location: SrcSpan(start: 4, end: 5),
  ))
}

pub fn string_unclosed_unicode_escape_sequence_test() {
  "\"\\u{039a\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.InvalidUnicodeEscape(error.ExpectedHexDigitOrCloseBrace),
      location: SrcSpan(start: 8, end: 9),
    )),
    location: SrcSpan(start: 8, end: 9),
  ))
}

pub fn string_empty_unicode_escape_sequence_test() {
  "\"\\u{}\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.InvalidUnicodeEscape(error.InvalidNumberOfHexDigits),
      location: SrcSpan(start: 1, end: 5),
    )),
    location: SrcSpan(start: 1, end: 5),
  ))
}

pub fn string_overlong_unicode_escape_sequence_test() {
  "\"\\u{0011f601}\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.InvalidUnicodeEscape(error.InvalidNumberOfHexDigits),
      location: SrcSpan(start: 1, end: 13),
    )),
    location: SrcSpan(start: 1, end: 13),
  ))
}

pub fn string_invalid_unicode_escape_sequence_test() {
  "\"\\u{110000}\""
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.InvalidUnicodeEscape(error.InvalidCodepoint),
      location: SrcSpan(start: 1, end: 11),
    )),
    location: SrcSpan(start: 1, end: 11),
  ))
}

// TODO
pub fn bit_array() {
  todo
}

// TODO
pub fn bit_array1() {
  todo
}

// TODO
pub fn bit_array2() {
  todo
}

pub fn name_test() {
  "let xS = 1"
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.BadName(name: "xS"),
      location: SrcSpan(start: 4, end: 6),
    )),
    location: SrcSpan(start: 4, end: 6),
  ))
}

pub fn name1_test() {
  "let _xS = 1"
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.BadDiscardName(name: "_xS"),
      location: SrcSpan(start: 4, end: 7),
    )),
    location: SrcSpan(start: 4, end: 7),
  ))
}

pub fn name2_test() {
  "type S_m = String"
  |> should_err(ParseError(
    error: error.LexError(error: LexicalError(
      error: error.BadUpname(name: "S_m"),
      location: SrcSpan(start: 5, end: 8),
    )),
    location: SrcSpan(start: 5, end: 8),
  ))
}

pub fn pointless_spread_test() {
  "let xs = [] [..xs]"
  |> should_err(ParseError(
    error: error.ListSpreadWithoutElements,
    location: SrcSpan(start: 12, end: 18),
  ))
}

pub fn lowcase_bool_in_pattern_test() {
  "case 42 > 42 { true -> 1; false -> 2; }"
  |> should_err(ParseError(
    error: error.LowcaseBooleanPattern,
    location: SrcSpan(start: 15, end: 19),
  ))
}

pub fn anonymous_function_labeled_arguments_test() {
  "let anon_subtract = fn (minuend a: Int, subtrahend b: Int) -> Int {
  a - b
}"
  |> should_err(ParseError(
    error: error.UnexpectedLabel,
    location: SrcSpan(start: 24, end: 31),
  ))
}

pub fn no_let_binding_test() {
  "foo = 32"
  |> should_err(ParseError(
    error: error.NoLetBinding,
    location: SrcSpan(start: 4, end: 5),
  ))
}

pub fn no_let_binding1_test() {
  "foo:Int = 32"
  |> should_err(ParseError(
    error: error.NoLetBinding,
    location: SrcSpan(start: 3, end: 4),
  ))
}

pub fn no_let_binding2_test() {
  "let bar:Int = 32
bar = 42"
  |> should_err(ParseError(
    error: error.NoLetBinding,
    location: SrcSpan(start: 21, end: 22),
  ))
}

pub fn no_let_binding3_test() {
  "[x] = [2]"
  |> should_err(ParseError(
    error: error.NoLetBinding,
    location: SrcSpan(start: 4, end: 5),
  ))
}

pub fn no_eq_after_binding_test() {
  "let foo"
  |> should_err(ParseError(
    error: error.ExpectedEqual,
    location: SrcSpan(start: 4, end: 7),
  ))
}

pub fn no_eq_after_binding1_test() {
  "let foo
foo = 4"
  |> should_err(ParseError(
    error: error.ExpectedEqual,
    location: SrcSpan(start: 4, end: 7),
  ))
}

pub fn no_let_binding_snapshot_1_test() {
  "foo = 4"
  |> should_any_err
}

pub fn no_let_binding_snapshot_2_test() {
  "foo:Int = 4"
  |> should_any_err
}

pub fn no_let_binding_snapshot_3_test() {
  "let bar:Int = 32
bar = 42"
  |> should_any_err
}

pub fn no_eq_after_binding_snapshot_1_test() {
  "let foo"
  |> should_any_err
}

pub fn no_eq_after_binding_snapshot_2_test() {
  "let foo
foo = 4"
  |> should_any_err
}

pub fn discard_left_hand_side_of_concat_pattern_test() {
  "
case \"\" {
  _ <> rest -> rest
}
"
  |> should_any_err
}

pub fn assign_left_hand_side_of_concat_pattern_test() {
  "
case \"\" {
  first <> rest -> rest
}
"
  |> should_any_err
}

// https://github.com/gleam-lang/gleam/issues/1890
pub fn valueless_list_spread_expression_test() {
  "let x = [1, 2, 3, ..]"
  |> should_any_err
}

// https://github.com/gleam-lang/gleam/issues/2035
pub fn semicolons_test() {
  "{ 2 + 3; - -5; }"
  |> should_any_err
}

pub fn bare_expression_test() {
  "1"
  |> should_parse
}

// https://github.com/gleam-lang/gleam/issues/1991
pub fn block_of_one_test() {
  "{ 1 }"
  |> should_parse
}

// https://github.com/gleam-lang/gleam/issues/1991
pub fn block_of_two_test() {
  "{ 1 2 }"
  |> should_parse
}

// https://github.com/gleam-lang/gleam/issues/1991
pub fn nested_block_test() {
  "{ 1 { 1.0 2.0 } 3 }"
  |> should_parse
}

// https://github.com/gleam-lang/gleam/issues/1831
pub fn argument_scope_test() {
  "
1 + let a = 5
a
"
  |> should_any_err
}

pub fn multiple_external_for_same_project_erlang_test() {
  "
@external(erlang, \"one\", \"two\")
@external(erlang, \"three\", \"four\")
pub fn one(x: Int) -> Int {
  todo
}
"
  |> should_module_err
}

pub fn multiple_external_for_same_project_javascript_test() {
  "
@external(javascript, \"one\", \"two\")
@external(javascript, \"three\", \"four\")
pub fn one(x: Int) -> Int {
  todo
}
"
  |> should_module_err
}

pub fn unknown_attribute_test() {
  "@go_faster()
pub fn main() { 1 }"
  |> should_module_err
}

pub fn incomplete_function_test() {
  "fn()"
  |> should_any_err
}

pub fn multiple_deprecation_attributes_test() {
  "
@deprecated(\"1\")
@deprecated(\"2\")
pub fn main() -> Nil {
  Nil
}
"
  |> should_module_err
}

pub fn multiple_internal_attributes_test() {
  "
@internal
@internal
pub fn main() -> Nil {
  Nil
}
"
  |> should_module_err
}

pub fn attributes_with_no_definition_test() {
  "
@deprecated(\"1\")
@target(erlang)
"
  |> should_module_err
}

pub fn external_attribute_with_non_fn_definition_test() {
  "
@external(erlang, \"module\", \"fun\")
pub type Fun
"
  |> should_module_err
}

pub fn attributes_with_improper_definition_test() {
  "
@deprecated(\"1\")
@external(erlang, \"module\", \"fun\")
"
  |> should_module_err
}

pub fn const_with_function_call_test() {
  "
pub fn wibble() { 123 }
const wib: Int = wibble()
"
  |> should_module_err
}

pub fn const_with_function_call_with_args_test() {
  "
pub fn wibble() { 123 }
const wib: Int = wibble(1, \"wobble\")
"
  |> should_module_err
}

pub fn import_type_test() {
  "import wibble.{type Wobble, Wobble, type Wabble}"
  |> should_parse_module
}

pub fn reserved_auto_test() {
  "const auto = 1"
  |> should_module_err
}

pub fn reserved_delegate_test() {
  "const delegate = 1"
  |> should_module_err
}

pub fn reserved_derive_test() {
  "const derive = 1"
  |> should_module_err
}

pub fn reserved_else_test() {
  "const else = 1"
  |> should_module_err
}

pub fn reserved_implement_test() {
  "const implement = 1"
  |> should_module_err
}

pub fn reserved_macro_test() {
  "const macro = 1"
  |> should_module_err
}

pub fn reserved_test_test() {
  "const test = 1"
  |> should_module_err
}

pub fn reserved_echo_test() {
  "const echo = 1"
  |> should_module_err
}

pub fn capture_with_name_test() {
  "
pub fn main() {
  add(_name, 1)
}

fn add(x, y) {
  x + y
}
"
  |> should_module_err
}

pub fn list_spread_with_no_tail_in_the_middle_of_a_list_test() {
  "
pub fn main() -> Nil {
  let xs = [1, 2, 3]
  [1, 2, .., 3 + 3, 4]
}
"
  |> should_module_err
}

pub fn list_spread_followed_by_extra_items_test() {
  "
pub fn main() -> Nil {
  let xs = [1, 2, 3]
  [1, 2, ..xs, 3 + 3, 4]
}
"
  |> should_module_err
}

// Tests for nested tuples and structs in tuples
// https://github.com/gleam-lang/gleam/issues/1980

pub fn nested_tuples_test() {
  "
let tup = #(#(5, 6))
{tup.0}.1
"
  |> should_parse
}

pub fn nested_tuples_no_block_test() {
  "
let tup = #(#(5, 6))
tup.0.1
"
  |> should_parse
}

pub fn deeply_nested_tuples_test() {
  "
let tup = #(#(#(#(4))))
{{{tup.0}.0}.0}.0
"
  |> should_parse
}

pub fn deeply_nested_tuples_no_block_test() {
  "
let tup = #(#(#(#(4))))
tup.0.0.0.0
"
  |> should_parse
}

pub fn inner_single_quote_parses_test() {
  "
let a = \"inner 'quotes'\"
"
  |> should_parse
}

pub fn string_single_char_suggestion_test() {
  "
pub fn main() {
    let a = 'example'
  }
"
  |> should_module_err
}

pub fn private_internal_const_test() {
  "
@internal
const wibble = 1
"
  |> should_module_err
}

pub fn private_internal_type_alias_test() {
  "
@internal
type Alias = Int
"
  |> should_module_err
}

pub fn private_internal_function_test() {
  "
@internal
fn wibble() { todo }
"
  |> should_module_err
}

pub fn private_internal_type_test() {
  "
@internal
type Wibble {
  Wibble
}
"
  |> should_module_err
}

pub fn wrong_record_access_pattern_test() {
  "
pub fn main() {
  case wibble {
    wibble.thing -> 1
  }
}
"
  |> should_module_err
}

pub fn tuple_invalid_expr_test() {
  "
fn main() {
    #(1, 2, const)
}
"
  |> should_module_err
}

fn bit_array_invalid_segment_test() {
  todo
  //     assert_module_error!(
  //         "
  // fn main() {
  //     <<72, 101, 108, 108, 111, 44, 32, 74, 111, 101, const>>
  // }
  // "
  //     );
}

pub fn case_invalid_expression_test() {
  "
fn main() {
    case 1, type {
        _, _ -> 0
    }
}
"
  |> should_module_err
}

pub fn case_invalid_case_pattern_test() {
  "
fn main() {
    case 1 {
        -> -> 0
    }
}
"
  |> should_module_err
}

pub fn use_invalid_assignments_test() {
  "
fn main() {
    use fn <- result.try(get_username())
}
"
  |> should_module_err
}

pub fn assignment_pattern_invalid_tuple_test() {
  "
fn main() {
    let #(a, case, c) = #(1, 2, 3)
}
"
  |> should_module_err
}

fn assignment_pattern_invalid_bit_segment_test() {
  todo
  //     assert_module_error!(
  //         "
  // fn main() {
  //     let <<b1, pub>> = <<24, 3>>
  // }
  // "
  //     );
}

pub fn type_invalid_constructor_test() {
  "
type A {
    A(String)
    type
}
"
  |> should_module_err
}

pub fn type_invalid_type_name_test() {
  "
type A(a, type) {
    A
}
"
  |> should_module_err
}

pub fn type_invalid_constructor_arg_test() {
  "
type A {
    A(type: String)
}
"
  |> should_module_err
}

pub fn function_type_invalid_param_type_test() {
  "
fn f(g: fn(Int, 1) -> Int) -> Int {
  g(0, 1)
}
"
  |> should_module_err
}

pub fn const_invalid_tuple_test() {
  "
const a = #(1, 2, <-)
"
  |> should_module_err
}

pub fn const_invalid_list_test() {
  "
const a = [1, 2, <-]
"
  |> should_module_err
}

fn const_invalid_bit_array_segment_test() {
  todo
  //     assert_module_error!(
  //         "
  // const a = <<1, 2, <->>
  // "
  //     );
}

pub fn const_invalid_record_constructor_test() {
  "
type A {
    A(String, Int)
}
const a = A(\"a\", let)
"
  |> should_module_err
}

pub fn newline_tokens_test() {
  lexer.make_tokenizer("1\n\n2\n")
  |> lexer.iterator
  |> iterator.to_list
  |> should.equal([
    Ok(#(0, token.Int(value: "1"), 1)),
    Ok(#(1, token.NewLine, 2)),
    Ok(#(2, token.NewLine, 3)),
    Ok(#(3, token.Int(value: "2"), 4)),
    Ok(#(4, token.NewLine, 5)),
  ])
}
