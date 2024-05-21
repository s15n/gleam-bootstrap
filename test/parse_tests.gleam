import gleeunit/should

import ast.{SrcSpan}
import parse
import parse/error.{LexicalError, ParseError}

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
