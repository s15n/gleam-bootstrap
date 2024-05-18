import gleeunit/should

import ast.{SrcSpan}
import parse
import parse/error.{LexicalError, ParseError}

fn should_err(src: String, error) {
  let assert Error(result) = parse.parse_statement_sequence(src)
  result
  |> should.equal(error)
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
