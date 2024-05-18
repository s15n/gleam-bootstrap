import gleam/bool.{guard}
import gleam/int
import gleam/iterator.{type Iterator}
import gleam/option.{type Option, None, Some}
import gleam/queue.{type Queue}
import gleam/regex
import gleam/result
import gleam/string
import gleam/string_builder.{type StringBuilder}

import ast.{type SrcSpan, SrcSpan}
import parse/error.{type LexicalError, LexicalError}
import parse/token.{type Token}

import gleam/io

pub type Lexer {
  Lexer(
    chars: Iterator(#(String, Int)),
    pending: Queue(Spanned),
    chr0: Option(String),
    chr1: Option(String),
    loc0: Int,
    loc1: Int,
    location: Int,
  )
}

pub type Spanned =
  #(Int, Token, Int)

pub type LexResult =
  Result(Spanned, LexicalError)

pub fn str_to_keyword(word: String) -> Option(Token) {
  // Alphabetical keywords:
  case word {
    "as" -> Some(token.As)
    "assert" -> Some(token.Assert)
    "auto" -> Some(token.Auto)
    "case" -> Some(token.Case)
    "const" -> Some(token.Const)
    "delegate" -> Some(token.Delegate)
    "derive" -> Some(token.Derive)
    "echo" -> Some(token.Echo)
    "else" -> Some(token.Else)
    "fn" -> Some(token.Fn)
    "if" -> Some(token.If)
    "implement" -> Some(token.Implement)
    "import" -> Some(token.Import)
    "let" -> Some(token.Let)
    "macro" -> Some(token.Macro)
    "opaque" -> Some(token.Opaque)
    "panic" -> Some(token.Panic)
    "pub" -> Some(token.Pub)
    "test" -> Some(token.Test)
    "todo" -> Some(token.Todo)
    "type" -> Some(token.Type)
    "use" -> Some(token.Use)
    _ -> None
  }
}

pub fn make_tokenizer(source: String) -> Lexer {
  let chars =
    source
    |> string.to_graphemes
    |> iterator.from_list
    |> iterator.index
  let nlh = new_nlh(chars)
  new(nlh_iterator(nlh))
}

// The newline handler is an iterator which collapses different newline
// types into \n always.
pub type NewlineHandler {
  NewlineHandler(
    source: Iterator(#(String, Int)),
    chr0: Option(#(String, Int)),
    chr1: Option(#(String, Int)),
  )
}

pub fn new_nlh(chars: Iterator(#(String, Int))) -> NewlineHandler {
  let nlh = NewlineHandler(chars, None, None)
  let #(_, nlh) = nlh_shift(nlh)
  let #(_, nlh) = nlh_shift(nlh)
  nlh
}

fn nlh_shift(nlh: NewlineHandler) -> #(Option(#(String, Int)), NewlineHandler) {
  let result = nlh.chr0
  let chr0 = nlh.chr1
  let #(chr1, source) = case iterator.step(nlh.source) {
    iterator.Done -> #(None, iterator.empty())
    iterator.Next(chr1, source) -> #(Some(chr1), source)
  }
  #(result, NewlineHandler(source, chr0, chr1))
}

fn nlh_iterator(nlh: NewlineHandler) -> Iterator(#(String, Int)) {
  let yield = fn(nlh: NewlineHandler) {
    let nlh = case nlh.chr0 {
      Some(#("\r", i)) -> {
        case nlh.chr1 {
          Some(#("\n", _)) -> {
            let #(_, nlh) = nlh_shift(nlh)
            NewlineHandler(..nlh, chr0: Some(#("\n", i)))
          }
          _ -> NewlineHandler(..nlh, chr0: Some(#("\n", i)))
        }
      }
      _ -> nlh
    }
    let #(chr, nlh) = nlh_shift(nlh)
    case chr {
      Some(c) -> iterator.Next(c, nlh)
      None -> iterator.Done
    }
  }
  iterator.unfold(nlh, yield)
}

pub fn new(input: Iterator(#(String, Int))) -> Lexer {
  let lexer =
    Lexer(
      chars: input,
      pending: queue.new(),
      location: 0,
      chr0: None,
      chr1: None,
      loc0: 0,
      loc1: 0,
    )
  let #(_, lexer) = next_char(lexer)
  let #(_, lexer) = next_char(lexer)
  Lexer(..lexer, location: 0)
}

// This is the main entry point. Call this function to retrieve the next token.
// This function is used by the iterator implementation.
fn inner_next(lexer: Lexer) -> #(LexResult, Lexer) {
  case queue.pop_front(lexer.pending) {
    Error(_) -> {
      let #(res, lexer) = consume_normal(lexer)
      case res {
        Ok(_) -> inner_next(lexer)
        Error(err) -> #(Error(err), lexer)
      }
    }
    Ok(#(first, rest)) -> {
      #(Ok(first), Lexer(..lexer, pending: rest))
    }
  }
}

// Take a look at the next character, if any, and decide upon the next steps.
fn consume_normal(lexer: Lexer) -> #(Result(Nil, LexicalError), Lexer) {
  case lexer.chr0 {
    Some(c) -> {
      // #(Result(Nil, LexicalError), Bool, Lexer)
      let #(res, check_for_minus, lexer) = {
        let res = {
          use <- bool.guard(when: !is_upname_start(c), return: None)
          let #(res, lexer) = lex_upname(lexer)
          Some(case res {
            Ok(name) -> {
              let lexer = emit(lexer, name)
              #(Ok(Nil), False, lexer)
            }
            Error(err) -> #(Error(err), False, lexer)
          })
        }
        use <- option.lazy_unwrap(res)
        let res = {
          use <- bool.guard(when: !is_name_start(c), return: None)
          let #(res, lexer) = lex_name(lexer)
          Some(case res {
            Ok(name) -> {
              let lexer = emit(lexer, name)
              let lexer = maybe_lex_dot_access(lexer)
              #(Ok(Nil), True, lexer)
            }
            Error(err) -> #(Error(err), True, lexer)
          })
        }
        use <- option.lazy_unwrap(res)
        let res = {
          use <- bool.guard(when: !is_number_start(c, lexer.chr1), return: None)
          let #(res, lexer) = lex_number(lexer)
          Some(case res {
            Ok(num) -> {
              let lexer = emit(lexer, num)
              #(Ok(Nil), True, lexer)
            }
            Error(err) -> #(Error(err), True, lexer)
          })
        }
        use <- option.lazy_unwrap(res)
        let #(res, lexer) = consume_character(lexer, c)
        case res {
          Ok(_) -> #(Ok(Nil), False, lexer)
          Error(err) -> #(Error(err), False, lexer)
        }
      }
      case res {
        Ok(_) ->
          case
            check_for_minus
            && lexer.chr0 == Some("-")
            && is_number_start("-", lexer.chr1)
          {
            True -> {
              // We want to lex `1-1` and `x-1` as `1 - 1` and `x - 1`
              let lexer = eat_single_char(lexer, token.Minus)
              #(Ok(Nil), lexer)
            }
            False -> #(Ok(Nil), lexer)
          }
        Error(err) -> #(Error(err), lexer)
      }
    }
    None -> {
      // We reached end of file.
      let tok_pos = get_pos(lexer)
      let lexer = emit(lexer, #(tok_pos, token.EndOfFile, tok_pos))
      #(Ok(Nil), lexer)
    }
  }
}

fn consume_character(
  lexer: Lexer,
  c: String,
) -> #(Result(Nil, LexicalError), Lexer) {
  case c {
    "@" -> #(Ok(Nil), eat_single_char(lexer, token.At))
    "\"" -> {
      let #(res, lexer) = lex_string(lexer)
      case res {
        Ok(str) -> #(Ok(Nil), emit(lexer, str))
        Error(err) -> #(Error(err), lexer)
      }
    }
    "=" -> #(
      Ok(Nil),
      maybe_double_char(lexer, "=", token.Equal, token.EqualEqual),
    )
    "+" -> #(Ok(Nil), maybe_double_char(lexer, ".", token.Plus, token.PlusDot))
    "*" -> #(Ok(Nil), maybe_double_char(lexer, ".", token.Star, token.StarDot))
    "/" -> {
      let token_start = get_pos(lexer)
      let #(_, lexer) = next_char(lexer)
      case lexer.chr0 {
        Some(".") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.SlashDot, token_end)))
        }
        Some("/") -> {
          let #(_, lexer) = next_char(lexer)
          let #(comment, lexer) = lex_comment(lexer)
          #(Ok(Nil), emit(lexer, comment))
        }
        _ -> {
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.Slash, token_end)))
        }
      }
    }
    "%" -> #(Ok(Nil), eat_single_char(lexer, token.Percent))
    "|" -> {
      let token_start = get_pos(lexer)
      let #(_, lexer) = next_char(lexer)
      case lexer.chr0 {
        Some("|") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.VbarVbar, token_end)))
        }
        Some(">") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.Pipe, token_end)))
        }
        _ -> {
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.Vbar, token_end)))
        }
      }
    }
    "&" -> {
      let token_start = get_pos(lexer)
      let #(_, lexer) = next_char(lexer)
      case lexer.chr0 {
        Some("&") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.AmperAmper, token_end)))
        }
        _ -> {
          #(
            Error(LexicalError(
              error: error.UnrecognizedToken("&"),
              location: SrcSpan(token_start, token_start),
            )),
            lexer,
          )
        }
      }
    }
    "-" -> {
      let token_start = get_pos(lexer)
      let #(_, lexer) = next_char(lexer)
      case lexer.chr0 {
        Some(".") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.MinusDot, token_end)))
        }
        Some(">") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.RArrow, token_end)))
        }
        _ -> {
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.Minus, token_end)))
        }
      }
    }
    "!" -> #(Ok(Nil), maybe_double_char(lexer, "=", token.Bang, token.NotEqual))
    "(" -> #(Ok(Nil), eat_single_char(lexer, token.LeftParen))
    ")" -> #(Ok(Nil), eat_single_char(lexer, token.RightParen))
    "[" -> #(Ok(Nil), eat_single_char(lexer, token.LeftSquare))
    "]" -> #(Ok(Nil), eat_single_char(lexer, token.RightSquare))
    "{" -> #(Ok(Nil), eat_single_char(lexer, token.LeftBrace))
    "}" -> #(Ok(Nil), eat_single_char(lexer, token.RightBrace))
    ":" -> #(Ok(Nil), eat_single_char(lexer, token.Colon))
    "<" -> {
      let token_start = get_pos(lexer)
      let #(_, lexer) = next_char(lexer)
      case lexer.chr0 {
        Some(">") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.LtGt, token_end)))
        }
        Some("<") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.LtLt, token_end)))
        }
        Some(".") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.LessDot, token_end)))
        }
        Some("-") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.LArrow, token_end)))
        }
        Some("=") -> {
          let #(_, lexer) = next_char(lexer)
          case lexer.chr0 {
            Some(".") -> {
              let #(_, lexer) = next_char(lexer)
              let token_end = get_pos(lexer)
              #(
                Ok(Nil),
                emit(lexer, #(token_start, token.LessEqualDot, token_end)),
              )
            }
            _ -> {
              let token_end = get_pos(lexer)
              #(
                Ok(Nil),
                emit(lexer, #(token_start, token.LessEqual, token_end)),
              )
            }
          }
        }
        _ -> {
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.Less, token_end)))
        }
      }
    }
    ">" -> {
      let token_start = get_pos(lexer)
      let #(_, lexer) = next_char(lexer)
      case lexer.chr0 {
        Some(">") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.GtGt, token_end)))
        }
        Some(".") -> {
          let #(_, lexer) = next_char(lexer)
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.GreaterDot, token_end)))
        }
        Some("=") -> {
          let #(_, lexer) = next_char(lexer)
          case lexer.chr0 {
            Some(".") -> {
              let #(_, lexer) = next_char(lexer)
              let token_end = get_pos(lexer)
              #(
                Ok(Nil),
                emit(lexer, #(token_start, token.GreaterEqualDot, token_end)),
              )
            }
            _ -> {
              let token_end = get_pos(lexer)
              #(
                Ok(Nil),
                emit(lexer, #(token_start, token.GreaterEqual, token_end)),
              )
            }
          }
        }
        _ -> {
          let token_end = get_pos(lexer)
          #(Ok(Nil), emit(lexer, #(token_start, token.Greater, token_end)))
        }
      }
    }
    "," -> #(Ok(Nil), eat_single_char(lexer, token.Comma))
    "." -> #(Ok(Nil), maybe_double_char(lexer, ".", token.Dot, token.DotDot))
    "#" -> #(Ok(Nil), eat_single_char(lexer, token.Hash))
    "\n" | " " | "\t" | "\u{0C}" -> {
      let token_start = get_pos(lexer)
      let #(_, lexer) = next_char(lexer)
      let token_end = get_pos(lexer)
      let lexer = case c {
        "\n" -> emit(lexer, #(token_start, token.NewLine, token_end))
        _ -> lexer
      }
      #(Ok(Nil), lexer)
    }
    c -> {
      let location = get_pos(lexer)
      #(
        Error(LexicalError(
          error: error.UnrecognizedToken(c),
          location: SrcSpan(location, location),
        )),
        lexer,
      )
    }
  }
}

// Small abstraction for function above
fn maybe_double_char(
  lexer: Lexer,
  second: String,
  ty_for_one: Token,
  ty_for_two: Token,
) -> Lexer {
  let token_start = get_pos(lexer)
  let #(_, lexer) = next_char(lexer)
  case lexer.chr0 == Some(second) {
    True -> {
      let #(_, lexer) = next_char(lexer)
      let token_end = get_pos(lexer)
      emit(lexer, #(token_start, ty_for_two, token_end))
    }
    False -> {
      let token_end = get_pos(lexer)
      emit(lexer, #(token_start, ty_for_one, token_end))
    }
  }
}

// Lexer helper functions:
// this can be either a reserved word, or a name
fn lex_name(lexer: Lexer) -> #(LexResult, Lexer) {
  let sb = string_builder.new()
  let start_pos = get_pos(lexer)

  let #(sb, lexer) = push_chars(lexer, sb, is_name_continuation)

  // Finish lexing the upname and return an error if an underscore is used
  let #(is_error, sb, lexer) = push_name_error_chars(lexer, sb, True)
  let end_pos = get_pos(lexer)

  let name = string_builder.to_string(sb)

  case is_error, string.starts_with(name, "_") {
    True, True -> #(
      Error(LexicalError(
        error: error.BadDiscardName(name),
        location: SrcSpan(start_pos, end_pos),
      )),
      lexer,
    )
    True, False -> #(
      Error(LexicalError(
        error: error.BadName(name),
        location: SrcSpan(start_pos, end_pos),
      )),
      lexer,
    )
    False, True -> #(Ok(#(start_pos, token.DiscardName(name), end_pos)), lexer)
    False, False ->
      case str_to_keyword(name) {
        Some(token) -> #(Ok(#(start_pos, token, end_pos)), lexer)
        None -> #(Ok(#(start_pos, token.Name(name), end_pos)), lexer)
      }
  }
}

// A type name or constructor
fn lex_upname(lexer: Lexer) -> #(LexResult, Lexer) {
  let sb = string_builder.new()
  let start_pos = get_pos(lexer)

  let #(sb, lexer) = push_chars(lexer, sb, is_upname_continuation)

  // Finish lexing the upname and return an error if an underscore is used
  let #(is_error, sb, lexer) = push_name_error_chars(lexer, sb, True)
  let end_pos = get_pos(lexer)

  let name = string_builder.to_string(sb)

  case is_error {
    True -> #(
      Error(LexicalError(
        error: error.BadUpname(name),
        location: SrcSpan(start_pos, end_pos),
      )),
      lexer,
    )
    False ->
      case str_to_keyword(name) {
        Some(token) -> #(Ok(#(start_pos, token, end_pos)), lexer)
        None -> #(Ok(#(start_pos, token.UpName(name), end_pos)), lexer)
      }
  }
}

// Loop for 2 functions above
fn push_chars(
  lexer: Lexer,
  sb: StringBuilder,
  condition: fn(Lexer) -> Bool,
) -> #(StringBuilder, Lexer) {
  case condition(lexer) {
    True -> {
      let assert #(Some(c), lexer) = next_char(lexer)
      let sb = string_builder.append(sb, c)
      push_chars(lexer, sb, condition)
    }
    False -> #(sb, lexer)
  }
}

// Loop for 2 functions above push_chars
fn push_name_error_chars(
  lexer: Lexer,
  sb: StringBuilder,
  first: Bool,
) -> #(Bool, StringBuilder, Lexer) {
  case is_name_error_continuation(lexer) {
    True -> {
      let assert #(Some(c), lexer) = next_char(lexer)
      let sb = string_builder.append(sb, c)
      push_name_error_chars(lexer, sb, False)
    }
    False -> #(!first, sb, lexer)
  }
}

fn lex_number(lexer: Lexer) -> #(LexResult, Lexer) {
  let start_pos = get_pos(lexer)
  let #(res, lexer) = case lexer.chr0 {
    Some("0") ->
      case lexer.chr1 {
        Some("x") | Some("X") -> {
          // Hex!
          let #(_, lexer) = next_char(lexer)
          let #(_, lexer) = next_char(lexer)
          lex_number_radix(lexer, start_pos, 16, "0x")
        }
        Some("o") | Some("O") -> {
          // Octal!
          let #(_, lexer) = next_char(lexer)
          let #(_, lexer) = next_char(lexer)
          lex_number_radix(lexer, start_pos, 8, "0o")
        }
        Some("b") | Some("B") -> {
          // Binary!
          let #(_, lexer) = next_char(lexer)
          let #(_, lexer) = next_char(lexer)
          lex_number_radix(lexer, start_pos, 2, "0b")
        }
        _ -> {
          let #(num, lexer) = lex_decimal_number(lexer)
          #(Ok(num), lexer)
        }
      }
    _ -> {
      let #(num, lexer) = lex_decimal_number(lexer)
      #(Ok(num), lexer)
    }
  }

  case res {
    Ok(_) ->
      case lexer.chr0 {
        Some("_") -> {
          let location = get_pos(lexer)
          #(
            Error(LexicalError(
              error: error.NumTrailingUnderscore,
              location: SrcSpan(location, location),
            )),
            lexer,
          )
        }
        _ -> #(res, lexer)
      }
    Error(_) -> #(res, lexer)
  }
}

// Lex a hex/octal/decimal/binary number without a decimal point.
fn lex_number_radix(
  lexer: Lexer,
  start_pos: Int,
  radix: Int,
  prefix: String,
) -> #(LexResult, Lexer) {
  let #(num, lexer) = radix_run(lexer, radix)
  case num {
    "" -> {
      let location = get_pos(lexer) - 1
      #(
        Error(LexicalError(
          error: error.RadixIntNoValue,
          location: SrcSpan(location, location),
        )),
        lexer,
      )
    }
    _ ->
      case radix < 16 && is_digit_of_radix(lexer.chr0, 16) {
        True -> {
          let location = get_pos(lexer)
          #(
            Error(LexicalError(
              error: error.DigitOutOfRadix,
              location: SrcSpan(location, location),
            )),
            lexer,
          )
        }
        False -> {
          let end_pos = get_pos(lexer)
          #(Ok(#(start_pos, token.Int(prefix <> num), end_pos)), lexer)
        }
      }
  }
}

// Lex a normal number, that is, no octal, hex or binary number.
// This function cannot be reached without the head of the stream being either 0-9 or '-', 0-9
fn lex_decimal_number(lexer: Lexer) -> #(Spanned, Lexer) {
  lex_decimal_or_int_number(lexer, True)
}

fn lex_int_number(lexer: Lexer) -> #(Spanned, Lexer) {
  lex_decimal_or_int_number(lexer, False)
}

fn lex_decimal_or_int_number(
  lexer: Lexer,
  can_lex_decimal: Bool,
) -> #(Spanned, Lexer) {
  let start_pos = get_pos(lexer)
  let sb = string_builder.new()
  // consume negative sign
  let #(sb, lexer) = case lexer.chr0 {
    Some("-") -> {
      let assert #(Some(c), lexer) = next_char(lexer)
      let sb = string_builder.append(sb, c)
      #(sb, lexer)
    }
    _ -> #(sb, lexer)
  }
  // consume first run of digits
  let #(first_run, lexer) = radix_run(lexer, 10)
  let sb = string_builder.append(sb, first_run)

  // If float:
  case can_lex_decimal, lexer.chr0 {
    True, Some(".") -> {
      let assert #(Some(c), lexer) = next_char(lexer)
      let sb = string_builder.append(sb, c)
      let #(second_run, lexer) = radix_run(lexer, 10)
      let sb = string_builder.append(sb, second_run)

      // If scientific:
      let #(sb, lexer) = case lexer.chr0 {
        Some("e") -> {
          let assert #(Some(c), lexer) = next_char(lexer)
          let sb = string_builder.append(sb, c)
          let #(sb, lexer) = case lexer.chr0 {
            Some("-") -> {
              let assert #(Some(c), lexer) = next_char(lexer)
              let sb = string_builder.append(sb, c)
              #(sb, lexer)
            }
            _ -> #(sb, lexer)
          }
          let #(third_run, lexer) = radix_run(lexer, 10)
          let sb = string_builder.append(sb, third_run)
          #(sb, lexer)
        }
        _ -> #(sb, lexer)
      }
      let end_pos = get_pos(lexer)
      #(#(start_pos, token.Float(string_builder.to_string(sb)), end_pos), lexer)
    }
    _, _ -> {
      let end_pos = get_pos(lexer)
      #(#(start_pos, token.Int(string_builder.to_string(sb)), end_pos), lexer)
    }
  }
}

// Maybe lex dot access that comes after name token.
fn maybe_lex_dot_access(lexer: Lexer) -> Lexer {
  // It can be nested like: `tuple.1.2.3.4`
  let assert Ok(re) = regex.from_string("^[0-9]$")
  case lexer.chr0, lexer.chr1 {
    Some("."), Some(chr1) ->
      case regex.check(with: re, content: chr1) {
        True -> {
          let lexer = eat_single_char(lexer, token.Dot)
          let #(num, lexer) = lex_int_number(lexer)
          emit(lexer, num)
          |> maybe_lex_dot_access
        }
        False -> lexer
      }
    _, _ -> lexer
  }
}

// Consume a sequence of numbers with the given radix,
// the digits can be decorated with underscores
// like this: '1_2_3_4' == '1234'
fn radix_run(lexer: Lexer, radix: Int) -> #(String, Lexer) {
  let #(sb, lexer) = radix_run_append(lexer, radix, string_builder.new())
  #(string_builder.to_string(sb), lexer)
}

fn radix_run_append(
  lexer: Lexer,
  radix: Int,
  sb: StringBuilder,
) -> #(StringBuilder, Lexer) {
  case take_number(lexer, radix) {
    #(Some(c), lexer) -> {
      let sb = string_builder.append(sb, c)
      radix_run_append(lexer, radix, sb)
    }
    #(None, lexer) ->
      case lexer.chr0 == Some("_") && is_digit_of_radix(lexer.chr1, radix) {
        True -> {
          let sb = string_builder.append(sb, "_")
          let #(_, lexer) = next_char(lexer)
          radix_run_append(lexer, radix, sb)
        }
        False -> #(sb, lexer)
      }
  }
}

// Consume a single character with the given radix.
fn take_number(lexer: Lexer, radix: Int) -> #(Option(String), Lexer) {
  case is_digit_of_radix(lexer.chr0, radix) {
    True -> {
      let assert #(Some(c), lexer) = next_char(lexer)
      #(Some(c), lexer)
    }
    False -> #(None, lexer)
  }
}

// Test if a digit is of a certain radix.
fn is_digit_of_radix(c: Option(String), radix: Int) -> Bool {
  case c {
    Some(c) -> {
      let re_str = case radix {
        2 -> "^[01]$"
        8 -> "^[0-7]$"
        10 -> "^[0-9]$"
        16 -> "^[0-9A-Fa-f]$"
        other -> panic as "Radix not implemented: " <> int.to_string(other)
      }
      let assert Ok(re) = regex.from_string(re_str)
      regex.check(with: re, content: c)
    }
    None -> False
  }
}

// There are 3 kinds of comments
// 2 slash, normal
// 3 slash, document
// 4 slash, module
// this function is entered after 2 slashes
fn lex_comment(lexer: Lexer) -> #(Spanned, Lexer) {
  let kind = case lexer.chr0, lexer.chr1 {
    Some("/"), Some("/") -> ModuleDocComment
    Some("/"), _ -> DocComment
    _, _ -> RegularComment
  }
  let sb = string_builder.new()
  let start_pos = get_pos(lexer)
  let #(sb, lexer) = push_line(lexer, sb)
  let end_pos = get_pos(lexer)
  let token = case kind {
    RegularComment -> token.CommentNormal
    DocComment ->
      sb
      |> string_builder.to_string
      |> token.CommentDoc
    ModuleDocComment -> token.CommentModule
  }
  #(#(start_pos, token, end_pos), lexer)
}

type CommentKind {
  RegularComment
  DocComment
  ModuleDocComment
}

// Loop for function above
fn push_line(lexer: Lexer, sb: StringBuilder) -> #(StringBuilder, Lexer) {
  case lexer.chr0 {
    Some("\n") -> #(sb, lexer)
    Some(c) -> {
      let sb = string_builder.append(sb, c)
      let #(_, lexer) = next_char(lexer)
      push_line(lexer, sb)
    }
    None -> #(sb, lexer)
  }
}

fn lex_string(lexer: Lexer) -> #(LexResult, Lexer) {
  let start_pos = get_pos(lexer)
  // advance past the first quote
  let #(_, lexer) = next_char(lexer)
  let sb = string_builder.new()

  let #(res, lexer) = push_string(lexer, sb, start_pos)
  case res {
    Ok(sb) -> {
      let end_pos = get_pos(lexer)
      let token = token.String(string_builder.to_string(sb))
      #(Ok(#(start_pos, token, end_pos)), lexer)
    }
    Error(err) -> #(Error(err), lexer)
  }
}

// Loop for function above
fn push_string(
  lexer: Lexer,
  sb: StringBuilder,
  start_pos: Int,
) -> #(Result(StringBuilder, LexicalError), Lexer) {
  let #(c, lexer) = next_char(lexer)
  case c {
    Some("\\") -> {
      let slash_pos = get_pos(lexer) - 1
      case lexer.chr0 {
        Some(c) ->
          case c {
            "f" | "n" | "r" | "t" | "\"" | "\\" -> {
              let #(_, lexer) = next_char(lexer)
              let sb = string_builder.append(sb, "\\" <> c)
              push_string(lexer, sb, start_pos)
            }
            "u" -> {
              let #(_, lexer) = next_char(lexer)

              use <- guard(when: lexer.chr0 != Some("{"), return: {
                let location = get_pos(lexer)
                #(
                  Error(LexicalError(
                    error: error.InvalidUnicodeEscape(error.MissingOpeningBrace),
                    location: SrcSpan(location - 1, location),
                  )),
                  lexer,
                )
              })

              // All digits inside \u{...}.
              let hex_sb = string_builder.new()

              case push_escape_hex(lexer, hex_sb) {
                Ok(#(hex_sb, lexer)) ->
                  case lexer.chr0 {
                    Some("}") -> {
                      let #(_, lexer) = next_char(lexer)
                      let hex_str = string_builder.to_string(hex_sb)
                      let hex_str_len = string.length(hex_str)
                      use <- guard(
                        when: hex_str_len < 1 || hex_str_len > 6,
                        return: #(
                          Error(LexicalError(
                            error: error.InvalidUnicodeEscape(
                              error.InvalidNumberOfHexDigits,
                            ),
                            location: SrcSpan(slash_pos, get_pos(lexer)),
                          )),
                          lexer,
                        ),
                      )
                      let assert Ok(hex_parsed) = int.base_parse(hex_str, 16)
                      use <- guard(
                        when: string.utf_codepoint(hex_parsed)
                          |> result.is_error,
                        return: #(
                          Error(LexicalError(
                            error: error.InvalidUnicodeEscape(
                              error.InvalidCodepoint,
                            ),
                            location: SrcSpan(slash_pos, get_pos(lexer)),
                          )),
                          lexer,
                        ),
                      )
                      let sb =
                        string_builder.append(sb, "\\u{" <> hex_str <> "}")
                      push_string(lexer, sb, start_pos)
                    }
                    _ -> {
                      let location = get_pos(lexer)
                      #(
                        Error(LexicalError(
                          error: error.InvalidUnicodeEscape(
                            error.ExpectedHexDigitOrCloseBrace,
                          ),
                          location: SrcSpan(location - 1, location),
                        )),
                        lexer,
                      )
                    }
                  }
                Error(err) -> #(Error(err), lexer)
              }
            }
            _ -> #(
              Error(LexicalError(
                error: error.BadStringEscape,
                location: SrcSpan(slash_pos, slash_pos + 1),
              )),
              lexer,
            )
          }
        _ -> #(
          Error(LexicalError(
            error: error.BadStringEscape,
            location: SrcSpan(slash_pos, slash_pos),
          )),
          lexer,
        )
      }
    }
    Some("\"") -> #(Ok(sb), lexer)
    Some(c) -> {
      let sb = string_builder.append(sb, c)
      push_string(lexer, sb, start_pos)
    }
    None -> #(
      Error(LexicalError(
        error: error.UnexpectedStringEnd,
        location: SrcSpan(start_pos, start_pos),
      )),
      lexer,
    )
  }
}

fn push_escape_hex(
  lexer: Lexer,
  sb: StringBuilder,
) -> Result(#(StringBuilder, Lexer), LexicalError) {
  let #(_, lexer) = next_char(lexer)
  case lexer.chr0 {
    // Don't break early when we've reached 6 digits to ensure a
    // useful error message
    Some("}") -> Ok(#(sb, lexer))
    Some(c) -> {
      let sb = string_builder.append(sb, c)
      let assert Ok(re) = regex.from_string("^[0-9a-fA-F]$")
      case regex.check(with: re, content: c) {
        True -> push_escape_hex(lexer, sb)
        False -> {
          let location = get_pos(lexer)
          Error(LexicalError(
            error: error.InvalidUnicodeEscape(
              error.ExpectedHexDigitOrCloseBrace,
            ),
            location: SrcSpan(location, location + 1),
          ))
        }
      }
    }
    None -> Ok(#(sb, lexer))
  }
}

fn is_name_start(c: String) -> Bool {
  let assert Ok(re) = regex.from_string("^[_a-z]$")
  regex.check(with: re, content: c)
}

fn is_upname_start(c: String) -> Bool {
  let assert Ok(re) = regex.from_string("^[A-Z]$")
  regex.check(with: re, content: c)
}

fn is_number_start(c: String, c1: Option(String)) -> Bool {
  let assert Ok(re) = regex.from_string("^[0-9]$")
  case regex.check(with: re, content: c), c, c1 {
    True, _, _ -> True
    False, "-", Some(c1) -> regex.check(with: re, content: c1)
    _, _, _ -> False
  }
}

fn is_name_continuation(lexer: Lexer) -> Bool {
  let assert Ok(re) = regex.from_string("^[_0-9a-z]$")
  lexer.chr0
  |> option.map(fn(c) { regex.check(with: re, content: c) })
  |> option.unwrap(or: False)
}

fn is_upname_continuation(lexer: Lexer) -> Bool {
  let assert Ok(re) = regex.from_string("^[0-9a-zA-Z]$")
  lexer.chr0
  |> option.map(fn(c) { regex.check(with: re, content: c) })
  |> option.unwrap(or: False)
}

fn is_name_error_continuation(lexer: Lexer) -> Bool {
  let assert Ok(re) = regex.from_string("^[_0-9a-zA-Z]$")
  lexer.chr0
  |> option.map(fn(c) { regex.check(with: re, content: c) })
  |> option.unwrap(or: False)
}

// advance the stream and emit a token
fn eat_single_char(lexer: Lexer, ty: Token) -> Lexer {
  let token_start = get_pos(lexer)
  let assert #(Some(_), lexer) = next_char(lexer)
  let token_end = get_pos(lexer)
  emit(lexer, #(token_start, ty, token_end))
}

// Helper function to go to the next character coming up.
fn next_char(lexer: Lexer) -> #(Option(String), Lexer) {
  let c = lexer.chr0
  let #(nxt, lexer) = case iterator.step(lexer.chars) {
    iterator.Next(#(c, loc), chars) -> {
      #(Some(c), Lexer(..lexer, chars: chars, loc0: lexer.loc1, loc1: loc))
    }
    iterator.Done -> {
      #(None, Lexer(..lexer, loc0: lexer.loc1, loc1: lexer.loc1 + 1))
    }
  }
  #(c, Lexer(..lexer, chr0: lexer.chr1, chr1: nxt))
}

// Helper function to retrieve the current position.
fn get_pos(lexer: Lexer) -> Int {
  lexer.loc0
}

// Helper function to emit a lexed token to the queue of tokens.
fn emit(lexer: Lexer, spanned: Spanned) -> Lexer {
  Lexer(..lexer, pending: queue.push_back(lexer.pending, spanned))
}

pub fn iterator(lexer: Lexer) -> Iterator(LexResult) {
  let yield = fn(lexer: Lexer) {
    let #(res, lexer) = inner_next(lexer)
    case res {
      Ok(#(_, token.EndOfFile, _)) -> iterator.Done
      res -> iterator.Next(res, lexer)
    }
  }
  iterator.unfold(lexer, yield)
}
