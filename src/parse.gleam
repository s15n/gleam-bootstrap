// Gleam Parser
//
// Terminology:
//   Expression Unit:
//     Essentially a thing that goes between operators.
//     Int, Bool, function call, "{" expression-sequence "}", case x {}, ..etc
//
//   Expression:
//     One or more Expression Units separated by an operator
//
//   Binding:
//     (let|let assert|use) name (:TypeAnnotation)? = Expression
//
//   Expression Sequence:
//     * One or more Expressions
//     * A Binding followed by at least one more Expression Sequences
//
// Naming Conventions:
//   parse_x
//      Parse a specific part of the grammar, not erroring if it cannot.
//      Generally returns `Result<Option<A>, ParseError>`, note the inner Option
//
//   expect_x
//      Parse a generic or specific part of the grammar, erroring if it cannot.
//      Generally returns `Result<A, ParseError>`, note no inner Option
//
//   maybe_x
//      Parse a generic part of the grammar. Returning `None` if it cannot.
//      Returns `Some(x)` and advances the token stream if it can.
//
// Operator Precedence Parsing:
//   Needs to take place in expressions and in clause guards.
//   It is accomplished using the Simple Precedence Parser algorithm.
//   See: https://en.wikipedia.org/wiki/Simple_precedence_parser
//
//   It relies or the operator grammar being in the general form:
//   e ::= expr op expr | expr
//   Which just means that exprs and operators always alternate, starting with an expr
//
//   The gist of the algorithm is:
//   Create 2 stacks, one to hold expressions, and one to hold un-reduced operators.
//   While consuming the input stream, if an expression is encountered add it to the top
//   of the expression stack. If an operator is encountered, compare its precedence to the
//   top of the operator stack and perform the appropriate action, which is either using an
//   operator to reduce 2 expressions on the top of the expression stack or put it on the top
//   of the operator stack. When the end of the input is reached, attempt to reduce all of the
//   expressions down to a single expression(or no expression) using the remaining operators
//   on the operator stack. If there are any operators left, or more than 1 expression left
//   this is a syntax error. But the implementation here shouldn't need to handle that case
//   as the outer parser ensures the correct structure.
//

import gleam/bool.{guard}
import gleam/int
import gleam/iterator.{type Iterator}
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/order
import gleam/pair
import gleam/queue.{type Queue}
import gleam/result
import gleam/string

import ast.{type SrcSpan, SrcSpan}
import parse/error.{
  type LexicalError, type ParseError, type ParseErrorType, ParseError,
}
import parse/extra.{type ModuleExtra, ModuleExtra}
import parse/lexer.{type LexResult, type Spanned}
import parse/token.{type Token}

import gleam/io

pub type Parsed {
  Parsed(module: UntypedModule, extra: ModuleExtra)
}

// TODO
type UntypedModule =
  Nil

/// We use this to keep track of the `@internal` annotation for top level
/// definitions. Instead of using just a boolean we want to keep track of the
/// source position of the annotation in case it is present. This way we can
/// report a better error message highlighting the annotation in case it is
/// used on a private definition (it doesn't make sense to mark something
/// private as internal):
///
/// ```txt
/// @internal
/// ^^^^^^^^^ we first get to the annotation
/// fn wibble() {}
/// ^^ and only later discover it's applied on a private definition
///    so we have to keep track of the attribute's position to highlight it
///    in the resulting error message.
/// ```
type InternalAttribute {
  // default
  Missing
  Present(SrcSpan)
}

type Attributes {
  Attributes(
    target: Option(Target),
    deprecated: Deprecation,
    external_erlang: Option(#(String, String)),
    external_javascript: Option(#(String, String)),
    internal: InternalAttribute,
  )
}

// TODO
type Target =
  Nil

// TODO
type Deprecation =
  Nil

fn attributes_has_function_only(attributes: Attributes) -> Bool {
  case attributes {
    Attributes(external_erlang: Some(_), ..)
    | Attributes(external_javascript: Some(_), ..) -> True
    _ -> False
  }
}

//
// Public Interface
//
pub fn parse_module(source: String) -> Result(Parsed, ParseError) {
  let parser =
    lexer.make_tokenizer(source)
    |> lexer.iterator
    |> parser_new
  let #(res, parser) = inner_parse_module(parser)
  case res {
    Ok(parsed) -> Ok(Parsed(..parsed, extra: parser.extra))
    Error(err) -> Error(err)
  }
  //use parsed, parser <- try(inner_parse_module(parser))
  //Parsed(..parsed, extra: parser.extra)
}

//
// Test Interface
//
pub fn parse_statement_sequence(
  source: String,
) -> Result(List(ast.UntypedStatement), ParseError) {
  let parser =
    lexer.make_tokenizer(source)
    |> lexer.iterator
    |> parser_new

  let #(res, parser) = parse_statement_seq(parser)
  let #(res, _parser) = ensure_no_errors_or_remaining_input(parser, res)
  case res {
    Ok(Some(#(e, _))) -> Ok(e)
    Ok(_) -> parse_error(error.ExpectedExpr, SrcSpan(0, 0))
    Error(err) -> Error(err)
  }
  //let #(expr, parser) = parse_statement_seq(parser)
  //use expr, _parser <- try(ensure_no_errors_or_remaining_input(parser, expr))
  //case expr {
  //  Some(#(e, _)) -> Ok(e)
  //  _ -> parse_error(error.ExpectedExpr, SrcSpan(0, 0))
  //}
}

//
// Test Interface
//
pub fn parse_const_value(
  source: String,
) -> Result(Constant(Nil, Nil), ParseError) {
  let parser =
    lexer.make_tokenizer(source)
    |> lexer.iterator
    |> parser_new

  let #(res, parser) = inner_parse_const_value(parser)
  let #(res, _parser) = ensure_no_errors_or_remaining_input(parser, res)
  case res {
    // TODO: Ok(e)
    Ok(Some(e)) -> Ok(NilConstant)
    Ok(_) -> parse_error(error.ExpectedExpr, SrcSpan(0, 0))
    Error(err) -> Error(err)
  }
}

// TODO
pub type Constant(a, b) {
  NilConstant
}

//
// Parser
//
pub type Parser {
  Parser(
    tokens: Iterator(LexResult),
    lex_errors: Queue(LexicalError),
    tok0: Option(Spanned),
    tok1: Option(Spanned),
    extra: ModuleExtra,
    doc_comments: Queue(#(Int, String)),
  )
}

fn parser_new(input: Iterator(LexResult)) -> Parser {
  Parser(
    tokens: input,
    lex_errors: queue.new(),
    tok0: None,
    tok1: None,
    extra: extra.module_extra_new(),
    doc_comments: queue.new(),
  )
  |> advance
  |> advance
}

fn inner_parse_module(parser: Parser) -> #(Result(Parsed, ParseError), Parser) {
  todo
}

// The way the parser is currently implemented, it cannot exit immediately while advancing
// the token stream upon seeing a LexError. That is to avoid having to put `?` all over the
// place and instead we collect LexErrors in `self.lex_errors` and attempt to continue parsing.
// Once parsing has returned we want to surface an error in the order:
// 1) LexError, 2) ParseError, 3) More Tokens Left
fn ensure_no_errors_or_remaining_input(
  parser: Parser,
  res: Result(a, ParseError),
) -> #(Result(a, ParseError), Parser) {
  case ensure_no_errors(parser, res) {
    Error(err) -> #(Error(err), parser)
    Ok(parse_result) -> {
      let #(res, parser) = next_tok(parser)
      case res {
        // there are still more tokens
        Some(#(start, _, end)) -> {
          let expected = ["An import, const, type, or function."]
          #(
            Error(ParseError(
              error.UnexpectedToken(expected, hint: None),
              SrcSpan(start, end),
            )),
            parser,
          )
        }
        None -> #(Ok(parse_result), parser)
      }
    }
  }
}

// The way the parser is currently implemented, it cannot exit immediately
// while advancing the token stream upon seeing a LexError. That is to avoid
// having to put `?` all over the place and instead we collect LexErrors in
// `self.lex_errors` and attempt to continue parsing.
// Once parsing has returned we want to surface an error in the order:
// 1) LexError, 2) ParseError
fn ensure_no_errors(
  parser: Parser,
  parse_result: Result(a, ParseError),
) -> Result(a, ParseError) {
  case queue.pop_front(parser.lex_errors) {
    Ok(#(error, _)) -> {
      // Lex errors first
      let location = error.location
      parse_error(error.LexError(error), location)
    }
    Error(_) ->
      // Return any existing parse error
      parse_result
  }
}

fn parse_definition(
  parser: Parser,
) -> #(Result(Option(TargetedDefinition), ParseError), Parser) {
  todo
}

// TODO
type TargetedDefinition =
  Nil

//
// Parse Expressions
//

// examples:
//   unit
//   unit op unit
//   unit op unit pipe unit(call)
//   unit op unit pipe unit(call) pipe unit(call)
fn parse_expression(
  parser: Parser,
) -> #(Result(Option(ast.UntypedExpr), ParseError), Parser) {
  // uses the simple operator parser algorithm
  let #(res, #(opstack, estack, _, _), parser) =
    push_expression(parser, #([], [], 0, 0))
  case res {
    Ok(True) -> {
      let #(op, _, _) = handle_op(None, opstack, estack, do_reduce_expression)
      #(Ok(op), parser)
    }
    Ok(False) -> #(Ok(None), parser)
    Error(err) -> #(Error(err), parser)
  }
}

// Loop for function above
fn push_expression(
  parser: Parser,
  meta: #(List(#(Spanned, Int)), List(Nil), Int, Int),
) -> #(
  Result(Bool, ParseError),
  #(List(#(Spanned, Int)), List(Nil), Int, Int),
  Parser,
) {
  let #(res, parser) = parse_expression_unit(parser)
  let #(opstack, estack, last_op_start, last_op_end) = meta
  case res {
    Ok(Some(unit)) -> {
      let estack = [unit, ..estack]
      case parser.tok0 {
        Some(#(op_s, t, op_e)) ->
          case precedence(t) {
            Some(p) -> {
              // Is Op
              let parser = advance(parser)
              let last_op_start = op_s
              let last_op_end = op_e
              let #(_, opstack, estack) =
                handle_op(
                  Some(#(#(op_s, t, op_e), p)),
                  opstack,
                  estack,
                  do_reduce_expression,
                )
              push_expression(parser, #(
                opstack,
                estack,
                last_op_start,
                last_op_end,
              ))
            }
            None -> {
              // Is not Op
              let parser = Parser(..parser, tok0: Some(#(op_s, t, op_e)))
              #(
                Ok(True),
                #(opstack, estack, last_op_start, last_op_end),
                parser,
              )
            }
          }
        None -> #(
          Ok(True),
          #(opstack, estack, last_op_start, last_op_end),
          parser,
        )
      }
    }
    Ok(None) if estack == [] -> #(Ok(False), meta, parser)
    Ok(None) -> #(
      parse_error(error.OpNakedRight, SrcSpan(last_op_start, last_op_end)),
      meta,
      parser,
    )
    Error(err) -> #(Error(err), meta, parser)
  }
}

fn parse_expression_unit_collapsing_single_value_blocks(
  parser: Parser,
) -> #(Result(Option(ast.UntypedExpr), ParseError), Parser) {
  use res, parser <- try(parse_expression_unit(parser))
  case res {
    Some(expr) -> #(Ok(Some(expr)), parser)
    None -> #(Ok(None), parser)
  }
}

// examples:
//   1
//   "one"
//   True
//   fn() { "hi" }
//   unit().unit().unit()
//   A(a.., label: tuple(1))
//   { expression_sequence }
fn parse_expression_unit(
  parser: Parser,
) -> #(Result(Option(ast.UntypedExpr), ParseError), Parser) {
  use res, parser <- try(case parser.tok0 {
    Some(#(start, token.String(value), end)) -> todo
    Some(#(start, token.Int(value), end)) -> {
      let parser = advance(parser)
      // UntypedExpr::Int(location: SrcSpan(start, end), value)
      #(Ok(Some(Nil)), parser)
    }
    Some(#(start, token.Float(value), end)) -> todo
    // var lower_name and UpName
    Some(#(start, token.Name(name), end))
    | Some(#(start, token.UpName(name), end)) -> {
      let parser = advance(parser)
      // UntypedExpr::Var(location: SrcSpan(start, end), name)
      #(Ok(Some(Nil)), parser)
    }
    Some(#(start, token.Todo, end)) -> todo
    Some(#(start, token.Panic, end)) -> todo
    Some(#(start, token.Hash, _)) -> todo
    // list
    Some(#(start, token.LeftSquare, _)) -> {
      let parser = advance(parser)
      use elements, parser <- try(series_of(
        parser,
        parse_expression,
        Some(token.Comma),
      ))

      // Parse an optional tail
      let #(loc, parser) = maybe_one(parser, token.DotDot)
      use #(tail, elements_after_tail, dot_dot_location), parser <- try(case
        loc
      {
        Some(loc) -> {
          let dot_dot_location = Some(loc)
          use tail, parser <- try(parse_expression(parser))

          let #(loc, parser) = maybe_one(parser, token.Comma)
          case loc {
            Some(_loc) -> {
              // See if there's a list of items after the tail,
              // like `[..wibble, wobble, wabble]`
              let #(elements_after_tail, parser) =
                series_of(parser, parse_expression, Some(token.Comma))
                |> pair.map_first(option.from_result)
              #(
                Ok(#(Some(tail), elements_after_tail, dot_dot_location)),
                parser,
              )
            }
            None -> #(Ok(#(Some(tail), None, dot_dot_location)), parser)
          }
        }
        None -> #(Ok(#(None, None, None)), parser)
      })

      use #(_, end), parser <- try(expect_one(parser, token.RightSquare))

      case dot_dot_location, tail, elements, elements_after_tail {
        // Return errors for malformed lists
        Some(#(start, end)), None, _, _ -> #(
          parse_error(error.ListSpreadWithoutTail, SrcSpan(start, end)),
          parser,
        )
        _, Some(_), [], _ -> #(
          parse_error(error.ListSpreadWithoutElements, SrcSpan(start, end)),
          parser,
        )
        Some(#(start, _)), Some(tail), [_, ..], Some(_) -> #(
          // TODO: tail.location().end
          parse_error(error.ListSpreadFollowedByElements, SrcSpan(start, 0)),
          parser,
        )
        _, _, [_, ..], Some(_) -> #(
          parse_error(error.ListSpreadFollowedByElements, SrcSpan(start, end)),
          parser,
        )
        _, _, _, _ -> #(Ok(Some(Nil)), parser)
        // TODO: UntypedExpr::List(location: SrcSpan(start, end), elements, tail)
      }
    }
    // BitArray
    Some(#(start, token.LtLt, _)) -> todo
    Some(#(start, token.Fn, _)) -> todo
    // expression block  "{" "}"
    Some(#(start, token.LeftBrace, _)) -> todo
    // case
    Some(#(start, token.Case, case_end)) -> todo
    // helpful error on possibly trying to group with "(" ")"
    Some(#(start, token.LeftParen, _)) -> todo
    // Boolean negation
    Some(#(start, token.Bang, _)) -> todo
    // Int negation
    Some(#(start, token.Minus, _)) -> todo
    // if it reaches this code block, there must be no "let" or "assert" at the beginning of the expression
    Some(#(start, token.Equal, end)) -> todo
    Some(#(start, token.Colon, end)) -> todo
    tok0 -> #(Ok(None), Parser(..parser, tok0: tok0))
  })
  case res {
    Some(expr) -> {
      // field access and call can stack up
      // (loop)

      #(Ok(Some(expr)), parser)
    }
    None -> #(Ok(None), parser)
  }
}

// A `use` expression
// use <- function
// use <- function()
// use <- function(a, b)
// use <- module.function(a, b)
// use a, b, c <- function(a, b)
// use a, b, c, <- function(a, b)
fn parse_use(
  parser: Parser,
  start: Int,
  end: Int,
) -> #(Result(ast.UntypedStatement, ParseError), Parser) {
  todo
}

fn parse_use_assignment(
  parser: Parser,
) -> #(Result(Option(UseAssignment), ParseError), Parser) {
  todo
}

// TODO
type UseAssignment =
  Nil

// An assignment, with `let` already consumed
fn parse_assignment(
  parser: Parser,
  start: Int,
) -> #(Result(ast.UntypedStatement, ParseError), Parser) {
  let kind = case parser.tok0 {
    Some(#(assert_start, token.Assert, assert_end)) -> todo
    _ -> ast.LetAssignment
  }
  use res, parser <- try(parse_pattern(parser))
  case res {
    Some(pattern) -> {
      use annotation, parser <- try(parse_type_annotation(parser, token.Colon))
      use #(eq_s, eq_e), parser <- try(
        maybe_one(parser, token.Equal)
        |> pair.map_first(fn(opt) {
          option.to_result(
            opt,
            ParseError(
              error: error.ExpectedEqual,
              // TODO: pattern.location().start|end
              location: SrcSpan(0, 0),
            ),
          )
        }),
      )
      use value, parser <- try(
        parse_expression(parser)
        |> pair.map_first(fn(res) {
          case res {
            Ok(Some(value)) -> Ok(value)
            Ok(None) ->
              Error(ParseError(error.ExpectedValue, SrcSpan(eq_s, eq_e)))
            Error(err) -> Error(err)
          }
        }),
      )
      #(
        Ok(
          ast.AssignmentStmt(ast.Assignment(
            // TODO: value.location().end
            location: SrcSpan(start, 0),
            value: value,
            pattern: pattern,
            annotation: annotation,
            kind: kind,
          )),
        ),
        parser,
      )
    }
    None -> {
      // DUPE: 62884
      next_tok_unexpected(parser, ["A pattern"])
    }
  }
}

// fn parse_statement_seq(
//   parser: Parser,
// ) -> #(Result(Option(#(Queue(ast.UntypedStatement), Int)), ParseError), Parser) {
//   let #(res, _, end, parser) = push_statement(parser, queue.new(), None, 0)
//   case res {
//     Ok(statements) ->
//       case queue.is_empty(statements) {
//         True -> #(Ok(None), parser)
//         False -> #(Ok(Some(#(statements, end))), parser)
//       }
//     Error(err) -> #(Error(err), parser)
//   }
// }

// examples:
//   expr
//   expr expr..
//   expr assignment..
//   assignment
//   assignment expr..
//   assignment assignment..
fn parse_statement_seq(
  parser: Parser,
) -> #(Result(Option(#(List(ast.UntypedStatement), Int)), ParseError), Parser) {
  let yield = fn(prev) -> Result(
    iterator.Step(#(ast.UntypedStatement, Int), #(Parser, Option(Int))),
    ParseError,
  ) {
    let #(parser, start) = prev
    let #(res, parser) = parse_statement(parser)
    case res {
      Error(err) -> Error(err)
      Ok(Some(statement)) -> {
        let location = ast.untyped_statement_location(statement)
        let start = case start {
          None -> Some(location.start)
          _ -> start
        }
        let end = location.end
        Ok(iterator.Next(#(statement, end), #(parser, start)))
      }
      Ok(_) -> Ok(iterator.Done)
    }
  }
  let reduce = fn(acc, item) -> Result(
    #(List(ast.UntypedStatement), Int),
    ParseError,
  ) {
    let #(statements, _) = acc
    case item {
      Ok(#(statement, end)) -> Ok(#([statement, ..statements], end))
      Error(err) -> Error(err)
    }
  }
  let res =
    try_unfold(#(parser, None), yield)
    |> iterator.try_fold(#([], 0), reduce)
  case res {
    Ok(#(statements_rev, end)) ->
      case statements_rev {
        [] -> #(Ok(None), parser)
        statements_rev -> #(
          Ok(Some(#(list.reverse(statements_rev), end))),
          parser,
        )
      }
    Error(err) -> #(Error(err), parser)
  }
}

// // Loop for function above
// fn push_statement(
//   parser: Parser,
//   statements: Queue(ast.UntypedStatement),
//   start: Option(Int),
//   end: Int,
// ) -> #(
//   Result(Queue(ast.UntypedStatement), ParseError),
//   Option(Int),
//   Int,
//   Parser,
// ) {
//   let #(res, parser) = parse_statement(parser)
//   case res {
//     Error(err) -> #(Error(err), start, end, parser)
//     Ok(Some(statement)) -> {
//       let location = ast.untyped_statement_location(statement)
//       let start = case start {
//         None -> Some(location.start)
//         _ -> start
//       }
//       let end = location.end
//       let statements = queue.push_back(statements, statement)
//       push_statement(parser, statements, start, end)
//     }
//     Ok(_) -> #(Ok(statements), start, end, parser)
//   }
// }

fn parse_statement(
  parser: Parser,
) -> #(Result(Option(ast.UntypedStatement), ParseError), Parser) {
  case parser.tok0 {
    Some(#(start, token.Use, end)) -> {
      let #(res, parser) =
        parser
        |> advance
        |> parse_use(start, end)
      case res {
        Ok(statement) -> #(Ok(Some(statement)), parser)
        Error(err) -> #(Error(err), parser)
      }
    }
    Some(#(start, token.Let, _)) -> {
      let #(res, parser) =
        parser
        |> advance
        |> parse_assignment(start)
      case res {
        Ok(statement) -> #(Ok(Some(statement)), parser)
        Error(err) -> #(Error(err), parser)
      }
    }
    token -> {
      let #(res, parser) =
        Parser(..parser, tok0: token)
        |> parse_expression
      case res {
        Ok(Some(expr)) -> #(Ok(Some(ast.ExpressionStmt(expr))), parser)
        Ok(None) -> #(Ok(None), parser)
        Error(err) -> #(Error(err), parser)
      }
    }
  }
}

fn parse_block(
  parser: Parser,
  start: Int,
) -> #(Result(ast.UntypedExpr, ParseError), Parser) {
  todo
}

// The left side of an "=" or a "->"
fn parse_pattern(
  parser: Parser,
) -> #(Result(Option(ast.UntypedPattern), ParseError), Parser) {
  let #(res, parser) = case parser.tok0 {
    // Pattern::Var or Pattern::Constructor start
    Some(#(start, token.Name(name), end)) -> {
      let parser = advance(parser)

      // A variable is not permitted on the left hand side of a `<>`
      use <- guard(
        when: case parser.tok0 {
          Some(#(_, token.LtGt, _)) -> True
          _ -> False
        },
        return: #(
          concat_pattern_variable_left_hand_side_error(start, end),
          parser,
        ),
      )

      let #(tok, parser) = maybe_one(parser, token.Dot)
      case tok {
        Some(_) -> {
          // We're doing this to get a better error message instead of a generic
          // `I was expecting a type`, you can have a look at this issue to get
          // a better idea: https://github.com/gleam-lang/gleam/issues/2841.
          let #(res, parser) =
            expect_constructor_pattern(parser, Some(#(start, name, end)))
          case res {
            Ok(res) -> #(Ok(Some(res)), parser)
            Error(ParseError(location: SrcSpan(end, ..), ..)) -> #(
              parse_error(error.InvalidModuleTypePattern, SrcSpan(start, end)),
              parser,
            )
          }
        }
        _ ->
          case name {
            "true" | "false" -> #(
              parse_error(error.LowcaseBooleanPattern, SrcSpan(start, end)),
              parser,
            )
            _ -> #(
              Ok(
                Some(ast.VariablePat(
                  location: SrcSpan(start, end),
                  name: name,
                  type_: Nil,
                )),
              ),
              parser,
            )
          }
      }
    }
    // Constructor
    Some(#(start, token.UpName(..) as token, end)) -> todo
    Some(#(start, token.DiscardName(name), end)) -> todo
    Some(#(start, token.String(value), end)) -> todo
    Some(#(start, token.Int(value), end)) -> todo
    Some(#(start, token.Float(value), end)) -> todo
    Some(#(start, token.Hash, _)) -> todo
    // BitArray
    Some(#(start, token.LtLt, _)) -> todo
    // List
    Some(#(start, token.LeftSquare, _)) -> todo
    // No pattern
    tok0 -> {
      #(Ok(None), Parser(..parser, tok0: tok0))
    }
  }
  case res {
    Ok(Some(pattern)) ->
      case parser.tok0 {
        Some(#(_, token.As, _)) -> {
          let parser = advance(parser)
          use #(start, name, end), parser <- try(expect_name(parser))
          #(
            Ok(
              Some(ast.AssignPat(
                name: name,
                location: SrcSpan(start, end),
                pattern: pattern,
              )),
            ),
            parser,
          )
        }
        _ -> #(Ok(Some(pattern)), parser)
      }
    res -> #(res, parser)
  }
}

// examples:
//   pattern -> expr
//   pattern, pattern if -> expr
//   pattern, pattern | pattern, pattern if -> expr
fn parse_case_clause(
  parser: Parser,
) -> #(Result(UntypedClause, ParseError), Parser) {
  todo
}

// TODO
type UntypedClause =
  Nil

fn parse_patterns(
  parser: Parser,
) -> #(Result(List(ast.UntypedPattern), ParseError), Parser) {
  todo
}

// examples:
//   if a
//   if a < b
//   if a < b || b < c
fn parse_case_clause_guard(
  parser: Parser,
  nested: Bool,
) -> #(Result(Option(UntypedClauseGuard), ParseError), Parser) {
  todo
}

// TODO
type UntypedClauseGuard =
  Nil

// examples
// a
// 1
// a.1
// { a }
// a || b
// a < b || b < c
fn parse_case_clause_guard_unit(
  parser: Parser,
) -> #(Result(Option(UntypedClauseGuard), ParseError), Parser) {
  todo
}

// examples:
//   UpName( args )
fn expect_constructor_pattern(
  parser: Parser,
  module: Option(#(Int, String, Int)),
) -> #(Result(ast.UntypedPattern, ParseError), Parser) {
  todo
}

// examples:
//   ( args )
fn parse_constructor_pattern_args(
  parser: Parser,
  upname_end: Int,
) -> #(
  Result(#(List(ast.CallArg(ast.UntypedPattern)), Bool, Int), ParseError),
  Parser,
) {
  todo
}

// examples:
//   a: <pattern>
//   <pattern>
fn parse_constructor_pattern_arg(
  parser: Parser,
) -> #(Result(Option(ast.CallArg(ast.UntypedPattern)), ParseError), Parser) {
  todo
}

// examples:
//   a: expr
fn parse_record_update_arg(
  parser: Parser,
) -> #(Result(Option(UntypedRecordUpdateArg), ParseError), Parser) {
  todo
}

// TODO
type UntypedRecordUpdateArg =
  Nil

//
// Parse Functions
//

// Starts after "fn"
//
// examples:
//   fn a(name: String) -> String { .. }
//   pub fn a(name name: String) -> String { .. }
fn parse_function(
  parser: Parser,
  start: Int,
  public: Bool,
  anonymous: Bool,
  attributes: Attributes,
) -> #(Result(Option(UntypedDefinition), ParseError), Parser) {
  todo
}

// TODO
type UntypedDefinition =
  Nil

fn publicity(
  parser: Parser,
  public: Bool,
  internal: InternalAttribute,
) -> #(Result(Publicity, ParseError), Parser) {
  todo
}

// TODO
type Publicity =
  Nil

// Parse a single function definition param
//
// examples:
//   _
//   a
//   a a
//   a _
//   a _:A
//   a a:A
fn parse_fn_param(
  parser: Parser,
  anonymous: Bool,
) -> #(Result(Option(UntypedArg), ParseError), Parser) {
  todo
}

// TODO
type UntypedArg =
  Nil

// Parse function call arguments, no parens
//
// examples:
//   _
//   expr, expr
//   a: _, expr
//   a: expr, _, b: _
fn parse_fn_args(
  parser: Parser,
) -> #(Result(List(ParserArg), ParseError), Parser) {
  todo
}

// TODO
type ParserArg =
  Nil

// Parse a single function call arg
//
// examples:
//   _
//   expr
//   a: _
//   a: expr
fn parse_fn_arg(
  parser: Parser,
) -> #(Result(Option(ParserArg), ParseError), Parser) {
  todo
}

//
// Parse Custom Types
//

// examples:
//   type A { A }
//   type A { A(String) }
//   type Box(inner_type) { Box(inner: inner_type) }
//   type NamedBox(inner_type) { Box(String, inner: inner_type) }
fn parse_custom_type(
  parser: Parser,
  start: Int,
  public: Bool,
  opaque_: Bool,
  attributes: Attributes,
) -> #(Result(Option(UntypedDefinition), ParseError), Parser) {
  todo
}

// examples:
//   A
//   A(one, two)
fn expect_type_name(
  parser: Parser,
) -> #(Result(#(Int, String, List(String), Int), ParseError), Parser) {
  todo
}

// examples:
//   *no args*
//   ()
//   (a, b)
fn parse_type_constructor_args(
  parser: Parser,
  start: Int,
) -> #(Result(#(List(RecordConstructorArg(Nil)), Int), ParseError), Parser) {
  todo
}

// TODO
type RecordConstructorArg(a) {
  NilRecordConstructorArg
}

//
// Parse Type Annotations
//

// examples:
//   :a
//   :Int
//   :Result(a, _)
//   :Result(Result(a, e), #(_, String))
fn parse_type_annotation(
  parser: Parser,
  start_token: Token,
) -> #(Result(Option(ast.TypeAst), ParseError), Parser) {
  let #(tok, parser) = maybe_one(parser, start_token)
  case tok {
    Some(#(start, end)) -> {
      let #(type_, parser) = parse_type(parser)
      case type_ {
        Ok(None) -> #(
          parse_error(error.ExpectedType, SrcSpan(start, end)),
          parser,
        )
        type_ -> #(type_, parser)
      }
    }
    None -> #(Ok(None), parser)
  }
}

// Parse the type part of a type annotation, same as `parse_type_annotation` minus the ":"
fn parse_type(
  parser: Parser,
) -> #(Result(Option(ast.TypeAst), ParseError), Parser) {
  case parser.tok0 {
    // Type hole
    Some(#(start, token.DiscardName(name), end)) -> todo
    // Tuple
    Some(#(start, token.Hash, end)) -> todo
    // Function
    Some(#(start, token.Fn, end)) -> todo
    // Constructor function
    Some(#(start, token.UpName(name), end)) -> todo
    // Constructor Module or type Variable
    Some(#(start, token.Name(mod_name), end)) -> todo
    tok0 -> #(Ok(None), Parser(..parser, tok0: tok0))
  }
}

// Parse the '( ... )' of a type name
fn parse_type_name_finish(
  parser: Parser,
  start: Int,
  module: Option(String),
  name: String,
  end: Int,
) -> #(Result(Option(ast.TypeAst), ParseError), Parser) {
  todo
}

// For parsing a comma separated "list" of types, for tuple, constructor, and function
fn parse_types(
  parser: Parser,
) -> #(Result(List(ast.TypeAst), ParseError), Parser) {
  todo
}

//
// Parse Imports
//

// examples:
//   import a
//   import a/b
//   import a/b.{c}
//   import a/b.{c as d} as e
fn parse_import(
  parser: Parser,
  import_start: Int,
) -> #(Result(Option(UntypedDefinition), ParseError), Parser) {
  todo
}

// [Name (as Name)? | UpName (as Name)? ](, [Name (as Name)? | UpName (as Name)?])*,?
fn parse_unqualified_imports(
  parser: Parser,
) -> #(Result(ParsedUnqualifiedImports, ParseError), Parser) {
  todo
}

// TODO
type ParsedUnqualifiedImports =
  Nil

//
// Parse Constants
//

// examples:
//   const a = 1
//   const a:Int = 1
//   pub const a:Int = 1
fn parse_module_const(
  parser: Parser,
  public: Bool,
  attributes: Attributes,
) -> #(Result(Option(UntypedDefinition), ParseError), Parser) {
  todo
}

// examples:
//   1
//   "hi"
//   True
//   [1,2,3]
fn inner_parse_const_value(
  parser: Parser,
) -> #(Result(Option(UntypedConstant), ParseError), Parser) {
  todo
}

// TODO
type UntypedConstant =
  Nil

// Parse the '( .. )' of a const type constructor
fn parse_const_record_finish(
  parser: Parser,
  start: Int,
  module: Option(String),
  name: String,
  end: Int,
) -> #(Result(Option(UntypedConstant), ParseError), Parser) {
  todo
}

// examples:
//  name: const
//  const
fn parse_const_record_arg(
  parser: Parser,
) -> #(Result(Option(ast.CallArg(UntypedConstant)), ParseError), Parser) {
  todo
}

//
// Bit String parsing
//

// ...

//
// Parse Helpers
//

// Expect a particular token, advances the token stream
fn expect_one(
  parser: Parser,
  wanted: Token,
) -> #(Result(#(Int, Int), ParseError), Parser) {
  let #(loc, parser) = maybe_one(parser, wanted)
  case loc {
    Some(#(start, end)) -> #(Ok(#(start, end)), parser)
    None -> next_tok_unexpected(parser, [string.inspect(wanted)])
  }
}

// Expect a particular token after having parsed a series, advances the token stream
// Used for giving a clearer error message in cases where the series item is what failed to parse
fn expect_one_following_series(
  parser: Parser,
  wanted: Token,
  series: String,
) -> #(Result(#(Int, Int), ParseError), Parser) {
  todo
}

// Expect a Name else a token dependent helpful error
fn expect_name(
  parser: Parser,
) -> #(Result(#(Int, String, Int), ParseError), Parser) {
  todo
}

fn expect_assign_name(
  parser: Parser,
) -> #(Result(#(Int, AssignName, Int), ParseError), Parser) {
  todo
}

// TODO
type AssignName =
  Nil

// Expect an UpName else a token dependent helpful error
fn expect_upname(
  parser: Parser,
) -> #(Result(#(Int, String, Int), ParseError), Parser) {
  todo
}

// Expect a target name. e.g. `javascript` or `erlang`
fn expect_target(parser: Parser) -> #(Result(Target, ParseError), Parser) {
  todo
}

// Expect a String else error
fn expect_string(
  parser: Parser,
) -> #(Result(#(Int, String, Int), ParseError), Parser) {
  todo
}

fn peek_tok1(parser: Parser) -> #(Option(Token), Parser) {
  todo
}

// If the next token matches the requested, consume it and return (start, end)
fn maybe_one(parser: Parser, token: Token) -> #(Option(#(Int, Int)), Parser) {
  case parser.tok0 {
    Some(#(s, t, e)) if t == token -> #(Some(#(s, e)), advance(parser))
    tok0 -> #(None, Parser(..parser, tok0: tok0))
  }
}

// Parse a series by repeating a parser, and possibly a separator
fn series_of(
  parser: Parser,
  parse parser_fn: fn(Parser) -> #(Result(Option(a), ParseError), Parser),
  by separator: Option(Token),
) -> #(Result(List(a), ParseError), Parser) {
  let yield = fn(parser) {
    let #(res, parser) = parser_fn(parser)
    case res {
      Ok(Some(item)) -> {
        case separator {
          Some(sep) -> {
            let #(loc, parser) = maybe_one(parser, sep)
            case loc {
              None -> Ok(iterator.Done)
              Some(_) -> {
                // Helpful error if extra separator
                let #(loc, parser) = maybe_one(parser, sep)
                case loc {
                  Some(#(start, end)) ->
                    parse_error(error.ExtraSeparator, SrcSpan(start, end))
                  None -> Ok(iterator.Next(item, parser))
                }
              }
            }
          }
          None -> Ok(iterator.Next(item, parser))
        }
      }
      Ok(None) -> Ok(iterator.Done)
      Error(err) -> Error(err)
    }
  }
  let items =
    try_unfold(parser, yield)
    |> try_to_list
  #(items, parser)
}

// If next token is a Name, consume it and return relevant info, otherwise, return none
fn maybe_name(parser: Parser) -> #(Option(#(Int, String, Int)), Parser) {
  todo
}

// if next token is an UpName, consume it and return relevant info, otherwise, return none
fn maybe_upname(parser: Parser) -> #(Option(#(Int, String, Int)), Parser) {
  todo
}

// if next token is a DiscardName, consume it and return relevant info, otherwise, return none
fn maybe_discard_name(parser: Parser) -> #(Option(#(Int, String, Int)), Parser) {
  todo
}

// Error on the next token or EOF
fn next_tok_unexpected(
  parser: Parser,
  expected: List(String),
) -> #(Result(a, ParseError), Parser) {
  let #(next, parser) = next_tok(parser)
  case next {
    None -> #(parse_error(error.UnexpectedEof, SrcSpan(0, 0)), parser)
    Some(#(start, _, end)) -> #(
      parse_error(
        error.UnexpectedToken(expected, hint: None),
        SrcSpan(start, end),
      ),
      parser,
    )
  }
}

// Moves the token stream forward
fn advance(parser: Parser) -> Parser {
  let #(_, parser) = next_tok(parser)
  parser
}

// Moving the token stream forward
// returns old tok0
fn next_tok(parser: Parser) -> #(Option(Spanned), Parser) {
  let #(spanned, _, parser) = next_tok_step(parser, parser.tok0, None)
  #(spanned, parser)
}

fn next_tok_step(
  parser: Parser,
  spanned: Option(Spanned),
  previous_newline: Option(Int),
) -> #(Option(Spanned), Option(Int), Parser) {
  case iterator.step(parser.tokens) {
    iterator.Next(next, rest) ->
      case next {
        Ok(token) ->
          case token {
            // gather and skip extra
            #(start, token.CommentNormal, end) -> {
              let parser =
                Parser(
                  ..parser,
                  extra: ModuleExtra(
                    ..parser.extra,
                    comments: queue.push_back(
                      parser.extra.comments,
                      SrcSpan(start, end),
                    ),
                  ),
                )
              next_tok_step(parser, spanned, None)
            }
            #(start, token.CommentDoc(content), end) -> {
              let parser =
                Parser(
                  ..parser,
                  doc_comments: queue.push_back(parser.doc_comments, #(
                    start,
                    content,
                  )),
                  extra: ModuleExtra(
                    ..parser.extra,
                    doc_comments: queue.push_back(
                      parser.extra.doc_comments,
                      SrcSpan(start, end),
                    ),
                  ),
                )
              next_tok_step(parser, spanned, None)
            }
            #(start, token.CommentModule, end) -> {
              let parser =
                Parser(
                  ..parser,
                  extra: ModuleExtra(
                    ..parser.extra,
                    module_comments: queue.push_back(
                      parser.extra.module_comments,
                      SrcSpan(start, end),
                    ),
                  ),
                )
              next_tok_step(parser, spanned, None)
            }
            #(start, token.NewLine, _) -> {
              let parser =
                Parser(
                  ..parser,
                  extra: ModuleExtra(
                    ..parser.extra,
                    new_lines: queue.push_back(parser.extra.new_lines, start),
                  ),
                )
              // If the previous token is a newline as well that means we
              // have run into an empty line.
              // TODO
              let parser = case previous_newline {
                Some(start) -> {
                  // We increase the byte position so that newline's start
                  // doesn't overlap with the previous token's end.
                  let parser =
                    Parser(
                      ..parser,
                      extra: ModuleExtra(
                        ..parser.extra,
                        new_lines: queue.push_back(
                          parser.extra.new_lines,
                          start + 1,
                        ),
                      ),
                    )
                  parser
                }
                _ -> parser
              }
              next_tok_step(parser, spanned, Some(start))
            }
            token -> #(
              spanned,
              previous_newline,
              Parser(
                ..parser,
                tok0: parser.tok1,
                tok1: Some(token),
                tokens: rest,
              ),
            )
          }
        // die on lex error
        Error(err) -> #(
          spanned,
          previous_newline,
          Parser(
            ..parser,
            lex_errors: queue.push_back(parser.lex_errors, err),
            tok0: parser.tok1,
            tok1: None,
            tokens: rest,
          ),
        )
      }
    iterator.Done -> #(
      spanned,
      previous_newline,
      Parser(..parser, tok0: parser.tok1, tok1: None, tokens: iterator.empty()),
    )
  }
}

fn take_documentation(parser: Parser, until: Int) -> #(Option(String), Parser) {
  todo
}

// TODO
//fn parse_attributes(
//  parser: Parser,
//  attributes: Attributes, <- mut
//) -> #(Result(Option(SrcSpan), ParseError), Parser) {
//  todo
//}

// TODO
//fn parse_attribute(
//  parser: Parser,
//  attributes: Attributes, <- mut
//) -> #(Result(Int, ParseError), Parser) {
//  todo
//}

// ...

// TODO
fn concat_pattern_variable_left_hand_side_error(
  start: Int,
  end: Int,
) -> Result(a, ParseError) {
  Error(ParseError(
    error: error.ConcatPatternVariableLeftHandSide,
    location: SrcSpan(start, end),
  ))
}

// Operator Precedence Parsing
//
// Higher number means higher precedence.
// All operators are left associative.

// line 3129
/// Simple-Precedence-Parser, handle seeing an operator or end
fn handle_op(
  next_op: Option(#(Spanned, Int)),
  opstack: List(#(Spanned, Int)),
  estack: List(a),
  do_reduce: fn(Spanned, List(a)) -> List(a),
) -> #(Option(a), List(#(Spanned, Int)), List(a)) {
  case opstack, next_op {
    [], None ->
      case estack {
        [fin] -> #(Some(fin), [], [])
        [] -> #(None, [], [])
        _ -> panic as "Expression not fully reduced"
      }
    [], Some(op) -> #(None, [op], estack)
    [#(op, _), ..rest], None ->
      handle_op(None, rest, do_reduce(op, estack), do_reduce)
    [#(op, pl), ..rest], Some(#(opr, pr)) ->
      case int.compare(pl, pr) {
        // all ops are left associative
        order.Gt | order.Eq ->
          handle_op(Some(#(opr, pr)), rest, do_reduce(op, estack), do_reduce)
        order.Lt -> #(None, [#(opr, pr), #(op, pl), ..rest], estack)
      }
  }
}

// line 3176
fn precedence(t: Token) -> Option(Int) {
  case t {
    token.Pipe -> Some(6)
    _ ->
      t
      |> tok_to_binop
      |> option.map(ast.binop_precedence)
  }
}

fn tok_to_binop(t: Token) -> Option(ast.BinOp) {
  case t {
    token.VbarVbar -> Some(ast.BinOpOr)
    token.AmperAmper -> Some(ast.BinOpAnd)
    token.EqualEqual -> Some(ast.BinOpEq)
    token.NotEqual -> Some(ast.BinOpNotEq)
    token.Less -> Some(ast.BinOpLtInt)
    token.LessEqual -> Some(ast.BinOpLtEqInt)
    token.Greater -> Some(ast.BinOpGtInt)
    token.GreaterEqual -> Some(ast.BinOpGtEqInt)
    token.LessDot -> Some(ast.BinOpLtFloat)
    token.LessEqualDot -> Some(ast.BinOpLtEqFloat)
    token.GreaterDot -> Some(ast.BinOpGtFloat)
    token.GreaterEqualDot -> Some(ast.BinOpGtEqFloat)
    token.Plus -> Some(ast.BinOpAddInt)
    token.Minus -> Some(ast.BinOpSubInt)
    token.PlusDot -> Some(ast.BinOpAddFloat)
    token.MinusDot -> Some(ast.BinOpSubFloat)
    token.Percent -> Some(ast.BinOpRemainderInt)
    token.Star -> Some(ast.BinOpMultInt)
    token.StarDot -> Some(ast.BinOpMultFloat)
    token.Slash -> Some(ast.BinOpDivInt)
    token.SlashDot -> Some(ast.BinOpDivFloat)
    token.LtGt -> Some(ast.BinOpConcatenate)
    _ -> None
  }
}

// line 3211
/// Simple-Precedence-Parser, perform reduction for expression
fn do_reduce_expression(
  op: Spanned,
  estack: List(ast.UntypedExpr),
) -> List(ast.UntypedExpr) {
  case estack {
    [er, el, ..rest] -> [expr_op_reduction(op, el, er), ..rest]
    _ -> panic as "Tried to reduce without 2 expressions"
  }
}

// TODO
/// Simple-Precedence-Parser, perform reduction for clause guard
fn do_reduce_clause_guard() {
  todo
}

fn expr_op_reduction(
  op: Spanned,
  l: ast.UntypedExpr,
  r: ast.UntypedExpr,
) -> ast.UntypedExpr {
  case op {
    #(_, token.Pipe, _) -> {
      let expressions = case l {
        // UntypedExprPipeline(expressions) -> queue.push_back(expressions, r)
        _ -> queue.from_list([l, r])
      }
      //UntypedExprPipeline(expressions)
      Nil
    }
    #(_, tok, _) ->
      case tok_to_binop(tok) {
        Some(binop) -> Nil
        //UntypedExprBinOp(
        //  location: SrcSpan(untyped_expr_location(l).start, untyped_expr_location(r).end),
        //  name: binop,
        //  left: l,
        //  right: r,
        //)
        _ -> panic as "Token could not be converted to binop."
      }
  }
}

//
// Error Helpers
//
// line 3391
fn parse_error(
  error: ParseErrorType,
  location: SrcSpan,
) -> Result(a, ParseError) {
  Error(ParseError(error: error, location: location))
}

// Gleam helper
fn try(
  pair: #(Result(a, ParseError), Parser),
  fun: fn(a, Parser) -> #(Result(c, ParseError), Parser),
) -> #(Result(c, ParseError), Parser) {
  let #(res, parser) = pair
  case res {
    Ok(a) -> fun(a, parser)
    Error(err) -> #(Error(err), parser)
  }
}

// Gleam helper
fn try_unfold(
  from initial: a,
  with step: fn(a) -> Result(iterator.Step(b, a), c),
) {
  let regular_step = fn(prev) {
    case prev {
      None -> iterator.Done
      Some(prev) -> {
        let res = step(prev)
        case res {
          Ok(iterator.Next(next, acc)) -> iterator.Next(Ok(next), Some(acc))
          Ok(iterator.Done) -> iterator.Done
          Error(err) -> iterator.Next(Error(err), None)
        }
      }
    }
  }
  iterator.unfold(Some(initial), regular_step)
}

fn try_to_list(iter) {
  let reduce = fn(acc, item) {
    case item {
      Ok(item) -> Ok([item, ..acc])
      Error(err) -> Error(err)
    }
  }
  iter
  |> iterator.try_fold([], reduce)
  |> result.map(list.reverse)
}
