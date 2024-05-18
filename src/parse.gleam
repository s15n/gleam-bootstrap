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

import gleam/int
import gleam/iterator.{type Iterator}
import gleam/option.{type Option, None, Some}
import gleam/order
import gleam/queue.{type Queue}

import ast.{type SrcSpan, SrcSpan}
import parse/error.{
  type LexicalError, type ParseError, type ParseErrorType, ParseError,
}
import parse/lexer.{type LexResult, type Spanned}
import parse/token.{type Token}

import gleam/io

pub type Parsed {
  Parsed(module: UntypedModule, extra: ModuleExtra)
}

// TODO
type UntypedModule =
  Nil

// TODO
type ModuleExtra =
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
}

//
// Test Interface
//
pub fn parse_statement_sequence(
  source: String,
) -> Result(Queue(ast.UntypedStatement), ParseError) {
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
    lex_errors: List(LexicalError),
    tok0: Option(Spanned),
    tok1: Option(Spanned),
    extra: ModuleExtra,
    doc_comments: Queue(#(Int, String)),
  )
}

fn parser_new(input: Iterator(LexResult)) -> Parser {
  Parser(
    tokens: input,
    lex_errors: [],
    tok0: None,
    tok1: None,
    // TODO: ModuleExtra::new()
    extra: Nil,
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
  todo
}

// The way the parser is currently implemented, it cannot exit immediately
// while advancing the token stream upon seeing a LexError. That is to avoid
// having to put `?` all over the place and instead we collect LexErrors in
// `self.lex_errors` and attempt to continue parsing.
// Once parsing has returned we want to surface an error in the order:
// 1) LexError, 2) ParseError
fn ensure_no_errors(
  parser: Parser,
  res: Result(a, ParseError),
) -> #(Result(a, ParseError), Parser) {
  todo
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
  let #(res, parser) = parse_expression_unit(parser)
  case res {
    Error(err) -> #(Error(err), parser)
    Ok(Some(expr)) -> #(Ok(Some(expr)), parser)
    Ok(None) -> #(Ok(None), parser)
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
  let expr = case parser.tok0 {
    Some(#(start, token.String(value), end)) -> todo
    Some(#(start, token.Int(value), end)) -> {
      let parser = advance(parser)
      // UntypedExprInt(location: SrcSpan(start, end), value)
      Nil
    }
    // ...
    tok0 -> {
      io.debug(parser)
      io.debug(tok0)
      todo
    }
  }

  // field access and call can stack up
  // (loop)

  #(Ok(Some(expr)), parser)
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
  todo
}

// examples:
//   expr
//   expr expr..
//   expr assignment..
//   assignment
//   assignment expr..
//   assignment assignment..
fn parse_statement_seq(
  parser: Parser,
) -> #(Result(Option(#(Queue(ast.UntypedStatement), Int)), ParseError), Parser) {
  let #(res, _, end, parser) = push_statement(parser, queue.new(), None, 0)
  case res {
    Ok(statements) ->
      case queue.is_empty(statements) {
        True -> #(Ok(None), parser)
        False -> #(Ok(Some(#(statements, end))), parser)
      }
    Error(err) -> #(Error(err), parser)
  }
}

// Loop for function above
fn push_statement(
  parser: Parser,
  statements: Queue(ast.UntypedStatement),
  start: Option(Int),
  end: Int,
) -> #(
  Result(Queue(ast.UntypedStatement), ParseError),
  Option(Int),
  Int,
  Parser,
) {
  let #(res, parser) = parse_statement(parser)
  case res {
    Error(err) -> #(Error(err), start, end, parser)
    Ok(Some(statement)) -> {
      let location = ast.untyped_statement_location(statement)
      let start = case start {
        None -> Some(location.start)
        _ -> start
      }
      let end = location.end
      let statements = queue.push_back(statements, statement)
      push_statement(parser, statements, start, end)
    }
    Ok(_) -> #(Ok(statements), start, end, parser)
  }
}

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
) -> #(Result(Option(UntypedPattern), ParseError), Parser) {
  todo
}

// TODO
type UntypedPattern =
  Nil

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
) -> #(Result(List(UntypedPattern), ParseError), Parser) {
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
) -> #(Result(UntypedPattern, ParseError), Parser) {
  todo
}

// examples:
//   ( args )
fn parse_constructor_pattern_args(
  parser: Parser,
  upname_end: Int,
) -> #(
  Result(#(List(ast.CallArg(UntypedPattern)), Bool, Int), ParseError),
  Parser,
) {
  todo
}

// examples:
//   a: <pattern>
//   <pattern>
fn parse_constructor_pattern_arg(
  parser: Parser,
) -> #(Result(Option(ast.CallArg(UntypedPattern)), ParseError), Parser) {
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
  todo
}

// Parse the type part of a type annotation, same as `parse_type_annotation` minus the ":"
fn parse_type(
  parser: Parser,
) -> #(Result(Option(ast.TypeAst), ParseError), Parser) {
  todo
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
  todo
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
  todo
}

// Parse a series by repeating a parser, and possibly a separator
fn series_of(
  parser: Parser,
  parse parser_fn: fn(Parser) -> #(Result(Option(a), ParseError), Parser),
  by separator: Option(Token),
) -> #(Result(List(a), ParseError), Parser) {
  todo
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
  todo
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
              //let parser = Parser(..parser, extra: ModuleExtra(..parser.extra, comments: [SrcSpan(start, end), ..parser.extra.comments]))
              next_tok_step(parser, spanned, None)
            }
            #(start, token.CommentDoc(content), end) -> {
              //let parser = Parser(..parser, extra: ModuleExtra(..parser.extra, doc_comments: [SrcSpan(start, end), ..parser.extra.doc_comments]))
              let parser =
                Parser(
                  ..parser,
                  doc_comments: queue.push_back(parser.doc_comments, #(
                    start,
                    content,
                  )),
                )
              next_tok_step(parser, spanned, None)
            }
            #(start, token.CommentModule, end) -> {
              //let parser = Parser(..parser, extra: ModuleExtra(..parser.extra, module_comments: [SrcSpan(start, end), ..parser.extra.module_comments]))
              next_tok_step(parser, spanned, None)
            }
            #(start, token.NewLine, _) -> {
              //let parser = Parser(..parser, extra: ModuleExtra(..parser.extra, new_lines: [start, ..parser.extra.new_lines]))
              // If the previous token is a newline as well that means we
              // have run into an empty line.
              // TODO
              let parser = case previous_newline {
                Some(start) -> {
                  // We increase the byte position so that newline's start
                  // doesn't overlap with the previous token's end.
                  //let parser = Parser(..parser, extra: ModuleExtra(..parser.extra, new_lines: [start + 1, ..parser.extra.new_lines]))
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
            lex_errors: [err, ..parser.lex_errors],
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
fn concat_pattern_variable_left_hand_side_error() -> Nil {
  todo
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
