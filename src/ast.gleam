//// TODO

import gleam/option.{type Option}

//https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/ast.rs

// line 261
pub type TypeAst {
  TypeAstConstructor
  TypeAstFn
  TypeAstVar
  TypeAstTuple
  TypeAstHole
}

// line 872
pub type BinOp {
  // Boolean logic
  BinOpAnd
  BinOpOr

  // Equality
  BinOpEq
  BinOpNotEq

  // Order comparison
  BinOpLtInt
  BinOpLtEqInt
  BinOpLtFloat
  BinOpLtEqFloat
  BinOpGtEqInt
  BinOpGtInt
  BinOpGtEqFloat
  BinOpGtFloat

  // Maths
  BinOpAddInt
  BinOpAddFloat
  BinOpSubInt
  BinOpSubFloat
  BinOpMultInt
  BinOpMultFloat
  BinOpDivInt
  BinOpDivFloat
  BinOpRemainderInt

  // Strings
  BinOpConcatenate
}

pub fn binop_precedence(binop: BinOp) -> Int {
  // Ensure that this matches the other precedence function for guards
  case binop {
    BinOpOr -> 1

    BinOpAnd -> 2

    BinOpEq | BinOpNotEq -> 3

    BinOpLtInt
    | BinOpLtEqInt
    | BinOpLtFloat
    | BinOpLtEqFloat
    | BinOpGtEqInt
    | BinOpGtInt
    | BinOpGtEqFloat
    | BinOpGtFloat -> 4

    BinOpConcatenate -> 5

    // Pipe is 6
    BinOpAddInt | BinOpAddFloat | BinOpSubInt | BinOpSubFloat -> 7

    BinOpMultInt
    | BinOpMultFloat
    | BinOpDivInt
    | BinOpDivFloat
    | BinOpRemainderInt -> 8
  }
}

// line 1002
pub type CallArg(a) {
  CallArg(
    label: Option(String),
    location: SrcSpan,
    value: a,
    // This is true if this argument is given as the callback in a `use`
    // expression. In future it may also be true for pipes too. It is used to
    // determine if we should error if an argument without a label is given or
    // not, which is not permitted if the argument is given explicitly by the
    // programmer rather than implicitly by Gleam's syntactic sugar.
    implicit: Bool,
  )
}

// line 1311
pub type SrcSpan {
  SrcSpan(start: Int, end: Int)
}

// line 1342
pub type UntypedPattern =
  Pattern(Nil)

// line 1346
pub type Pattern(ty) {
  IntPat(location: SrcSpan, value: String)

  /// The creation of a variable.
  /// e.g. `assert [this_is_a_var, .._] = x`
  VariablePat(location: SrcSpan, name: String, type_: ty)

  /// A name given to a sub-pattern using the `as` keyword.
  /// e.g. `assert #(1, [_, _] as the_list) = x`
  AssignPat(name: String, location: SrcSpan, pattern: Pattern(ty))
}

// line 1597
pub type AssignmentKind {
  // let x = ...
  LetAssignment
  // let assert x = ...
  AssertAssignment(location: SrcSpan)
}

// line 1826
pub type Statement(ty, expr) {
  ExpressionStmt(expression: expr)
  AssignmentStmt(assignment: Assignment(ty, expr))
  UseStmt(use_: Use)
}

pub fn statement_location(statement: Statement(ty, expr)) -> SrcSpan {
  case statement {
    ExpressionStmt(expression) -> todo
    AssignmentStmt(assignment) -> assignment.location
    UseStmt(_) -> todo
  }
}

// line 1836
//pub type UntypedStatement =
//  Statement(Nil, untyped.Expr)

// line 1945
pub type Assignment(ty, expr) {
  Assignment(
    location: SrcSpan,
    value: expr,
    pattern: Pattern(ty),
    kind: AssignmentKind,
    annotation: Option(TypeAst),
  )
}

// TODO
type Use =
  Nil
