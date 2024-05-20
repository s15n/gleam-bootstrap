import gleam/option.{type Option}
import gleam/queue.{type Queue}

import ast.{type SrcSpan}
import build

pub type Expr {
  IntExpr(location: SrcSpan, value: String)
  FloatExpr(location: SrcSpan, value: String)
  StringExpr(location: SrcSpan, value: String)
  BlockExpr(location: SrcSpan, statements: List(Statement))
  VarExpr(location: SrcSpan, name: String)
  FnExpr(
    location: SrcSpan,
    arguments: List(ast.Arg(Nil)),
    body: List(Statement),
    return_annotation: Option(ast.TypeAst),
  )
  CaptureExpr(
    location: SrcSpan,
    arguments: List(ast.Arg(Nil)),
    body: List(Statement),
    return_annotation: Option(ast.TypeAst),
  )
  ListExpr(location: SrcSpan, elements: List(Expr), tail: Option(Expr))
  CallExpr(location: SrcSpan, fun: Expr, arguments: List(ast.CallArg(Expr)))
  BinOpExpr(location: SrcSpan, name: ast.BinOp, left: Expr, right: Expr)
  // Guaranteed to have at least one element
  PipeLineExpr(expressions: Queue(Expr))
  CaseExpr(location: SrcSpan, subjects: List(Expr), clauses: List(Clause))
  FieldAccessExpr(
    // This is the location of the whole record and field
    //   user.name
    //   ^^^^^^^^^
    location: SrcSpan,
    // This is the location of just the field access
    //   user.name
    //       ^^^^^
    label_location: SrcSpan,
    label: String,
    container: Expr,
  )
  TupleExpr(location: SrcSpan, elements: List(Expr))
  TupleIndexExpr(location: SrcSpan, index: Int, tuple: Expr)
  TodoExpr(kind: ast.TodoKind, location: SrcSpan, message: Option(Expr))
  PanicExpr(location: SrcSpan, message: Expr)
  BitArrayExpr(location: SrcSpan, segments: List(ExprBitArraySegment))
  RecordUpdateExpr(
    location: SrcSpan,
    constructor: Expr,
    spread: RecordUpdateSpread,
    arguments: List(RecordUpdateArg),
  )
  NegateBoolExpr(location: SrcSpan, value: Expr)
  NegateIntExpr(location: SrcSpan, value: Expr)
  /// A placeholder used when parsing is incomplete or when a function body is
  /// missing due to an external implementation being given for the function
  /// instead.
  /// gleam- TODO: This variant should be removed in future, but it requires some
  /// rework of the type inference code to be able to handle functions that do
  /// not have a body.
  PlaceholderExpr(location: SrcSpan)
}

pub fn expr_location(expr: Expr) {
  case expr {
    PipeLineExpr(expressions) -> {
      let assert Ok(#(last, _)) = queue.pop_back(expressions)
      expr_location(last)
    }
    IntExpr(location, ..)
    | FloatExpr(location, ..)
    | StringExpr(location, ..)
    | BlockExpr(location, ..)
    | VarExpr(location, ..)
    | FnExpr(location, ..)
    | CaptureExpr(location, ..)
    | ListExpr(location, ..)
    | CallExpr(location, ..)
    | BinOpExpr(location, ..)
    | CaseExpr(location, ..)
    | FieldAccessExpr(location, ..)
    | TupleExpr(location, ..)
    | TupleIndexExpr(location, ..)
    | TodoExpr(location: location, ..)
    | PanicExpr(location, ..)
    | BitArrayExpr(location, ..)
    | RecordUpdateExpr(location, ..)
    | NegateBoolExpr(location, ..)
    | NegateIntExpr(location, ..)
    | PlaceholderExpr(location) -> location
  }
}

pub type Use {
  Use(
    /// This is the expression with the untyped/typed code of the use callback
    /// function.
    call: Expr,
    /// This is the location of the whole use line, starting from the `use`
    /// keyword and ending with the function call on the right hand side of
    /// `<-`.
    ///
    /// ```gleam
    /// use a <- reult.try(result)
    /// ^^^^^^^^^^^^^^^^^^^^^^^^^^
    /// ```
    location: SrcSpan,
    /// This is the SrcSpan of the patterns you find on the left hand side of
    /// `<-` in a use expression.
    ///
    /// ```gleam
    /// use pattern1, pattern2 <- todo
    ///     ^^^^^^^^^^^^^^^^^^
    /// ```
    ///
    /// In case there's no patterns it will be corresponding to the SrcSpan of
    /// the `use` keyword itself.
    assignments_location: SrcSpan,
    /// The patterns on the left hand side of `<-` in a use expression.
    assignments: List(UseAssignment),
  )
}

// TODO
pub type Constant =
  Nil

// ast.rs

// line 41
pub type Module =
  ast.Module(Nil, TargetedDefinition)

// line 70
pub type TargetedDefinition {
  TargetedDefinition(definition: Definition, target: Option(build.Target))
}

// line 134
pub type Arg =
  ast.Arg(Nil)

// line 544
pub type CustomType =
  ast.CustomType(Nil)

// line 610
pub type Definition =
  ast.Definition(Nil, Expr, Nil, Nil)

// line 1042
pub type RecordUpdateSpread {
  RecordUpdateSpread(base: Expr, location: SrcSpan)
}

// line 1112
pub type ClauseGuard =
  ast.ClauseGuard(Nil, Nil)

// line 1342
pub type Pattern =
  ast.Pattern(Nil)

pub type RecordUpdateArg {
  RecordUpdateArg(label: String, location: SrcSpan, value: Expr)
}

// line 1836
pub type Statement =
  ast.Statement(Nil, Expr)

pub fn statement_location(statement: Statement) {
  ast.statement_location(statement, expr_location)
}

// line 1974 (last)
pub type UseAssignment {
  UseAssignment(
    location: SrcSpan,
    pattern: Pattern,
    annotation: Option(ast.TypeAst),
  )
}

// TODO
pub type Clause =
  Nil

// TODO
pub type ExprBitArraySegment =
  Nil
