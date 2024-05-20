//// TODO

import gleam/option.{type Option}

//https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/ast.rs

// line 44
pub type Module(info, statements) {
  Module(
    name: String,
    documentation: Option(String),
    type_info: info,
    definitions: List(statements),
  )
}

// line 137
pub type Arg(ty) {
  Arg(
    names: ArgNames,
    location: SrcSpan,
    annotation: Option(TypeAst),
    type_: ty,
  )
}

pub type ArgNames {
  DiscardArgNames(name: String)
  LabelDiscardArgNames(label: String, name: String)
  NamedArgNames(name: String)
  LabelNamedArgNames(label: String, name: String)
}

// line 197
pub type RecordConstructor(ty) {
  RecordConstructor(
    location: SrcSpan,
    name: String,
    arguments: List(RecordConstructorArg(ty)),
    documentation: Option(String),
  )
}

pub type RecordConstructorArg(ty) {
  RecordConstructorArg(
    label: Option(String),
    location: SrcSpan,
    annotation: TypeAst,
    type_: ty,
    documentation: Option(String),
  )
}

// line 261
pub type TypeAst {
  TypeAstConstructor
  TypeAstFn
  TypeAstVar
  TypeAstTuple
  TypeAstHole
}

// line 412
pub type Publicity {
  Public
  Private
  Internal
}

// line 459
pub type Function(ty, expr) {
  Function(
    location: SrcSpan,
    end_position: Int,
    name: String,
    arguments: List(Arg(ty)),
    body: List(Statement(ty, expr)),
    publicity: Publicity,
    deprecation: Deprecation,
    return_annotation: Option(TypeAst),
    return_type: ty,
    documentation: Option(String),
    external_erlang: Option(#(String, String)),
    external_javascript: Option(#(String, String)),
    implementations: Implementations,
  )
}

// TODO
type Deprecation =
  Nil

// TODO
type Implementations =
  Nil

// line 497
/// Import another Gleam module so the current module can use the types and
/// values it defines.
///
/// # Example(s)
///
/// ```gleam
/// import unix/cat
/// // Import with alias
/// import animal/cat as kitty
/// ```
pub type Import(package_name) {
  Import(
    documentation: Option(String),
    location: SrcSpan,
    module: String,
    as_name: Option(#(AssignName, SrcSpan)),
    unqualified_values: List(UnqualifiedImport),
    unqualified_types: List(UnqualifiedImport),
    package: package_name,
  )
}

/// A certain fixed value that can be used in multiple places
///
/// # Example(s)
///
/// ```gleam
/// pub const start_year = 2101
/// pub const end_year = 2111
/// ```
pub type ModuleConstant(ty, const_record_tag) {
  ModuleConstant(
    location: SrcSpan,
    name: String,
    annotation: Option(TypeAst),
    value: Constant(ty, const_record_tag),
    type_: ty,
    publicity: Publicity,
    documentation: Option(String),
    deprecation: Deprecation,
    implementations: Implementations,
  )
}

// TODO
pub type Constant(ty, const_record_tag) {
  NilConstant
}

/// A newly defined type with one or more constructors.
/// Each variant of the custom type can contain different types, so the type is
/// the product of the types contained by each variant.
///
/// This might be called an algebraic data type (ADT) or tagged union in other
/// languages and type systems.
///
///
/// # Example(s)
///
/// ```gleam
/// pub type Cat {
///   Cat(name: String, cuteness: Int)
/// }
/// ```
pub type CustomType(ty) {
  CustomType(
    location: SrcSpan,
    end_position: Int,
    name: String,
    publicity: Publicity,
    constructors: List(RecordConstructor(ty)),
    documentation: Option(String),
    deprecation: Deprecation,
    opaque_: Bool,
    /// The names of the type parameters.
    parameters: List(String),
    /// Once type checked this field will contain the type information for the
    /// type parameters.
    typed_parameters: List(ty),
  )
}

// line 598
/// A new name for an existing type
///
/// # Example(s)
///
/// ```gleam
/// pub type Headers =
///   List(#(String, String))
/// ```
pub type TypeAlias(ty) {
  TypeAlias(
    location: SrcSpan,
    alias: String,
    parameters: List(String),
    type_ast: TypeAst,
    type_: ty,
    publicity: Publicity,
    documentation: Option(String),
    deprecation: Deprecation,
  )
}

// line 613
pub type Definition(ty, expr, const_record_tag, package_name) {
  FunctionDef(fun: Function(ty, expr))
  TypeAliasDef(alias: TypeAlias(ty))
  CustomTypeDef(custom_type: CustomType(ty))
  ImportDef(import_: Import(package_name))
  ModuleConstantDef(con: ModuleConstant(ty, const_record_tag))
}

// line 845
pub type UnqualifiedImport {
  UnqualifiedImport(location: SrcSpan, name: String, as_name: Option(String))
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

// line 1116
// TODO
pub type ClauseGuard(ty, record_tag) {
  NilClauseGuard
}

// line 1311
pub type SrcSpan {
  SrcSpan(start: Int, end: Int)
}

// line 1346
pub type Pattern(ty) {
  IntPat(location: SrcSpan, value: String)
  FloatPat(location: SrcSpan, value: String)
  StringPat(location: SrcSpan, value: String)
  /// The creation of a variable.
  /// e.g. `assert [this_is_a_var, .._] = x`
  VariablePat(location: SrcSpan, name: String, type_: ty)
  /// A reference to a variable in a bit array. This is always a variable
  /// being used rather than a new variable being assigned.
  /// e.g. `assert <<y:size(somevar)>> = x`
  VarUsagePat(
    location: SrcSpan,
    name: String,
    constructor: Option(ValueConstructor),
    type_: ty,
  )
  /// A name given to a sub-pattern using the `as` keyword.
  /// e.g. `assert #(1, [_, _] as the_list) = x`
  AssignPat(name: String, location: SrcSpan, pattern: Pattern(ty))
  /// A pattern that binds to any value but does not assign a variable.
  /// Always starts with an underscore.
  DiscardPat(name: String, location: SrcSpan, type_: ty)
  ListPat(
    location: SrcSpan,
    elements: List(Pattern(ty)),
    tail: Option(Pattern(ty)),
    type_: ty,
  )
  /// The constructor for a custom type. Starts with an uppercase letter.
  ConstructorPat(
    location: SrcSpan,
    name: String,
    arguments: List(CallArg(Pattern(ty))),
    module: Option(String),
    constructor: Inferred(PatternConstructor),
    with_spread: Bool,
    type_: ty,
  )
  TuplePat(location: SrcSpan, elements: List(Pattern(ty)))
  BitArrayPat(
    location: SrcSpan,
    segments: List(BitArraySegment(Pattern(ty), ty)),
  )
  // "prefix" <> variable
  StringPrefixPat(
    location: SrcSpan,
    left_location: SrcSpan,
    left_side_assignment: Option(#(String, String)),
    right_location: SrcSpan,
    left_side_string: String,
    /// The variable on the right hand side of the `<>`
    right_side_assignment: AssignName,
  )
}

pub type AssignName {
  VariableAssignName(String)
  DiscardAssignName(String)
}

// TODO
type ValueConstructor =
  Nil

// TODO
pub type Inferred(ty) {
  NilInferred
}

// TODO
pub type PatternConstructor =
  Nil

// TODO
pub type BitArraySegment(t1, t2) {
  NilBitArraySegment
}

// line 1597
pub type AssignmentKind {
  // let x = ...
  LetAssignment
  // let assert x = ...
  AssertAssignment(location: SrcSpan)
}

// line 1772
pub type TodoKind {
  KeywordTodo
  EmptyFunctionTodo
  IncompleteUseTodo
}

// line 1826
pub type Statement(ty, expr) {
  ExpressionStmt(expression: expr)
  AssignmentStmt(assignment: Assignment(ty, expr))
  UseStmt(use_: Use)
}

pub fn statement_location(
  statement: Statement(ty, expr),
  expression_location_getter: fn(expr) -> SrcSpan,
) -> SrcSpan {
  case statement {
    ExpressionStmt(expression) -> expression_location_getter(expression)
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

pub fn assignment_location(assignment: Assignment(_, _)) -> SrcSpan {
  assignment.location
}

// TODO
type Use =
  Nil
