import ast

pub type Type {
  /// A nominal (named) type such as `Int`, `Float`, or a programmer defined
  /// custom type such as `Person`. The type can take other types as
  /// arguments (aka "generics" or "parametric polymorphism").
  ///
  /// If the type is defined in the Gleam prelude the `module` field will be
  /// the string "gleam", otherwise it will contain the name of the module
  /// that defines the type.
  Named(
    publicity: ast.Publicity,
    package: String,
    module: String,
    name: String,
    args: List(ast.Arg(Type)),
  )

  /// The type of a function. It takes arguments and returns a value.
  Fn(args: List(ast.Arg(Type)), ret: Type)

  /// A type variable. See the contained `TypeVar` enum for more information.
  Var(type_: TypeVar)

  /// A tuple is an ordered collection of 0 or more values, each of which
  /// can have a different type, so the `tuple` type is the sum of all the
  /// contained types.
  Tuple(args: List(Type))
}

// TODO
type TypeVar =
  Nil
