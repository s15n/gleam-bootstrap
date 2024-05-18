import gleam/option.{type Option}

import ast.{type SrcSpan}

pub type LexicalError {
  LexicalError(error: LexicalErrorType, location: SrcSpan)
}

pub type InvalidUnicodeEscapeError {
  MissingOpeningBrace
  // Expected '{'
  ExpectedHexDigitOrCloseBrace
  // Expected hex digit or '}'
  InvalidNumberOfHexDigits
  // Expected between 1 and 6 hex digits
  InvalidCodepoint
  // Invalid Unicode codepoint
}

pub type LexicalErrorType {
  BadStringEscape
  // string contains an unescaped slash
  InvalidUnicodeEscape(InvalidUnicodeEscapeError)
  // \u{...} escape sequence is invalid
  DigitOutOfRadix
  // 0x012 , 2 is out of radix
  NumTrailingUnderscore
  // 1_000_ is not allowed
  RadixIntNoValue
  // 0x, 0b, 0o without a value
  UnexpectedStringEnd
  // Unterminated string literal
  UnrecognizedToken(tok: String)
  BadName(name: String)
  BadDiscardName(name: String)
  BadUpname(name: String)
}

pub type ParseError {
  ParseError(error: ParseErrorType, location: SrcSpan)
}

pub type ParseErrorType {
  ExpectedEqual
  // expect "="
  ExpectedExpr
  // after "->" in a case clause
  ExpectedName
  // any token used when a Name was expected
  ExpectedPattern
  // after ':' where a pattern is expected
  ExpectedType
  // after ':' or '->' where a type annotation is expected
  ExpectedUpName
  // any token used when a UpName was expected
  ExpectedValue
  // no value after "="
  ExpectedStatement
  // no statement after "@<name>"
  ExpectedDefinition
  // after attributes
  ExpectedFunctionDefinition
  // after function-only attributes
  ExprLparStart
  // it seems "(" was used to start an expression
  ExtraSeparator
  // #(1,,) <- the 2nd comma is an extra separator
  IncorrectName
  // UpName or DiscardName used when Name was expected
  IncorrectUpName
  // Name or DiscardName used when UpName was expected
  InvalidBitArraySegment
  // <<7:hello>> `hello` is an invalid BitArray segment
  InvalidBitArrayUnit
  // in <<1:unit(x)>> x must be 1 <= x <= 256
  InvalidTailPattern
  // only name and _name are allowed after ".." in list pattern
  InvalidTupleAccess
  // only positive int literals for tuple access
  LexError(error: LexicalError)
  NestedBitArrayPattern
  // <<<<1>>, 2>>, <<1>> is not allowed in there
  NoExpression
  // between "{" and "}" in expression position, there must be an expression
  NoLetBinding
  // Bindings and rebinds always require let and must always bind to a value.
  NoValueAfterEqual
  // = <something other than a value>
  NotConstType
  // :fn(), name, _  are not valid const types
  OpNakedRight
  // Operator with no value to the right
  OpaqueTypeAlias
  // Type aliases cannot be opaque
  TooManyArgHoles
  // a function call can have at most 1 arg hole
  DuplicateAttribute
  // an attribute was used more than once
  UnknownAttribute
  // an attribute was used that is not known
  UnknownTarget
  // an unknown target was used
  ListSpreadWithoutElements
  // Pointless spread: `[..xs]`
  ListSpreadFollowedByElements
  // trying to append something after the spread: `[..xs, x]`
  LowcaseBooleanPattern
  // most likely user meant True or False in patterns
  UnexpectedLabel
  // argument labels were provided, but are not supported in this context
  UnexpectedEof
  UnexpectedReservedWord
  // reserved word used when a name was expected
  UnexpectedToken(expected: List(String), hint: Option(String))
  ExpectedBoolean
  UnexpectedFunction
  // a function was used called outside of another function
  ConcatPatternVariableLeftHandSide
  // A variable was assigned or discarded on the left hand side of a <> pattern
  ListSpreadWithoutTail
  // let x = [1, ..]
  ExpectedFunctionBody
  // let x = fn()
  RedundantInternalAttribute
  // for a private definition marked as internal
  InvalidModuleTypePattern
  // for patterns that have a dot like: `name.thing`
}
