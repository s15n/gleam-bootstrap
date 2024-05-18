pub type Token {
  Name(name: String)
  UpName(name: String)
  DiscardName(name: String)
  Int(value: String)
  Float(value: String)
  String(value: String)
  CommentDoc(content: String)
  // Groupings
  LeftParen
  // (
  RightParen
  // )
  LeftSquare
  // [
  RightSquare
  // ]
  LeftBrace
  // {
  RightBrace
  // }
  // Int Operators
  Plus
  Minus
  Star
  Slash
  Less
  Greater
  LessEqual
  GreaterEqual
  Percent
  // Float Operators
  PlusDot
  // '+.'
  MinusDot
  // '-.'
  StarDot
  // '*.'
  SlashDot
  // '/.'
  LessDot
  // '<.'
  GreaterDot
  // '>.'
  LessEqualDot
  // '<=.'
  GreaterEqualDot
  // '>=.'
  // String Operators
  LtGt
  // '<>'
  // Other Punctuation
  Colon
  Comma
  Hash
  // '#'
  Bang
  // '!'
  Equal
  EqualEqual
  // '=='
  NotEqual
  // '!='
  Vbar
  // '|'
  VbarVbar
  // '||'
  AmperAmper
  // '&&'
  LtLt
  // '<<'
  GtGt
  // '>>'
  Pipe
  // '|>'
  Dot
  // '.'
  RArrow
  // '->'
  LArrow
  // '<-'
  DotDot
  // '..'
  At
  // '@'
  EndOfFile
  // Extra
  CommentNormal
  CommentModule
  NewLine
  // Keywords (alphabetically):
  As
  Assert
  Auto
  Case
  Const
  Delegate
  Derive
  Echo
  Else
  Fn
  If
  Implement
  Import
  Let
  Macro
  Opaque
  Panic
  Pub
  Test
  Todo
  Type
  Use
}
