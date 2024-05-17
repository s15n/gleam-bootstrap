pub type LexicalError {
  LexicalError(error: LexicalErrorType, location: SrcSpan)
}

// TODO: This is a placeholder
type SrcSpan =
  #()

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
