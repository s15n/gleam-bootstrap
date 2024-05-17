import gleam/io

import parse/lexer

pub fn main() {
  let lex = lexer.make_tokenizer("1 + 2 * 3")
  io.debug(lex)
}
