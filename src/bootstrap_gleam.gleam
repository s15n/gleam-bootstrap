import simplifile

import gleam/io
import gleam/iterator

import parse/lexer

pub fn main() {
  //let filepath = "./src/parse/lexer.gleam"
  //let assert Ok(content) = simplifile.read(from: filepath)

  let content = "\"\\g\""

  let lex = lexer.make_tokenizer(content)

  let iter = lexer.iterator(lex)
  iterator.each(iter, fn(token) { io.debug(token) })
}
