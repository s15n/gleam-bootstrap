import simplifile

import gleam/io
import gleam/iterator

import parse
import parse/lexer

pub fn main() {
  //let filepath = "./src/parse/lexer.gleam"
  //let assert Ok(content) = simplifile.read(from: filepath)

  let content =
    "let bar:Int = 32
bar = 42"

  let res = parse.parse_statement_sequence(content)

  io.debug(res)
}
