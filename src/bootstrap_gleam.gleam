import simplifile

import gleam/io
import gleam/iterator

import parse
import parse/lexer

pub fn main() {
  //let filepath = "./src/parse/lexer.gleam"
  //let assert Ok(content) = simplifile.read(from: filepath)

  let content = "case 42 > 42 { true -> 1; false -> 2; }"

  let res = parse.parse_statement_sequence(content)

  io.debug(res)
}
