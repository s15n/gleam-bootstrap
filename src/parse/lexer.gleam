import gleam/iterator.{type Iterator}
import gleam/option.{type Option, None, Some}
import gleam/string

import parse/error.{type LexicalError}
import parse/token.{type Token}

pub type Lexer {
  Lexer(
    chars: Iterator(#(String, Int)),
    pending: List(Spanned),
    chr0: Option(String),
    chr1: Option(String),
    loc0: Int,
    loc1: Int,
    location: Int,
  )
}

pub type Spanned =
  #(Int, Token, Int)

pub type LexResult =
  Result(Spanned, LexicalError)

pub fn make_tokenizer(source: String) -> Lexer {
  let chars =
    source
    |> string.to_graphemes
    |> iterator.from_list
    |> iterator.index
  let nlh = new_nlh(chars)
  new(nlh_iterator(nlh))
}

// The newline handler is an iterator which collapses different newline
// types into \n always.
pub type NewlineHandler {
  NewlineHandler(
    source: Iterator(#(String, Int)),
    chr0: Option(#(String, Int)),
    chr1: Option(#(String, Int)),
  )
}

pub fn new_nlh(chars: Iterator(#(String, Int))) -> NewlineHandler {
  let nlh = NewlineHandler(chars, None, None)
  let #(_, nlh) = nlh_shift(nlh)
  let #(_, nlh) = nlh_shift(nlh)
  nlh
}

fn nlh_shift(nlh: NewlineHandler) -> #(Option(#(String, Int)), NewlineHandler) {
  let result = nlh.chr0
  let chr0 = nlh.chr1
  let #(chr1, source) = case iterator.step(nlh.source) {
    iterator.Done -> #(None, iterator.empty())
    iterator.Next(chr1, source) -> #(Some(chr1), source)
  }
  #(result, NewlineHandler(source, chr0, chr1))
}

fn nlh_iterator(nlh: NewlineHandler) -> Iterator(#(String, Int)) {
  let yield = fn(nlh: NewlineHandler) {
    let nlh = case nlh.chr0 {
      Some(#("\r", i)) -> {
        case nlh.chr1 {
          Some(#("\n", _)) -> {
            let #(_, nlh) = nlh_shift(nlh)
            NewlineHandler(..nlh, chr0: Some(#("\n", i)))
          }
          _ -> NewlineHandler(..nlh, chr0: Some(#("\n", i)))
        }
      }
      _ -> nlh
    }
    let #(chr, nlh) = nlh_shift(nlh)
    case chr {
      Some(c) -> iterator.Next(c, nlh)
      None -> iterator.Done
    }
  }
  iterator.unfold(nlh, yield)
}

pub fn new(input: Iterator(#(String, Int))) -> Lexer {
  let lxr =
    Lexer(
      chars: input,
      pending: [],
      location: 0,
      chr0: None,
      chr1: None,
      loc0: 0,
      loc1: 0,
    )
  let #(_, lxr) = next_char(lxr)
  let #(_, lxr) = next_char(lxr)
  Lexer(..lxr, location: 0)
}

// This is the main entry point. Call this function to retrieve the next token.
// This function is used by the iterator implementation.
fn inner_next(lxr: Lexer) -> #(LexResult, Lexer) {
  case lxr.pending {
    [] -> {
      let #(res, lxr) = consume_normal(lxr)
      case res {
        Ok(_) -> inner_next(lxr)
        Error(err) -> #(Error(err), lxr)
      }
    }
    [first, ..rest] -> {
      #(Ok(first), Lexer(..lxr, pending: rest))
    }
  }
}

// Take a look at the next character, if any, and decide upon the next steps.
fn consume_normal(lxr: Lexer) -> #(Result(#(), LexicalError), Lexer) {
  let lxr = case lxr.chr0 {
    Some(c) -> {
      todo
    }
    None -> {
      todo
      //let tok_pos = get_pos(lxr)
      //emit(lxr, tok_pos, Token::Eof)
    }
  }
  #(Ok(#()), lxr)
}

// Helper function to go to the next character coming up.
fn next_char(lxr: Lexer) -> #(Option(String), Lexer) {
  let c = lxr.chr0
  let #(nxt, lxr) = case iterator.step(lxr.chars) {
    iterator.Next(#(c, loc), chars) -> {
      #(Some(c), Lexer(..lxr, chars: chars, loc0: lxr.loc1, loc1: loc))
    }
    iterator.Done -> {
      #(None, Lexer(..lxr, loc0: lxr.loc1, loc1: lxr.loc1 + 1))
    }
  }
  #(c, Lexer(..lxr, chr0: lxr.chr1, chr1: nxt))
}
