import gleam/option.{type Option}
import gleam/queue.{type Queue}

import ast.{type SrcSpan}

pub type Expr {
  IntExpr(location: SrcSpan, value: String)
  VarExpr(location: SrcSpan, name: String)
  ListExpr(location: SrcSpan, elements: List(Expr), tail: Option(Expr))

  BinOpExpr(location: SrcSpan, name: ast.BinOp, left: Expr, right: Expr)

  // Guaranteed to have at least one element
  PipeLineExpr(expressions: Queue(Expr))

  CaseExpr(location: SrcSpan, subjects: List(Expr), clauses: List(Clause))
}

pub fn expr_location(expr: Expr) {
  case expr {
    PipeLineExpr(expressions) -> {
      let assert Ok(#(last, _)) = queue.pop_back(expressions)
      expr_location(last)
    }
    IntExpr(location, ..)
    | VarExpr(location, ..)
    | ListExpr(location, ..)
    | BinOpExpr(location, ..)
    | CaseExpr(location, ..) -> location
  }
}

// ast.rs:1836
pub type Statement =
  ast.Statement(Nil, Expr)

pub fn statement_location(statement: Statement) {
  ast.statement_location(statement)
}

// TODO
pub type Clause =
  Nil
