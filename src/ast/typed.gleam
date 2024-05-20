import ast

import type_.{type Type}

// TODO
pub type Expr =
  Nil

// ast.rs

// line 609

pub type Definition =
  ast.Definition(Type, Expr, String, String)
