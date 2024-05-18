import gleam/queue.{type Queue}

import ast.{type SrcSpan}

pub type ModuleExtra {
  ModuleExtra(
    module_comments: Queue(SrcSpan),
    doc_comments: Queue(SrcSpan),
    comments: Queue(SrcSpan),
    empty_lines: Queue(Int),
    new_lines: Queue(Int),
  )
}

pub fn module_extra_new() -> ModuleExtra {
  ModuleExtra(queue.new(), queue.new(), queue.new(), queue.new(), queue.new())
}
