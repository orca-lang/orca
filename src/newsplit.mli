open Syntax


val check_clauses :
  Int.signature ->
  def_name ->
  Int.exp ->
  Apx.pat_decls -> Int.signature_entry * Int.split_tree
