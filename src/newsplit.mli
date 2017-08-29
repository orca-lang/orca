open Syntax
open Sign

val check_clauses :
  signature ->
  def_name ->
  Int.exp ->
  Apx.pat_decls -> signature_entry * Int.split_tree
