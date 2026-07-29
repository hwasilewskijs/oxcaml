[@@@ocaml.warning "+a-40-41-42"]

val run_z3 : string -> string

val fmt_fact : Format.formatter -> string -> string list -> unit

module Label_id_gen : sig
  type t

  val create : Label.t list -> t

  val get_id : t -> key:Label.t -> string

  val get_id_int : t -> key:Label.t -> int

  val width : t -> int
end
