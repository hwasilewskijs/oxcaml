[@@@ocaml.warning "+a-40-41-42"]

module Graph : sig
  type t =
    { entry : Label.t;
      nodes : Label.t list;
      edges : (Label.t * Label.t) list
    }

  val create : Cfg.t -> t
end
