[@@@ocaml.warning "+a-40-41-42"]

let run_z3 code =
  let with_temp_file suffix f =
    let filename = Filename.temp_file "oxcaml-z3-" suffix in
    Misc.try_finally
      (fun () -> f filename)
      ~always:(fun () -> Misc.remove_file filename)
  in
  with_temp_file ".smt2" @@ fun input_file ->
  with_temp_file ".out" @@ fun output_file ->
  Out_channel.with_open_text input_file (fun out_channel ->
      Out_channel.output_string out_channel code);
  let command =
    Filename.quote_command "z3" ["-smt2"; input_file] ~stderr:output_file
      ~stdout:output_file
  in
  let ret = Ccomp.command command in
  let output = In_channel.with_open_text output_file In_channel.input_all in
  if ret <> 0
  then
    Misc.fatal_errorf "Z3 failed with return code %d. Input: @.%s@.Output: @.%s"
      ret code output;
  output

let fmt_fact fmt relation arguments =
  let fmt_argument fmt argument = Format.fprintf fmt " %s" argument in
  Format.fprintf fmt "(rule (%s%a))@." relation
    (Format.pp_print_list fmt_argument)
    arguments

module type Id_key = sig
  type t

  val compare : t -> t -> int

  val format : Format.formatter -> t -> unit

  module Tbl : Hashtbl.S with type key = t
end

module Make_id_gen (Key : Id_key) = struct
  type t =
    { id_table : int Key.Tbl.t;
      width : int
    }

  let bitwidth_of_count count =
    match count with 0 | 1 -> 1 | num_blocks -> 1 + Misc.log2 (num_blocks - 1)

  let create keys =
    let keys = List.sort_uniq Key.compare keys in
    let key_count = List.length keys in
    let id_table = Key.Tbl.create key_count in
    List.iteri (fun id key -> Key.Tbl.add id_table key id) keys;
    { id_table; width = bitwidth_of_count key_count }

  let width t = t.width

  let get_id_int { id_table; width = _ } ~key =
    match Key.Tbl.find_opt id_table key with
    | Some id -> id
    | None -> Misc.fatal_errorf "No Z3 id assigned to %a" Key.format key

  let get_id ({ width; _ } as t) ~key =
    Printf.sprintf "(_ bv%d %d)" (get_id_int t ~key) width
end

module Label_id_gen = Make_id_gen (Label)
