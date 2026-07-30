open Cfg_intf.S
open Utils

let sequence = ref (InstructionId.make_sequence ())

let make_id () = InstructionId.get_and_incr !sequence

let terminator ?(arg = [||]) desc : Terminator.t =
  { id = make_id (); desc; arg; res = [||] }

let block ?(body = []) ?exn start terminator : Block.t =
  { start; body; terminator; exn }

let make_cfg blocks =
  sequence := InstructionId.make_sequence ();
  Cfg_desc.make_pre_regalloc
    { fun_args = [| int.(0); int.(1) |];
      blocks;
      fun_contains_calls = false;
      fun_ret_type = Cmm.typ_int
    }

let validate_liveness cfg_with_infos =
  Misc.protect_refs
    [R (Oxcaml_flags.cfg_liveness_validate, true)]
    (fun () ->
      ignore (Cfg_with_infos.liveness cfg_with_infos : Cfg_with_infos.liveness))

let validate cfg_with_infos =
  Misc.protect_refs
    [ R (Oxcaml_flags.cfg_liveness_validate, true);
      R (Oxcaml_flags.cfg_dominators_validate, true) ]
    (fun () ->
      let cfg = Cfg_with_infos.cfg cfg_with_infos in
      ignore (Cfg_with_infos.liveness cfg_with_infos : Cfg_with_infos.liveness);
      ignore (Cfg_dominators.build cfg : Cfg_dominators.t);
      Cfg_reachability_validate.validate_reachability cfg)

let test_diamond () =
  let left = new_label 1 in
  let right = new_label 2 in
  let join = new_label 3 in
  make_cfg
    [ block entry_label
        (terminator
           ~arg:[| int.(0) |]
           (Truth_test { ifso = left; ifnot = right }));
      block left (terminator (Always join));
      block right (terminator (Always join));
      block join (terminator ~arg:[| int.(0) |] Return) ]
  |> validate

let test_nested_loops () =
  let outer_header = new_label 4 in
  let inner_header = new_label 5 in
  let inner_body = new_label 6 in
  let outer_latch = new_label 7 in
  let exit = new_label 8 in
  make_cfg
    [ block entry_label (terminator (Always outer_header));
      block outer_header
        (terminator
           ~arg:[| int.(0) |]
           (Truth_test { ifso = inner_header; ifnot = exit }));
      block inner_header
        (terminator
           ~arg:[| int.(1) |]
           (Truth_test { ifso = inner_body; ifnot = outer_latch }));
      block inner_body (terminator (Always inner_header));
      block outer_latch (terminator (Always outer_header));
      block exit (terminator ~arg:[| int.(0) |] Return) ]
  |> validate

let test_irreducible () =
  let left = new_label 9 in
  let right = new_label 10 in
  let join = new_label 11 in
  make_cfg
    [ block entry_label
        (terminator
           ~arg:[| int.(0) |]
           (Truth_test { ifso = left; ifnot = right }));
      block left (terminator (Always join));
      block right (terminator (Always join));
      block join
        (terminator
           ~arg:[| int.(1) |]
           (Truth_test { ifso = left; ifnot = right })) ]
  |> validate

let test_dead_pure_and_impure () =
  let body : Basic.t list =
    [ { id = make_id ();
        desc = Op (Intop Iadd);
        arg = [| int.(0); int.(1) |];
        res = [| int.(2) |]
      };
      { id = make_id (); desc = Op Opaque; arg = [| int.(3) |]; res = [||] } ]
  in
  make_cfg [block ~body entry_label (terminator ~arg:[| int.(0) |] Return)]
  |> validate

let test_exception_handler () =
  let handler = new_label 12 in
  make_cfg
    [ block ~exn:handler entry_label
        (terminator ~arg:[| int.(0) |] (Raise Raise_regular));
      block handler (terminator ~arg:[| Proc.loc_exn_bucket |] Return) ]
  |> validate

let expect_fatal f =
  let fmt = Format.err_formatter in
  Format.pp_print_flush fmt ();
  let previous = Format.pp_get_formatter_out_functions fmt () in
  let sink = Format.formatter_of_buffer (Buffer.create 0) in
  Format.pp_set_formatter_out_functions fmt
    (Format.pp_get_formatter_out_functions sink ());
  let raised =
    Fun.protect
      ~finally:(fun () -> Format.pp_set_formatter_out_functions fmt previous)
      (fun () ->
        match f () with () -> false | exception Misc.Fatal_error -> true)
  in
  if not raised then failwith "expected a fatal error"

let test_unreachable () =
  let dead = new_label 13 in
  let cfg_with_infos =
    make_cfg
      [ block entry_label (terminator ~arg:[| int.(0) |] Return);
        block dead (terminator ~arg:[| int.(1) |] Return) ]
  in
  expect_fatal (fun () ->
      Cfg_reachability_validate.validate_reachability
        (Cfg_with_infos.cfg cfg_with_infos))

let test_tailcall_self () =
  make_cfg
    [ block entry_label
        (terminator
           ~arg:[| int.(0); int.(1) |]
           (Tailcall_self { destination = entry_label })) ]
  |> validate_liveness

let random_reachable_cfg seed =
  let state = Random.State.make [| seed |] in
  let block_count = 1 + Random.State.int state 20 in
  let successors = Array.make block_count [] in
  let has_capacity index = List.compare_length_with successors.(index) 2 < 0 in
  let add_edge source target =
    if
      has_capacity source
      && not (List.exists (Int.equal target) successors.(source))
    then successors.(source) <- target :: successors.(source)
  in
  for target = 1 to block_count - 1 do
    let rec choose_parent () =
      let parent = Random.State.int state target in
      if has_capacity parent then parent else choose_parent ()
    in
    add_edge (choose_parent ()) target
  done;
  if block_count > 1
  then
    for _ = 1 to 2 * block_count do
      let source = Random.State.int state block_count in
      let target = 1 + Random.State.int state (block_count - 1) in
      add_edge source target
    done;
  let labels =
    Array.init block_count (fun index ->
        if index = 0 then entry_label else new_label index)
  in
  List.init block_count (fun index ->
      let terminator =
        match successors.(index) with
        | [] -> terminator ~arg:[| int.(0) |] Return
        | [target] -> terminator (Always labels.(target))
        | [left; right] ->
          terminator
            ~arg:[| int.(0) |]
            (Truth_test { ifso = labels.(left); ifnot = labels.(right) })
        | _ -> assert false
      in
      block labels.(index) terminator)
  |> make_cfg

let test_random_dominators () =
  for seed = 0 to 999 do
    let cfg_with_infos = random_reachable_cfg seed in
    let cfg = Cfg_with_infos.cfg cfg_with_infos in
    match
      Misc.protect_refs
        [R (Oxcaml_flags.cfg_dominators_validate, true)]
        (fun () -> ignore (Cfg_dominators.build cfg : Cfg_dominators.t))
    with
    | () -> ()
    | exception exn ->
      let backtrace = Printexc.get_raw_backtrace () in
      Format.eprintf "Dominator fuzz failure, seed %d:@.%a@." seed Printcfg.cfg
        cfg;
      Printexc.raise_with_backtrace exn backtrace
  done

let () =
  test_diamond ();
  test_nested_loops ();
  test_irreducible ();
  test_dead_pure_and_impure ();
  test_exception_handler ();
  test_unreachable ();
  test_tailcall_self ();
  test_random_dominators ()
