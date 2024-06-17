open Extracted_code
open POram

let max_id = 100
let max_val = 10000
let num_trials = 10000

let tree_height = 5
let lop = tree_height - 1

let output_file = "stats.txt"

let get_rand_id () = Random.int max_id
let get_rand_val () = Random.int max_val

let get_rand_op () =
  let b = Random.bool () in
  if b then Read else
    let v = get_rand_val () in Write v

let get_rand_pair () =
  let id = get_rand_id () in
  let op = get_rand_op () in
  (id, op)

let rec get_pairs = function
  | 0 -> []
  | n ->
    let p = get_rand_pair () in
    p :: get_pairs (n-1)

let get_traces () =
  let ops = get_pairs num_trials in
  get_traces lop ops (empty_state lop) ()

let rec path_to_int = function
  | [] -> 0
  | false :: tl -> 2 * path_to_int tl
  | true :: tl -> 1 + 2 * path_to_int tl

let table = Hashtbl.create 50

let increment path =
  match Hashtbl.find_opt table path with
  | None -> Hashtbl.add table path 1
  | Some n -> Hashtbl.replace table path (n+1)

let mk_hashtbl () =
  let nums = List.map path_to_int (get_traces ()) in
  List.iter increment nums

let print_table oc =
  Hashtbl.iter (Printf.fprintf oc "Path: %d \t Frequency: %d\n") table

let () =
  let oc = open_out output_file in
  let () = Random.self_init () in
  let () = mk_hashtbl () in
  let () = print_table oc in
  close_out oc
