open Extracted_code
open POram

let max_id = 100
let max_val = 10000
let num_trials = 10000

let tree_height = 5
let lop = tree_height - 1

let output_file = "results.txt"

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

let get_ops () = get_pairs num_trials

let get_vals ops =
  get_vals lop ops (empty_state lop) ()

let naive_ram = Hashtbl.create 50

let eval_op id op =
  match op with
  | Read ->
    begin match Hashtbl.find_opt naive_ram id with
    | None -> 0
    | Some v -> v
    end
  | Write v ->
    begin match Hashtbl.find_opt naive_ram id with
    | None -> Hashtbl.add naive_ram id v; 0
    | Some old_v -> Hashtbl.replace naive_ram id v; old_v
    end

let rec get_naive_vals ops =
  match ops with
  | [] -> []
  | (id,op) :: tl ->
    let v = eval_op id op in
    v :: get_naive_vals tl

let rec zip3 xs ys zs =
  match xs,ys,zs with
  | [], [], [] -> []
  | x::xs, y::ys, z::zs -> (x,y,z) :: zip3 xs ys zs
  | _,_,_ -> failwith "zip3 length mismatch"

let triples () =
  let ops = get_ops () in
  let oram_vals = get_vals ops in
  let naive_vals = get_naive_vals ops in
  zip3 ops oram_vals naive_vals

let print_op oc (id,o) =
  match o with
  | Read -> Printf.fprintf oc "Read @ %d" id
  | Write v -> Printf.fprintf oc "Write %d @ %d" v id

let print_results oc =
  let rec print tups =
  match tups with
  | [] -> Printf.fprintf stdout "all tests passed :)\n"
  | (p, v1, v2) :: tl ->
    print_op oc p; Printf.fprintf oc "\tORAM: %d\t Naive: %d\n" v1 v2;
    if v1 = v2 then print tl else Printf.fprintf stdout "test failed!"
  in 
  print (triples ())

let () =
  let oc = open_out output_file in
  let () = Random.self_init () in
  let () = print_results oc in
  close_out oc
