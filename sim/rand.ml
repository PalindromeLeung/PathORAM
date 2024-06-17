type 'a t = unit -> 'a

let ret (x : 'a) : 'a t = fun () -> x

let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
  let x = m () in
  f x

let coin_flip : bool t =
  Random.bool
