let deb = false;;

let p_list oc l =
  Printf.fprintf oc "[";
  List.iter (Printf.fprintf oc "%i;") l;
  Printf.fprintf oc "]";
;;

let p_res (q, i) =
  Printf.eprintf "\nq=%i\ti=%a\n\n" q p_list i;
;;

let nat_select_n pp n =
  List.filter pp (List.init (succ n) (fun x -> x))
;;

let extr_f cmp f l =
  List.fold_left
    (fun accu x ->
      match accu with
      | None -> Some x
      | Some x' -> if cmp (f x) (f x') then Some x else Some x')
    None l
;;

let extr_f_n cmp f pp n = extr_f cmp f (nat_select_n pp n);;

let opt_cover_r a b an bn n =
  let pp x m = an m < x && x < bn m in
  let rec loop accu bi p =
    if deb then Printf.eprintf "\nenter loop_r: p=%i, bip=%i\n" p bi;
    let max_b = extr_f_n ( > ) bn (pp bi) n in
    let i =
      match max_b with
      | Some i -> i
      | None -> failwith "not a covering" in
    let accu = i :: accu in
    let bi = bn i in
    let p = succ p in
    if deb then Printf.eprintf "  in loop_r: p=%i, ip=%i, bip=%i\n" p i bi;
    if b < bi then (p, List.rev accu) else
    loop accu bi p in
  loop [] a 0
;;

let opt_cover_l a b an bn n =
  let pp x m = an m < x && x < bn m in
  let rec loop accu ai p =
    if deb then Printf.eprintf "\nenter loop_l: p=%i, aip=%i\n" p ai;
    let min_a = extr_f_n ( < ) an (pp ai) n in
    let i =
      match min_a with
      | Some i -> i
      | None -> failwith "not a covering" in
    let accu = i :: accu in
    let ai = an i in
    let p = succ p in
    if deb then Printf.eprintf "  in loop_l: p=%i, ip=%i, aip=%i\n" p i ai;
    if ai < a then (p, accu) else
    loop accu ai p in
  loop [] b 0
;;

let p_loop msg p bip accu pack =
  Printf.fprintf stderr
    "%s: p=%i, bip=%i, accu=%a, pack=%a\n"
    msg p bip p_list accu p_list pack
;;

let subcover1 a b an bn n =
  let pp x j = an j < x && x < bn j in
  let rec loop accu pack bip p =
    if deb then p_loop "\nenter loop" p bip accu pack;
    let i = try List.find (pp bip) pack with
      | Not_found -> failwith "not a covering" in
    let accu = i :: accu in
    let pack = List.find_all (( <> ) i) pack in
    let bip = bn i in
    let p = succ p in
    if deb then p_loop "exit loop" p bip accu pack;
    if b < bip then (p, List.rev accu) else
    loop accu pack bip p in
  let zero_n = List.init (succ n) (fun x -> x) in
  loop [] zero_n a 0
;;

let p_loop msg x pack =
  Printf.fprintf stderr
    "%s: x=%i, pack=%a\n"
    msg x p_list pack
;;

let subcover2 a b an bn n =
  let not_pp x j = x <= an j || bn j <= x in
  let rec loop x l =
    match l with
    | [] -> []
    | i :: l ->
      if deb then p_loop "\nenter loop" x (i :: l);
      if not_pp x i then loop x l else
      begin if deb then p_loop "exit loop" (bn i) l;
      i :: if b < bn i then [] else loop (bn i) l end in
  let colex j j' = Pervasives.compare (bn j, an j) (bn j', an j') in
  let zero_n = List.init (succ n) (fun x -> x) in
  if deb then Printf.fprintf stderr "\nzero_n=%a\n" p_list zero_n;
  let sorted_0_n = List.sort colex zero_n in
  if deb then Printf.fprintf stderr "sorted_0_n=%a\n" p_list sorted_0_n;
  let res = loop a sorted_0_n in
  (List.length res, res)
;;

let abl = [
  (1, 9);
  (-1, 0);
  (7, 10);
  (-1, 2);
  (1, 9);
  (12, 15);
  (8, 11);
  (2, 5);
  (3, 5);
  (7, 10);
  (6, 9);
];;

let (an, bn) =
  let (al, bl) = List.split abl in
  (List.nth al, List.nth bl)
;;

let num = pred (List.length abl);;

p_res (opt_cover_r 0 10 an bn num);;
p_res (opt_cover_l 0 10 an bn num);;
p_res (subcover1 0 10 an bn num);;
p_res (subcover2 0 10 an bn num);;
