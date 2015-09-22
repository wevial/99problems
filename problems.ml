(* 99 Problems in OCaml
From: https://ocaml.org/learn/tutorials/99problems.html
*)

let rec last (ls:'a list):'a option =
    match ls with
    | [] -> None
    | [x] -> Some x
    | _::ls -> last ls

let rec last_two (ls:'a list):('a * 'a) option =
    match ls with
    | [] -> None
    | [x; y] -> Some (x, y)
    | _::ls -> last_two ls

let rec at (k:int) (ls:'a list):'a option =
    match ls with
    | [] -> None
    | l::ls -> if k = 1 then Some l else at (k-1) ls

let rec length (ls:'a list):int =
    match ls with
    | [] -> 0
    | _::ls -> 1 + length ls

let rec rev (ls:'a list):'a list =
    match ls with
    | [] -> []
    | l::ls -> (rev ls) @ [l]

let is_palindrome (ls:'a list):bool =
    rev ls = ls

type 'a node = 
    | One of 'a
    | Many of 'a node list

let rec flatten ls =
    match ls with
    | [] -> []
    | One x::xs -> [x] @ (flatten xs)
    | Many x::xs -> (flatten x) @ (flatten xs)

let rec compress ls =
    match ls with
    | [] -> []
    | x::[] -> [x]
    | x::y::ls -> if x = y
        then compress (x::ls)
        else [x] @ compress (y::ls)

let pack ls =
    let rec aux acc ls (curr, c) =
        match ls with
        | [] -> []
        | [x] -> if x = c
            then acc @ [(curr @ [x])]
            else acc @ [curr] @ [[x]]
        | x::xs -> if x = c
            then aux acc xs (curr @ [x], c)
            else aux (acc @ [curr]) xs ([x], x)

let encode ls = List.map (fun ls -> (List.length ls), (List.hd ls)) (pack ls)

type 'a rle =
    | One of 'a
    | Many of int * 'a

let encodeModified ls =
    let aux e = 
        match e with
        | (1, x) -> One x
        | (c, x) -> Many (c, x)
    in List.map aux (encode ls)

let decode ls =
    let rec many count acc x = 
        if count = 0 then acc else many (count-1) (acc @ [x]) x in
    let aux e =
        match e with
        | One x -> [x]
        | Many (c, x) -> many c [] x
    in List.map aux ls

let rec encodeDirect ls =
    let rec many (count, x) ls = 
        match ls with
        | [] -> ((count, x), [])
        | a::bs ->
            if a = x then many (count+1, x) bs
            else ((count, x), [a] @ bs)
    in
    match ls with
    | [] -> []
    | [x] -> [One x]
    | x::y::t ->
        if x = y then 
            let r = many (2, x) t in 
            let count = fst (fst r) in
            [Many (count, x)] @ encodeDirect (snd r)
        else [One x] @ encodeDirect ([y] @ t)

let rec duplicate ls =
    match ls with
    | [] -> []
    | x::xs -> [x;x] @ duplicate xs

let rec replicate ls n =
    let rec aux x n acc =
        if n = 0 then acc else aux x (n-1) ([x] @ acc)
    in
    match ls with
    | [] -> []
    | x::xs -> (aux x n []) @ replicate xs n

let rec drop ls n =
    if n <= 0 then ls else
    match ls with
    | [] -> []
    | x::xs ->
        if n = 1 then xs
        else [x] @ drop xs (n-1)

let rec split (ls:'a list) (n:int):('a list * 'a list) = 
    if List.length ls <= n then (ls, []) else
    match n, ls with
    | 0, _ -> ([], ls)
    | _, [] -> ([], [])
    | 1, [x] -> ([], [x])
    | n, x::xs -> let r = split xs (n-1) in
        ([x] @ fst r, snd r)

let slice ls i k =
    let rec lhs ls i = 
        match ls, i with
        | [], _ -> []
        | ls, 0 -> ls
        | x::xs, i -> lhs xs (i-1)
    in
    let rec rhs ls len =
        match ls, len with
        | [], _ | _, 0 -> []
        | x::xs, len -> [x] @ rhs xs (len-1)
    in
    if List.length ls < k then ls else
    match ls, i, k with 
    | [], _, _ | _, _, 0 -> []
    | ls, 0, k -> rhs ls k
    | ls, i, k -> rhs (lhs ls i) (k-i+1) (* Take indexing at 0 into account *)

let rec rotate ls n = 
    let ls = if n < 0 then rev ls else ls in
    match n, ls with
    | 0, ls -> ls
    | _, [] -> []
    | n, x::xs ->
        if n > 0 then rotate (xs @ [x]) (n-1)
        else rev (rotate (xs @ [x]) ((abs n)-1))

let rec remove_at i ls =
    match i, ls with
    | _, [] -> []
    | 0, _::xs -> xs
    | i, x::xs -> [x] @ remove_at (i-1) xs

let rec insert_at ele i ls =
    match i, ls with
    | _, [] -> [ele]
    | 0, ls -> [ele] @ ls
    | i, x::xs -> [x] @ insert_at ele (i-1) xs

let rec extract_at i ls =
    match i, ls with
    | _, [] -> raise Not_found
    | 0, x::xs -> (x, xs)
    | i, x::xs -> 
        let r = extract_at (i-1) xs
        in (fst r, [x] @ snd r)

let rec range x y =
    if x = y then [x]
    else if x < y then [x] @ range (x+1) y
    else rev (range y x)

(* FROM SOLUTION... *)
let rand_select list n =
    let rec extract acc n = function
        | [] -> raise Not_found
        | h::t -> if n = 0 then (h, acc @ t) else extract (h::acc) (n-1) t
    in
    let extract_rand list len =
        extract [] (Random.int len) list
    in
    let rec aux n acc list len =
        if n = 0 then acc else
            let picked, rest = extract_rand list len in
            aux (n-1) (picked::acc) rest (len-1)
    in
    let len = List.length list in
    aux (min n len) [] list len

let lotto_select n m = rand_select (range 1 m) n

let permutation ls =
    let rec aux (acc, ls) len = 
        if len = 0 then (acc, []) else
            let r = extract_at (Random.int len) ls in
            aux (acc @ [fst r], snd r) (len-1)
    in
    match ls with
    | [] -> []
    | x::xs -> fst (aux ([], ls) (List.length ls))

(* generate combination of K distinct objects chosen from
 * N elements of a list. *)
let extract k ls =
    let rec aux k acc emit = function
        | [] -> acc
        | hd::tl ->
            if k = 1 then aux k (emit [h] acc) emit t else
                let new_emit x = emit (hd::x) in
                aux k (aux (k-1) acc new_emit t) emit t
    in
    let emit x acc = x::acc in
    aux k [] emit ls

(* let rec combinations n ls =
    let rec aux n acc ls c =
        match n, ls with
        | 0, _ | _, [] -> []
        | n, [x] -> aux (n-1) ([x] @ acc) ls [c] (* reduce n by 1 *)
        | n, hd::tl -> 
    in
    match n, ls with
    | 0, _ | _, [] -> []
    | n, hd::tl -> aux n [] tl [hd] *)

(* let group ls1 ls2 ... *)

let rec length_sort ls =
    match ls with
    | [] -> []
    | hd::tl ->
        let hdlen = List.length hd in 
        let smaller = length_sort (List.filter ~f:(fun ls -> List.length ls <= hdlen) tl) in
        let bigger = length_sort (List.filter ~f:(fun ls -> List.length ls > hdlen) tl) in
        smaller @ [hd] @ bigger

(* let rec frequency_sort ls = *)

(* Fermat's little theorem *)
let is_prime n =
    let k = Int.of_float (3. ** Float.of_int n) mod n
    in k = 3 mod n

(* Euclidean algorithm *)
let rec gcd n m =
    match n, m with
    | n, 0 -> n
    | n, m -> gcd m (n mod m)

let coprime n m = 1 = gcd n m

(* Euler's totient function phi(m) *)
let phi m =
    if m = 1 then 1
    else List.length (List.filter ~f:(coprime m) (range 1 m))

let factors n =
    let rec aux d n =
        if n = 1 then [] else
            if n mod d = 0 then d :: aux d (n/d) else aux (d+1) n
    in
    aux 2 n

let factors2 n = encode (factors n)

let pow n p = if p < 1 then 1 else Int.of_float ((Float.of_int n) ** (Float.of_int p))

let phi_improved m =
    let fac = factors2 m in
    let rec aux fac =
        match fac with
        | [] -> 1
        | (p, m')::tl -> (p-1) * (pow p (m' -1)) * aux tl
        (* (Int.of_float ((Float.of_int p) ** (Float.of_int (m'-1)))) * aux tl *)
    in
    aux m

let timeit f a =
    let t0 = Unix.gettimeofday() in
    ignore(f a);
    let t1 = Unix.gettimeofday() in
    t1 -. t0

let all_primes n m = List.filter is_prime (range n m)

let goldbach n =
    let aux d =
        if is_prime d && is_prime (n-d) then (d, n-d)
        else aux (d+1)
    in
    aux 2
