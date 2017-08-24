(* Array.array *)
type 'x array0 = 'x array

let array x = x 
  
(* Array.length *)
let size = Array.length 
  
(* Array.`|_| *)
let bqbr_br (xs : 'x array0) = size xs
  
(* Array._.[_] *)
let _dtlb_rb = Array.get
  
(* Array.empty *)
let empty : 'x array0 = [||]
  
(* Array._::_ *)
let _clcl_ x t = 
  let len = Array.length t in
  let res = Array.make (len + 1) x in
  Array.blit t 0 res 1 len;
  res

(* Array.::: *)
let clclcl t x = 
  let len = Array.length t in
  let res = Array.make (len + 1) x in
  Array.blit t 0 res 0 len;
  res

(* Array._.[_<-_] *)
let _dtlb_lsmn_rb : 'x array0 -> int -> 'x -> 'x array0 =
  fun t i x ->
  Array.set t i x; t
  
(* Array.make *)
let make : int -> 'x -> 'x array0 = 
  Array.make 
  
(* Array.init *)
let offun : (int -> 'x) -> int -> 'x array0 = fun f n ->
  Array.init n f
  
(* Array.fill *)
let fill : 'x array0 -> int -> int -> 'x -> 'x array0 =
  fun t d o x -> 
    Array.fill t d o x;
    t
  
(* Array.map *)
let map : ('x -> 'y) -> 'x array0 -> 'y array0 =
  Array.map
  
(* Array.map2 *)
let map2 f t1 t2 = 
  let len = min (Array.length t1) (Array.length t2) in
  Array.init len (fun i -> f t1.(i) t2.(i))
  
(* Array.fold_left *)
let fold_left : ('state -> 'x -> 'state) -> 'state -> 'x array0 -> 'state =
  Array.fold_left
  
(* Array.fold_right *)
let fold_right f s t =
  Array.fold_right (fun x s -> f s x) t s
  
(* Array.all *)
let all f t = 
  let rec aux i = i >= Array.length t || (not (f t.(i)) && aux (i+1)) in
  aux 0 
  
(* Array.alli *)
let alli f t = 
  let rec aux i = i >= Array.length t || (not (f i t.(i)) && aux (i+1)) in
  aux 0

(* Array.Darray *)
module Darray = struct
  
  (* Array.Darray.darray *)
  let darray : int -> 'a EcPervasive.distr -> 'a array0 EcPervasive.distr =
     fun len d () -> Array.init len (fun _ -> d ()) 

end

(* ArrayExt *)
module ArrayExt = struct

  (* ArrayExt.|| *)
  let brbr : 'x array0 -> 'x array0 -> 'x array0 =
    Array.append
  
  (* ArrayExt.mapi *)
  let mapi : (int -> 'x -> 'y) -> 'x array0 -> 'y array0 =
    Array.mapi

  (* ArrayExt.sub *)
  let sub : 'x array0 -> int -> int -> 'x array0 =
    Array.sub
    
  (* ArrayExt.take *)
  let take : int -> 'a array0 -> 'a array0 = fun l xs ->
    sub xs 0 l
  
  (* ArrayExt.drop *)
  let drop : int -> 'a array0 -> 'a array0 = fun l xs ->
    sub xs l (size xs - l)
  
  (* ArrayExt.blit *)
  let blit : 'x array0 ->
             int -> 'x array0 -> int -> int -> 'x array0 =
    fun dst dOff src sOff len ->
    Array.blit src sOff dst dOff len; dst

    (* Array.init_dep *)
  let init_dep ar len extract =
    let r =
      make (Pervasives.(+) (size ar) len)
           (_dtlb_rb ar 0) in
    let r0 = blit r 0 ar 0 (size ar) in
    EcInt.ForLoop.range 0 len r0
                        (fun i r1 ->
                          _dtlb_lsmn_rb r1 (Pervasives.(+) i (size ar))
                                        (extract i r1))

end
