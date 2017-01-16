(* Array.array *)
type 'x top_Array_array = 'x array

let array x = x 
  
(* Array.length *)
let top_Array_size = Array.length
                                                       
(* Array._.[_] *)
let top_Array___lb_rb = Array.get
  
(* Array.empty *)
let top_ArrayExt_empty : 'x top_Array_array = [||]

(* Array.init *)
let top_Array_offun (f : int -> 'x) (i : int) =
  Array.init i f

(* Array.blit *)
let top_ArrayExt_blit dst dOff src sOff len = Array.blit src sOff dst dOff len; dst
    
(* Array._::_ *)
let top_ArrayExt_clcl x t = 
  let len = top_Array_size t in
  let res = top_Array_offun (fun k -> x) (len + 1) in
  top_ArrayExt_blit res 1 t 0 len

(* Array.::: *)
let top_ArrayExt_clclcl t x = 
  let len = top_Array_size t in
  let res = top_Array_offun (fun k -> x) (len + 1) in
  top_ArrayExt_blit res 0 t 0 len

(* Array._.[_<-_] *)
let top_Array___lb_lsmn_rb : 'x top_Array_array -> int -> 'x -> 'x top_Array_array =
  fun t i x ->
  Array.set t i x; t
  
(* Array.|| *)
let top_ArrayExt_brbr : 'x top_Array_array -> 'x top_Array_array -> 'x top_Array_array =
  Array.append
  
(* Array.sub *)
let top_ArrayExt_sub : 'x top_Array_array -> int -> int -> 'x top_Array_array =
  Array.sub
  
(* Array.map *)
let top_Array_map : ('x -> 'y) -> 'x top_Array_array -> 'y top_Array_array =
  Array.map
 
(* Array.mapi *)
let top_ArrayExt_mapi : (int -> 'x -> 'y) -> 'x top_Array_array -> 'y top_Array_array =
  Array.mapi
  
(* Array.all *)
let top_ArrayExt_all f t = 
  let rec aux i = i >= top_Array_size t || (not (f t.(i)) && aux (i+1)) in
  aux 0 
  
(* Array.init_dep *)
let top_ArrayExt_init_dep ar size extract =
  let r =  top_Array_offun (fun k -> top_Array___lb_rb ar 0) (Pervasives.(+) (top_Array_size ar) size) in
  let r0 = top_ArrayExt_blit r 0 ar 0 (top_Array_size ar) in
  GarbleTools.ForLoop.top_GarbleTools_ForLoop_range 0 size r0
    (fun i r1 ->
       top_Array___lb_lsmn_rb r1 (Pervasives.(+) i (top_Array_size ar))
         (extract i r1))


(* Array.take *)
let top_ArrayExt_take l xs =
  top_ArrayExt_sub xs 0 l

(* Array.drop *)
let top_ArrayExt_drop l xs =
  top_ArrayExt_sub xs l (top_Array_size xs - l)

(* Array.append *)
let top_ArrayExt_brbr : 'x top_Array_array -> 'x top_Array_array -> 'x top_Array_array =
  Array.append
                   
(* Array.Darray *)
module Darray = struct
  
  (* Array.Darray.darray *)
  let darray : int -> 'a EcPervasive.distr -> 'a top_Array_array EcPervasive.distr =
     fun len d () -> top_Array_offun (fun _ -> d ()) len 

end
