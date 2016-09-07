(* Int.zero *)
let zero : int = 0
  
(* Int.one *)
let one : int = 1
  
(* Int.< *)
let ( < ) = ( < )

(* Int.<= *)
let ( <= ) = ( <= )
              
(* Int.> *)
let ( > ) a b = not (a <= b)
 
(* Int.>= *)
let ( >= ) a b = not ( a < b )
 
(* Int.+ *)
let (+) = (+)

(* Int.[-] *)
let (~-) = (~-)
  
(* Int.* *)
let ( * ) = ( * )

(* Int.- *)
let (-) = (-)

(* Int.Abs *)
module Abs = struct
  
  (* Int.Abs.`|_| *)
  let top_Int_bqbr_br = Pervasives.abs
  
end
  
(* Int.Extrema *)
module Extrema = struct

  (* Int.Extrema.min *)
  let top_Int_Extrema_min = fun a b -> (if a < b then a else b)
  
  (* Int.Extrema.max *)
  let top_Int_Extrema_max = fun a b -> (if a < b then b else a)
    
end
  
(* Int.EuclDiv *)
module EuclDiv = struct

  (* Int.EuclDiv./% *)
  let top_IntDiv_euclidef = (/)  

  (* Int.EuclDiv.%% *)
  let top_IntDiv_pcpc = (mod)
  
end
  
(* Int.Power *)
module Power = struct
  
  (* Int.Power.^ *)
  let rec top_IntDiv_cf x p = 
    if p <= 0 then 1 
    else 
      let pow = top_IntDiv_cf x (p lsr 1) in
      if p land 1 = 0 then pow else pow * x
        
end
