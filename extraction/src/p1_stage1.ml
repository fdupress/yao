open Batteries
open EcIArray
open Utils

let cyclicarray_tostring bs =
  let l = List.map SFE.Cyclic_group_prime.to_string (Array.to_list bs) in
  String.concat "," l 
                   
let _ = Random.self_init ()

let prepareCircuit fn =
  let ((m,n,q,a,b),g) = fn in
  ((m,n,q,array a,array b),array g)

let prepareI i =
  match i with
  | Full bs -> array bs
  | Rand n  -> Random.self_init (); array (Array.init n (fun _ -> Random.bool ()))

type randomness = { r1:(SFE.Prime_field.gf_q array0) option;
                    r2:((SFE.Prime_field.gf_q array0 * string) * SFE.Prime_field.gf_q) option;
                    toks:((SFE.Concrete.W.word * SFE.Concrete.W.word) array0) option }

let rec parsedRandoms res rands =
  match rands with
  | [] -> res
  | (OTR2 (rs,r))::rands ->
    let res = {res with r2 = Some ((array rs, ""),r)} in
    parsedRandoms res rands
  | (GR toks)::rands ->
    let res = {res with toks = Some (array toks)} in
    parsedRandoms res rands

let prepareRandomness n fn rands : SFE.Concrete.rand1_t * SFE.Concrete.rand2_t =
  let res = parsedRandoms {r1 = None; r2 = None; toks = None} rands in
  let r1 = 
    match res.r1 with
    | None -> 
      offun (fun _ -> Lint.random SFE.Prime_field.modulus) n 
    | Some r1 -> r1 in
  let (r2:SFE.Concrete.SomeOT.OTSecurity.OT.rand2_t) = 
    match res.r2 with
    | None -> 
      let t1 = 
        offun (fun _ -> Lint.random SFE.Prime_field.modulus) n in
      ((t1, ""), Lint.random SFE.Prime_field.modulus)
    | Some r2 -> r2 in
  let (toks:SFE.Concrete.ES.ProjScheme.Sch.Scheme.rand_t) =
    match res.toks with
    | None ->
      let init_word _ = 
	let w = String.create 16 in
	for i = 0 to 15 do 
	  w.[i] <- Char.chr (Random.int 256)
	done;
	w in
      let init_token _ = init_word (), init_word () in
      let ((n,_,q,_,_),_) = fn in
      offun init_token (n + q)
    | Some ts -> ts in
  (r1,(r2,toks))


let m1_tostring s =
  let cs = String.nsplit s "," in
  Array.of_list (List.map (fun x -> Lint.of_string x) cs)
                
let string_to_code s =
  let to_code c =  Char.escaped '\\' ^ string_of_int (Char.code c) in
  String.concat "" (List.map to_code (String.to_list s))
    
let string_to_int_array s =
  let cs = String.nsplit s "," in
  Array.of_list (List.map (fun x -> int_of_string x) cs)

let bool_of_char = function
  | '0' -> false
  | '1' -> true
                
let string_to_gates s =
  let cs = String.nsplit s "," in
  Array.of_list (List.map (fun x -> (bool_of_char x.[0], bool_of_char x.[1], bool_of_char x.[2], bool_of_char x.[3])) cs)

let string_to_intlist s =
  List.map Char.code (String.to_list s)

let rec intlist_to_string = function
  | [] -> ""
  | [x] -> string_of_int x
  | h :: t -> string_of_int h ^ "," ^ intlist_to_string t
                
let tokensarray_to_string ts =
  let ls = Array.to_list (map (fun x -> intlist_to_string (string_to_intlist (fst x)) ^"*"^intlist_to_string (string_to_intlist (snd x))) ts) in
  String.concat ",," ls
     
let string_to_tokensarray s =
  let cs = String.nsplit s "," in
  let cs = List.map (fun x -> String.nsplit x "*") cs in
  cs

let string_to_bool_array s =

  let my_bool_of_string = fun x -> if x = "1" then true else false in
  
  let cs = String.nsplit s "," in
  Array.of_list (List.map (fun x -> my_bool_of_string x) cs)

let wordgates_to_string gs =
  let wordgate_to_string = fun (x,y,z,k) -> intlist_to_string (string_to_intlist x)^"*"^intlist_to_string (string_to_intlist y)^"*"^intlist_to_string (string_to_intlist z)^"*"^intlist_to_string (string_to_intlist k) in
  String.concat ",," (List.map wordgate_to_string (Array.to_list gs))
                
let funG_to_string fg =
  let ((n,m,q,aa,bb),gg) = fg in
  wordgates_to_string gg

let boolarray_to_string bs =
  String.of_list (List.map (fun x -> if x then '1' else '0') (Array.to_list bs))
                      
let x2g_to_string ta =
  let token_to_string x = intlist_to_string (string_to_intlist x) in
  String.concat ",," (List.map token_to_string (Array.to_list ta))

let file_to_list s =
  let filelines = File.lines_of s in
  let ret = ref [] in
  Enum.iter ( fun line -> ret := !ret @ [line] ) filelines ;
  !ret
                
let p1stage1 i1 m1 =
  let i1 = string_to_bool_array i1 in
  let i1 = prepareI (Full i1) in
  
  let rand1 = offun (fun _ -> Lint.random SFE.Prime_field.modulus) (size i1) in
  let m1 = m1_tostring m1 in
  
  let x = SFE.Concrete.p1_stage1 i1 rand1 ("",m1) in
  let (st,m) = x in
  let (inp,hkey,r1) = st in
  let strr1 = String.concat "," (List.map Lint.to_string (Array.to_list rand1)) in
  let out = strr1 ^ " " ^ cyclicarray_tostring m in
  out
    
let _ =

  let p1stage1inp = file_to_list "p1stage1.dat" in
  
  let i1 = List.nth p1stage1inp 0 in
  let m1 = List.nth p1stage1inp 1 in
  
  (*let i1 = Sys.argv.(1) in
  let m1 = Sys.argv.(2) in
   *)
  Printf.printf "%s" (p1stage1 i1 m1)


  
