open Batteries
open EcIArray
open Utils
       
let print_boolarray bs = 
  for i = 0 to size bs - 1 do 
    print_char (if _dtlb_rb bs i then '1' else '0'); done; flush stdout

let print_cyclicarray bs =
  for i = 0 to size bs - 1 do
    print_string (SFE.Cyclic_group_prime.to_string (_dtlb_rb bs i)) ;
    print_string " "
  done ;
  flush stdout

let cyclicarray_tostring bs =
  let l = List.map SFE.Cyclic_group_prime.to_string (Array.to_list bs) in
  String.concat "," l 

let string_to_cyclicarray s =
  let ss = String.nsplit s "," in
  Array.of_list (List.map Lint.of_string ss)
                   
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

let string_to_intlist2 s =
  List.map Char.code (String.to_list s)
 
let rec intlist_to_string2 = function
  | [] -> ""
  | [x] -> string_of_int x
  | h :: t -> string_of_int h ^ "," ^ intlist_to_string2 t

let string_to_intlist s =
  let ss = String.nsplit s "," in
  List.map int_of_string ss
 
let rec intlist_to_string = function
  | [] -> ""
  | h :: t -> String.make 1 (Char.chr h) ^ intlist_to_string t

let intarray_to_string = fun x -> intlist_to_string2 (Array.to_list x)
           
let tokensarray_to_string ts =
  let ls = List.map (fun (x,y) -> intlist_to_string2 (string_to_intlist2 x) ^"*"^intlist_to_string2 (string_to_intlist2 y)) (Array.to_list ts) in
  String.concat ",," ls
     
let string_to_tokensarray s =
  let cs = String.nsplit s ",," in

  let string_to_tokens s = 
    let ss = String.nsplit s "*" in
    (intlist_to_string (string_to_intlist (List.nth ss 0)), intlist_to_string (string_to_intlist (List.nth ss 1)))
  in
  Array.of_list (List.map string_to_tokens cs)

let string_to_bool_array s =

  let my_bool_of_string = fun x -> if x = "1" then true else false in
  
  let cs = String.nsplit s "," in
  Array.of_list (List.map (fun x -> my_bool_of_string x) cs)

let wordgates_to_string gs =
  let wordgate_to_string = fun (x,y,z,k) -> intlist_to_string (string_to_intlist x)^"*"^intlist_to_string (string_to_intlist y)^"*"^intlist_to_string (string_to_intlist z)^"*"^intlist_to_string (string_to_intlist k) in
  String.concat ",," (List.map wordgate_to_string (Array.to_list gs))

let string_to_wordgates s =
  let ss = String.nsplit s ",," in
  let string_to_wordgate s =
    let ss = String.nsplit s "*" in
    (intlist_to_string (string_to_intlist (List.nth ss 0)), intlist_to_string (string_to_intlist (List.nth ss 1)), intlist_to_string (string_to_intlist (List.nth ss 2)), intlist_to_string (string_to_intlist (List.nth ss 3)))
  in
  Array.of_list (List.map string_to_wordgate ss)
                
let funG_to_string fg =
  let ((n,m,q,aa,bb),gg) = fg in
  wordgates_to_string gg

let string_to_funG s =
  string_to_wordgates s

let boolarray_to_string bs =
  String.of_list (List.map (fun x -> if x then '1' else '0') (Array.to_list bs))
                      
let x2g_to_string ta =
  let token_to_string x = intlist_to_string (string_to_intlist x) in
  String.concat ",," (List.map token_to_string (Array.to_list ta))

let string_to_x2g s =
  let ss = String.nsplit s ",," in
  Array.of_list (List.map (fun x -> intlist_to_string (string_to_intlist x)) ss)

let file_to_list s =
  let filelines = File.lines_of s in
  let ret = ref [] in
  Enum.iter ( fun line -> ret := !ret @ [line] ) filelines ;
  !ret

let p2stage2 strtoks strgps n m q straa strbb strfunG strx2g strrand2 m2 =
  let toks = string_to_tokensarray strtoks in
  let gps = string_to_cyclicarray strgps in
  let n = int_of_string n in
  let m = int_of_string m in
  let q = int_of_string q in
  let aa = string_to_int_array straa in
  let bb = string_to_int_array strbb in

  let funG = string_to_funG strfunG in
   
  let funG = prepareCircuit ((n,m,q,aa,bb),funG) in
  let x2g = string_to_x2g strx2g in
  let rand2 = Lint.of_string strrand2 in
  
  let m2 = string_to_cyclicarray m2 in

  let x = SFE.Concrete.p2_stage2 ((toks, gps, ""), funG, (), x2g, rand2) m2 in
  (*parsing the message*)
  
  let (m3, fg, ko, x2g) = x in
  let (cy, e) = m3 in

  let strcy = Lint.to_string cy in
  let stre = tokensarray_to_string e in
  let out = strcy ^ " " ^ stre ^ " " ^ string_of_int n ^ " " ^ string_of_int m ^ " " ^ string_of_int q ^ " " ^ straa ^ " " ^ strbb ^ " " ^ strfunG ^ " " ^ strx2g in
  out
   
let _ =

  let state = file_to_list "state2.dat" in
  let p2stage2inp = file_to_list "p2stage2.dat" in
  
  let strtoks = List.nth state 0 in
  let strgps = List.nth state 1 in
  (*these 2 together with "" create st_ot*)
  let n = List.nth state 2 in
  let m = List.nth state 3 in
  let q = List.nth state 4 in
  let aa = List.nth state 5 in
  let bb = List.nth state 6 in
  let strfunG = List.nth state 7 in

  (*this does fg*)
  let strx2g = List.nth state 8 in
  (*unit here*)
  let strrand2 = List.nth state 9 in

  let m2 = List.nth p2stage2inp 0 in

  Printf.printf "%s" (p2stage2 strtoks strgps n m q aa bb strfunG strx2g strrand2 m2)
 (*cyclicarray_tostring*)
