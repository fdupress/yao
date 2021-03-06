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

(*let execute (i1,i2,fn,r) = 
     let i1 = prepareI i1 in
     let i2 = prepareI i2 in
     let (r1,r2) = prepareRandomness i1 fn r in
     let t0 = Sys.time () in
     let ((st2,m1), t01) = SFE.Concrete.top_Concrete_p2_stage1 (fn,i2) r2 in
     let t1 = Sys.time () in
     let (st1, m2) = SFE.Concrete.top_Concrete_p1_stage1 i1 r1 m1 in
     let t2 = Sys.time () in
     let m3 = SFE.Concrete.top_Concrete_p2_stage2 st2 m2 in
     let t3 = Sys.time () in
     let (y,t34) = SFE.Concrete.top_Concrete_p1_stage2 st1 m3 in
     let t4 = Sys.time () in
     (i1,i2,y,t4 -. t0,t01 -. t0,t1 -. t0,t2 -. t1,t3 -. t2,t34 -. t3,t4 -. t3)*)

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

let p1stage2 strcy stre n m q aa bb strfunG strx2g stri1 strr1 =
  let cy = Lint.of_string strcy in
  let e = string_to_tokensarray stre in
  
  let n = int_of_string n in
  let m = int_of_string m in
  let q = int_of_string q in
  let aa = string_to_int_array aa in
  let bb = string_to_int_array bb in

  let funG = string_to_funG strfunG in
  let funG = prepareCircuit ((n,m,q,aa,bb),funG) in
  let x2g = string_to_x2g strx2g in

  let i1 = string_to_bool_array stri1 in
  let i1 = prepareI (Full i1) in
 
  let r1 = Array.of_list (List.map Lint.of_string (String.nsplit strr1 ",")) in

  (*Printf.printf "Calling stage2 with:\ncy = %s\ne = %s\nn = %s\nm = %s\nq = %s\naa = %s\nbb = %s\nfung = %s\nx2g = %s\ni1 = %s\nr1 = %s\n\n\n\n\n" (Lint.to_string cy) (tokensarray_to_string e) (string_of_int n) (string_of_int m) (string_of_int q) ("") ("") (funG_to_string funG) ("") (boolarray_to_string i1) (strr1) ;*)
  
  let x = SFE.Concrete.p1_stage2 (i1, "", r1) ((cy, e), funG, (), x2g) in
  
  (*parsing the message*)
  let (res,t) = x in
  let out = boolarray_to_string res in
  out
  (*Printf.printf "%s" out*)
   
let _ =
  (*read from cmd*)

  let state1 = file_to_list "state2simpl.dat" in
  let state2 = file_to_list "state1.dat" in
  let p1stage2inp = file_to_list "p1stage2.dat" in
  
  let strcy = List.nth state1 0 in
  let stre = List.nth state1 1 in

  let n = List.nth state1 2 in
  let m = List.nth state1 3 in
  let q = List.nth state1 4 in
  let aa = List.nth state1 5 in
  let bb = List.nth state1 6 in
  let strfunG = List.nth state1 7 in

  let strx2g = List.nth state1 8 in

  let stri1 = List.nth p1stage2inp 0 in
  let strr1 = List.nth state2 0 in

  Printf.printf "%s" (p1stage2 strcy stre n m q aa bb strfunG strx2g stri1 strr1)

