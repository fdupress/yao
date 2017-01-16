open EcIArray
open Utils
open Batteries
       
let print_boolarray bs = 
  for i = 0 to top_Array_size bs - 1 do 
    print_char (if top_Array___lb_rb bs i then '1' else '0'); done; flush stdout

let _ = Random.self_init ()

let pp_name oname = 
  match oname with
  | None -> ()
  | Some name -> Printf.printf "Running %s\n" name

let pp_input i ti = 
  Printf.printf "Input %i (%i bits):" i (top_Array_size ti);
  print_boolarray ti; print_newline(); flush stdout

let prepareCircuit fn =
  let ((m,n,q,a,b),g) = fn in
  ((m,n,q,array a,array b),array g)

let prepareI i =
  match i with
  | Full bs -> array bs
  | Rand n  -> Random.self_init (); array (Array.init n (fun _ -> Random.bool ()))

type randomness = { r1:(Prime_field.top_Prime_field_gf_q top_Array_array) option;
                    r2:((Prime_field.top_Prime_field_gf_q top_Array_array * string) * Prime_field.top_Prime_field_gf_q) option;
                    toks:((Word.top_Concrete_W_word * Word.top_Concrete_W_word) top_Array_array) option }

let rec parsedRandoms res rands =
  match rands with
  | [] -> res
  | (OTR1 rs)::rands ->
    let res = {res with r1 = Some (array rs)} in
    parsedRandoms res rands
  | (OTR2 (rs,r))::rands ->
    let res = {res with r2 = Some ((array rs, ""),r)} in
    parsedRandoms res rands
  | (GR toks)::rands ->
    let res = {res with toks = Some (array toks)} in
    parsedRandoms res rands

let prepareRandomness i1 fn rands : SFE.Concrete.top_Concrete_rand1_t * SFE.Concrete.top_Concrete_rand2_t =
  let res = parsedRandoms {r1 = None; r2 = None; toks = None} rands in
  let r1 = 
    match res.r1 with
    | None -> 
      top_Array_offun (fun _ -> Lint.random Prime_field.modulus) (top_Array_size i1) 
    | Some r1 -> r1 in
  let (r2:SFE.Concrete.SomeOT.OTSecurity.OT.top_Concrete_SomeOT_OTSecurity_OT_rand2_t) = 
    match res.r2 with
    | None -> 
      let t1 = 
        top_Array_offun (fun _ -> Lint.random Prime_field.modulus) (top_Array_size i1) in
      ((t1, ""), Lint.random Prime_field.modulus)
    | Some r2 -> r2 in
  let (toks:SFE.Concrete.ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_rand_t) =
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
      top_Array_offun init_token (n + q)
    | Some ts -> ts in
  (r1,(r2,toks))

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
  let ls = Array.to_list (top_Array_map (fun (x,y) -> intlist_to_string (string_to_intlist x) ^"*"^ intlist_to_string (string_to_intlist y)) ts) in
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

let x2g_to_string ta =
  let token_to_string x = intlist_to_string (string_to_intlist x) in
  String.concat ",," (List.map token_to_string (Array.to_list ta))

let cyclicarray_tostring bs =
  let l = List.map Cyclic_group_prime.to_string (Array.to_list bs) in
  String.concat "," l 

let string_to_boolarray s =
  let ret = ref [] in
  for i = 0 to String.length s - 1 do
    ret := !ret @ [(if s.[i] = '1' then true else false)] ;
  done
  ;
  Array.of_list !ret
                
let execute (i1,i2,fn,r) = 
  let i1 = prepareI (Full (string_to_boolarray "111")) in
  let i2 = prepareI (Full (string_to_boolarray "111")) in
  let (r1,r2) = prepareRandomness i1 fn r in
  let t0 = Sys.time () in
  let ((st2,m1), t01) = SFE.Concrete.top_Concrete_p2_stage1 (fn,i2) r2 in

  let (st_ot, fg, ko, x2g, r_ot) = st2 in
  let (toks,gps,hkey) = st_ot in

  let strtoks = tokensarray_to_string toks in
  let strgps = cyclicarray_tostring gps in
  let strfunG = funG_to_string fg in
  let strx2g = x2g_to_string x2g in
  let strrand2 = Lint.to_string r_ot in

  Printf.printf "toks = %s\ngps = %s\nfunG = %s\nx2g = %s\nrand2 = %s\nm1 = %s\n\n\n" strtoks strgps strfunG strx2g strrand2 (cyclicarray_tostring (snd m1)) ;

  Printf.printf "rand1 = %s\n\n\n" (String.concat "," (List.map Lint.to_string (Array.to_list r1))) ;
  
  let t1 = Sys.time () in
  let (st1, m2) = SFE.Concrete.top_Concrete_p1_stage1 i1 r1 m1 in

  let (inp,hkey,r1) = st1 in
  let strr1 = String.concat "," (List.map Lint.to_string (Array.to_list r1)) in

  Printf.printf "strr1 = %s\nm2 = %s\n\n\n" strr1 (cyclicarray_tostring m2) ;
  
  let t2 = Sys.time () in

  Printf.printf "Calling stage2 with:\ntoks = %s\ngps = %s\nhkey = %s\nfg = %s\nx2g = %s\nr_ot = %s\nm2 = %s\n\n\n\n" strtoks strgps hkey strfunG strx2g (Lint.to_string r_ot) (cyclicarray_tostring m2) ;
  
  let m3 = SFE.Concrete.top_Concrete_p2_stage2 ((toks,gps,hkey), fg, ko, x2g, r_ot) m2 in

  let ((cy, e), fg, ko, x2g) = m3 in

  let strcy = Lint.to_string cy in
  let stre = tokensarray_to_string e in

  Printf.printf "strcy = %s\nstre = %s\n\n\n" strcy stre ;
  
  let t3 = Sys.time () in
  let (y,t34) = SFE.Concrete.top_Concrete_p1_stage2 st1 m3 in
  let t4 = Sys.time () in
  (i1,i2,y,t4 -. t0,t01 -. t0,t1 -. t0,t2 -. t1,t3 -. t2,t34 -. t3,t4 -. t3)

let execSimple invals = 
  let (i1,i2,y,tf,_,t1,t2,t3,_,t4) = execute invals in
  pp_input 1 i1;
  pp_input 2 i2;
  print_string "Output: "; print_boolarray y; print_newline();
  Printf.printf "Time: %f (p2_s1: %f, p1_s1: %f, p2_s2: %f, p1_s2: %f)\n%!" tf t1 t2 t3 t4 

let benchmark invals count = 
  Printf.printf "FT, P2S1OT, P2S1, P1S1, P2S2, P1S2OT, P1S2\n%!";
  for i = 1 to count do  
     let (i1,i2,y,tf,t01,t1,t2,t3,t34,t4) = execute invals in
     Printf.printf "%f, %f, %f, %f, %f, %f, %f\n%!" tf t01 t1 t2 t3 t34 t4
  done

let parse_and_execute simple (oname, inchannel) =
  let lexbuf = Lexing.from_channel inchannel in
  let t0 = Sys.time () in
  let (i1,i2,fn,r) = SfeParser.main SfeLexer.main lexbuf in
  let fn = prepareCircuit fn in
  let input = (i1,i2,fn,r) in
  if (simple) 
  then (pp_name oname;
       Printf.printf "Parsing (excluding sampling) done in: %fs.\n%!" (Sys.time () -. t0);
       execSimple input;)
  else benchmark input 100

let _ =
  let open_in i = 
    let s = Sys.argv.(i+1) in
    Some s, open_in s in
  let todo = 
    let len = Array.length Sys.argv in
    if len = 1 then [|None, stdin|] 
    else Array.init (len-1) open_in in
  Array.iter (parse_and_execute true) todo
