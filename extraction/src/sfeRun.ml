open EcIArray
open Utils

let print_boolarray bs = 
  for i = 0 to size bs - 1 do 
    print_char (if _dtlb_rb bs i then '1' else '0'); done; flush stdout

let _ = Random.self_init ()

let pp_name oname = 
  match oname with
  | None -> ()
  | Some name -> Printf.printf "Running %s\n" name

let pp_input i ti = 
  Printf.printf "Input %i (%i bits):" i (size ti);
  print_boolarray ti; print_newline(); flush stdout

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
  | (OTR1 rs)::rands ->
    let res = {res with r1 = Some (array rs)} in
    parsedRandoms res rands
  | (OTR2 (rs,r))::rands ->
    let res = {res with r2 = Some ((array rs, ""),r)} in
    parsedRandoms res rands
  | (GR toks)::rands ->
    let res = {res with toks = Some (array toks)} in
    parsedRandoms res rands
    
let prepareRandomness i1 fn rands : SFE.Concrete.rand1_t * SFE.Concrete.rand2_t =
  let res = parsedRandoms {r1 = None; r2 = None; toks = None} rands in
  let r1 = 
    match res.r1 with
    | None -> 
      offun (fun _ -> Lint.random SFE.Prime_field.modulus) (size i1)
    | Some r1 -> r1 in
  let (r2:SFE.Concrete.SomeOT.OTSecurity.OT.rand2_t) = 
    match res.r2 with
    | None -> 
      let t1 = 
        offun (fun _ -> Lint.random SFE.Prime_field.modulus) (size i1) in
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

let execute (i1,i2, fn ,r) = 
     let i1 = prepareI i1 in
     let i2 = prepareI i2 in
     let (r1,r2) = prepareRandomness i1 fn r in
     let t0 = Sys.time () in
     let ((st2,m1), t01) = SFE.Concrete.p2_stage1 (fn,i2) r2 in
     let t1 = Sys.time () in
     let (st1, m2) = SFE.Concrete.p1_stage1 i1 r1 m1 in
     let t2 = Sys.time () in
     let m3 = SFE.Concrete.p2_stage2 st2 m2 in
     let t3 = Sys.time () in
     let (y,t34) = SFE.Concrete.p1_stage2 st1 m3 in
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
  Array.iter (parse_and_execute false) todo
