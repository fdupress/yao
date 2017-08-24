(* GarbleTools *)
module GarbleTools = struct

  (* GarbleTools.ForLoop *)
  module ForLoop = struct
  
    (* GarbleTools.ForLoop.range *)
    let range : int -> int -> 'a -> (int -> 'a -> 'a) -> 'a = fun i j st f ->
      let st = ref st in
      for k = i to (j - 1) do
        st := f k !st;
      done;
      !st
  
  end
  
  (* GarbleTools.topo_t *)
  type topo_t = int * int * int * int EcIArray.array0 * int EcIArray.array0

end

(* Prime_field *)
module Prime_field = struct

  (* Prime_field.gf_q *)
  type gf_q = Lint.t

  (* For randomness generation outside *)
  let modulus : gf_q = Lint.of_string "72481352767688315425751847875272892093619870112060002462146901703425518159130917836981057777695498463879466680495585649636677842097230422710387592327164292868087312760004785404212516083244823425570343940987731481214098927618187231833749144065915043417485911202117888699457300562380265349235668136154184369633"            
end

(* Cyclic_group_prime *)
module Cyclic_group_prime = struct

  (* Cyclic_group_prime.group *)
  type group = Lint.t

  let modulus : group = Lint.of_string "144962705535376630851503695750545784187239740224120004924293803406851036318261835673962115555390996927758933360991171299273355684194460845420775184654328585736174625520009570808425032166489646851140687881975462962428197855236374463667498288131830086834971822404235777398914601124760530698471336272308368739267"
             
  (* Cyclic_group_prime.g *)
  let g : group = Lint.of_string "90351703421823010347810851313033956212579414141189157713471021982244971608490179588705148907491760337109520665561278964019650732503116486360224346513768744456449268334513380070713786359897561686555375461119637457758995356043237122464764882303280318697782628967458066188727079498536659324073031242343725137482"
  
  (* Cyclic_group_prime./ *)
  let sl : group -> group -> group = fun a b -> Lint.div_mod a b modulus
  
  (* Cyclic_group_prime.^ *)
  let cf : group -> Prime_field.gf_q -> group = fun a e -> Lint.powm a e modulus

  (* For hashing *)
  let to_string = Lint.to_string

end

(* Concrete *)
module Concrete = struct

  (* Concrete.W *)
  module W = struct
  
    (* Concrete.W.word *)
    type word = string

    let _dtlb_rb : word -> int -> bool = fun t n ->
      let c = Char.code (t.[n/8]) in
      let c = c land (1 lsl (n mod 8)) in
      c > 0
      
    let _dtlb_lsmn_rb : word -> int -> bool -> word = fun t n v ->
      let t = String.copy t in
      let q = n / 8 in
      let r = n mod 8 in
      let c = Char.code t.[q] in
      let mask = 0x01 lsl r in
      let c = if v then c lor mask else c land (0xFF lxor mask) in
      t.[q] <- Char.chr c;
      t
              
    (* Concrete.W.zeros *)
    let zeros : word =
      String.make 16 '\000'
    
    (* Concrete.W.getlsb *)
    let getlsb : word -> bool = fun w ->
      _dtlb_rb w 0
    
    (* Concrete.W.setlsb *)
    let setlsb : word -> bool -> word = fun w b ->
      _dtlb_lsmn_rb w 0 b
    
    (* Concrete.W.^ *)
    let cf : word -> word -> word = fun a b ->
      let r = String.copy zeros in
      for i = 0 to 15 do
        r.[i] <- Char.chr ((Char.code a.[i]) lxor (Char.code b.[i]))
      done;
      r
      
    (* Concrete.W.from_int *)
    let from_int : int -> word = fun inttok ->
      let tok = String.copy zeros in
      let inttokr = ref inttok in
      for i = 0 to 7 do
        tok.[i] <- Char.chr (!inttokr mod 256);
        inttokr := !inttokr / 256;
      done;
      tok
  
  end
           
  (* Concrete.SomeOT *)
  module SomeOT = struct
  
    (* Concrete.SomeOT.^^ *)
    let cfcf (w : W.word) =
      W.cf w
    
    (* Concrete.SomeOT.ESn *)
    module ESn = struct
    
      (* Concrete.SomeOT.ESn.dom_t *)
      type dom_t = Cyclic_group_prime.group
      
      (* Concrete.SomeOT.ESn.codom_t *)
      type codom_t = W.word
      
      (* Concrete.SomeOT.ESn.hkey_t *)
      type hkey_t = W.word
      
      (* Concrete.SomeOT.ESn.H *)
      module H = struct
      
        (* Concrete.SomeOT.ESn.H.dom_t *)
        type dom_t0 = dom_t
        
        (* Concrete.SomeOT.ESn.H.codom_t *)
        type codom_t0 = codom_t
        
        (* Concrete.SomeOT.ESn.H.hkey_t *)
        type hkey_t0 = hkey_t
        
        (* Concrete.SomeOT.ESn.H.hash *)
        let hash : hkey_t0 -> dom_t0 -> codom_t0 = fun k x ->
          let sha256 = Cryptokit.Hash.sha256 () in
          sha256#add_string (Cyclic_group_prime.to_string x);
          String.sub (sha256#result) 0 16
      
      end
    
    end
    
    (* Concrete.SomeOT.H *)
    let h  =
      ESn.H.hash
    
    (* Concrete.SomeOT.rand1_s_t *)
    type rand1_s_t = Prime_field.gf_q EcIArray.array0 * ESn.hkey_t
    
    (* Concrete.SomeOT.rand2_s_t *)
    type rand2_s_t = Prime_field.gf_q
    
    (* Concrete.SomeOT.rand_c_t *)
    type rand_c_t = Prime_field.gf_q EcIArray.array0
    
    (* Concrete.SomeOT.st_s_t *)
    type st_s_t =
      (W.word * W.word) EcIArray.array0 *
      Cyclic_group_prime.group EcIArray.array0 * ESn.hkey_t
    
    (* Concrete.SomeOT.st_c_t *)
    type st_c_t =
      bool EcIArray.array0 * ESn.hkey_t * Prime_field.gf_q EcIArray.array0
    
    (* Concrete.SomeOT.msg1_t *)
    type msg1_t = ESn.hkey_t * Cyclic_group_prime.group EcIArray.array0
    
    (* Concrete.SomeOT.msg2_t *)
    type msg2_t = Cyclic_group_prime.group EcIArray.array0
    
    (* Concrete.SomeOT.msg3_t *)
    type msg3_t =
      Cyclic_group_prime.group * (W.word * W.word) EcIArray.array0
    
    (* Concrete.SomeOT.gpow *)
    let gpow (xs : Prime_field.gf_q EcIArray.array0) =
      EcIArray.map (fun x -> Cyclic_group_prime.cf Cyclic_group_prime.g x) xs
    
    (* Concrete.SomeOT.pk0s *)
    let pk0s (inp : bool EcIArray.array0)
             (gcs : Cyclic_group_prime.group EcIArray.array0)
             (xs : Prime_field.gf_q EcIArray.array0) =
      EcIArray.ArrayExt.mapi
        (fun k sigma ->
           (if sigma then
             Cyclic_group_prime.sl (EcIArray._dtlb_rb gcs k)
               (Cyclic_group_prime.cf Cyclic_group_prime.g
                  (EcIArray._dtlb_rb xs k))
           else
             Cyclic_group_prime.cf Cyclic_group_prime.g
               (EcIArray._dtlb_rb xs k))) inp
    
    (* Concrete.SomeOT.msg1 *)
    let msg1 (inp : (W.word * W.word) EcIArray.array0) (r : rand1_s_t) =
      let (cs, hkey) = r in
      let gcs = gpow cs in ((inp, gcs, hkey), (hkey, gcs))
    
    (* Concrete.SomeOT.msg2 *)
    let msg2 (inp : bool EcIArray.array0) (r : rand_c_t) (m1 : msg1_t) =
      let (hkey, gcs) = m1 in ((inp, hkey, r), pk0s inp gcs r)
    
    (* Concrete.SomeOT.msg3 *)
    let msg3 (st : st_s_t) (r : Prime_field.gf_q) (m2 : msg2_t) =
      let (inp, gc, hkey) = st in
      let e =
        EcIArray.ArrayExt.mapi
          (fun k m ->
             (cfcf
                (h hkey (Cyclic_group_prime.cf (EcIArray._dtlb_rb m2 k) r))
                (Pervasives.fst m),
               cfcf
                 (h hkey
                    (Cyclic_group_prime.cf
                       (Cyclic_group_prime.sl (EcIArray._dtlb_rb gc k)
                          (EcIArray._dtlb_rb m2 k)) r)) (Pervasives.snd m)))
          inp in (Cyclic_group_prime.cf Cyclic_group_prime.g r, e)
    
    (* Concrete.SomeOT.result *)
    let result (st : st_c_t) (m3 : msg3_t) =
      let (inp, hkey, x) = st in
      EcIArray.ArrayExt.mapi
        (fun k sigma ->
           cfcf
             (h hkey
                (Cyclic_group_prime.cf (Pervasives.fst m3)
                   (EcIArray._dtlb_rb x k)))
             ((if sigma then
                Pervasives.snd (EcIArray._dtlb_rb (Pervasives.snd m3) k)
              else Pervasives.fst (EcIArray._dtlb_rb (Pervasives.snd m3) k))))
        inp
    
    (* Concrete.SomeOT.OTSecurity *)
    module OTSecurity = struct
    
      (* Concrete.SomeOT.OTSecurity.OT *)
      module OT = struct
      
        (* Concrete.SomeOT.OTSecurity.OT.rand1_t *)
        type rand1_t = rand_c_t
        
        (* Concrete.SomeOT.OTSecurity.OT.rand2_t *)
        type rand2_t = rand1_s_t * rand2_s_t
      
      end
    
    end
  
  end
  
  (* Concrete.ES *)
  module ES = struct
  
    (* Concrete.ES.SomeDKC *)
    module SomeDKC = struct
    
      (* Concrete.ES.SomeDKC.KW *)
      module KW = struct
      
        (* Concrete.ES.SomeDKC.KW.word *)
        type word = string
      
      end
      
      (* Concrete.ES.SomeDKC.PRF *)
      module PRF = struct
      
        (* Concrete.ES.SomeDKC.PRF.D *)
        type d = W.word
        
        (* Concrete.ES.SomeDKC.PRF.R *)
        type r = W.word
        
        (* Concrete.ES.SomeDKC.PRF.K *)
        type k = KW.word
        
        (* Concrete.ES.SomeDKC.PRF.F *)
        let f : k -> d -> r = fun key plain ->
          
          let kp = String.copy key in
          kp.[0] <- Char.chr ((Char.code kp.[0]) land 0xfe);
          let res = String.make 16 'a' in
          
          let res' = Aesprf.aes plain res kp in

          res
          
      end
      
      (* Concrete.ES.SomeDKC.PrfDKC *)
      module PrfDKC = struct
      
        (* Concrete.ES.SomeDKC.PrfDKC.E *)
        let e (t : PRF.d) (k1 : W.word) (k2 : W.word) (m : W.word) =
          W.cf
            (W.cf (PRF.f (W.setlsb k1 false) t)
               (PRF.f (W.setlsb k2 false) t)) m
        
        (* Concrete.ES.SomeDKC.PrfDKC.D *)
        let d (t : PRF.d) (k1 : W.word) (k2 : W.word) (c : W.word) =
          W.cf
            (W.cf (PRF.f (W.setlsb k1 false) t)
               (PRF.f (W.setlsb k2 false) t)) c
      
      end
    
    end
    
    (* Concrete.ES.SG *)
    module SG = struct
    
      (* Concrete.ES.SG.Tweak *)
      module Tweak = struct
      
        (* Concrete.ES.SG.Tweak.bti *)
        let bti (x : bool) =
          (if x then 1 else 0)
        
        (* Concrete.ES.SG.Tweak.tweak *)
        let tweak (g : int) (a : bool) (b : bool) =
          W.from_int (Pervasives.(+)
               (Pervasives.(+) (Pervasives.( * ) 4 g)
                  (Pervasives.( * ) 2 (bti a))) (bti b))
      
      end
    
    end
    
    (* Concrete.ES.Local *)
    module Local = struct
    
      (* Concrete.ES.Local.tupleGate_t *)
      type 'a tupleGate_t = 'a * 'a * 'a * 'a
      
      (* Concrete.ES.Local.tokens_t *)
      type tokens_t = (W.word * W.word) EcIArray.array0
      
      (* Concrete.ES.Local.gates_t *)
      type 'a gates_t = 'a tupleGate_t EcIArray.array0
      
      (* Concrete.ES.Local.funct_t *)
      type 'a funct_t = GarbleTools.topo_t * 'a gates_t
      
      (* Concrete.ES.Local.getTok *)
      let getTok (x : tokens_t) (a : int) (i : bool) =
        (if i then (fun (x_0, x_1) -> x_1) (EcIArray._dtlb_rb x a)
        else (fun (x_0, x_1) -> x_0) (EcIArray._dtlb_rb x a))
      
      (* Concrete.ES.Local.evalTupleGate *)
      let evalTupleGate (f : 'a tupleGate_t) (x1 : bool) (x2 : bool) =
        let (ff, ft, tf, tt) = f in
        (if Pervasives.(&&) (Pervasives.not x1) (Pervasives.not x2) then ff
        else
          (if Pervasives.(&&) (Pervasives.not x1) x2 then ft
          else (if Pervasives.(&&) x1 (Pervasives.not x2) then tf else tt)))
      
      (* Concrete.ES.Local.enc *)
      let enc (x : tokens_t) (f : bool tupleGate_t) (a : int) (b : int)
              (g : int) (x1 : bool) (x2 : bool) =
        let xx1 = Pervasives.(=) (W.getlsb (getTok x a true)) x1 in
        let xx2 = Pervasives.(=) (W.getlsb (getTok x b true)) x2 in
        SomeDKC.PrfDKC.e (SG.Tweak.tweak g x1 x2) (getTok x a xx1)
          (getTok x b xx2) (getTok x g (evalTupleGate f xx1 xx2))
      
      (* Concrete.ES.Local.garbleGate *)
      let garbleGate (x : tokens_t) (f : bool tupleGate_t) (a : int)
                     (b : int) (g : int) =
        (enc x f a b g false false, enc x f a b g false true,
          enc x f a b g true false, enc x f a b g true true)
      
      (* Concrete.ES.Local.init_dep *)
      let init_dep (xs : 'x EcIArray.array0) (l : int)
                   (f : int -> 'x EcIArray.array0 -> 'x) =
        let r =
          EcIArray.offun (fun k -> EcIArray._dtlb_rb xs 0)
            (Pervasives.(+) (EcIArray.size xs) l) in
        let r0 = EcIArray.ArrayExt.blit r 0 xs 0 (EcIArray.size xs) in
        GarbleTools.ForLoop.range 0 l r0
          (fun i r1 ->
             EcIArray._dtlb_lsmn_rb r1 (Pervasives.(+) i (EcIArray.size xs))
               (f i r1))
      
      (* Concrete.ES.Local.evalComplete *)
      let evalComplete (f : 'a funct_t) (x : 'a EcIArray.array0)
                       (extract : 'a funct_t ->
                                    int -> 'a EcIArray.array0 -> 'a) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        init_dep x q (extract f)
      
      (* Concrete.ES.Local.evalGen *)
      let evalGen (f : 'a funct_t) (x : 'a EcIArray.array0)
                  (extract : 'a funct_t -> int -> 'a EcIArray.array0 -> 'a) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        EcIArray.ArrayExt.sub (evalComplete f x extract)
          (Pervasives.(+) (Pervasives.(+) n q) (Pervasives.(~-) m)) m
      
      (* Concrete.ES.Local.extractG *)
      let extractG (ff : W.word funct_t) (g : int)
                   (x : W.word EcIArray.array0) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) ff in
        let a = EcIArray._dtlb_rb aa g in
        let b = EcIArray._dtlb_rb bb g in
        let aA = EcIArray._dtlb_rb x a in
        let bB = EcIArray._dtlb_rb x b in
        let a0 = W.getlsb aA in
        let b0 = W.getlsb bB in
        let t = SG.Tweak.tweak (Pervasives.(+) n g) a0 b0 in
        SomeDKC.PrfDKC.d t aA bB
          (evalTupleGate (EcIArray._dtlb_rb (Pervasives.snd ff) g) a0 b0)
      
      (* Concrete.ES.Local.garbMap *)
      let garbMap (x : tokens_t) (f : bool funct_t) (g : int) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        garbleGate x (EcIArray._dtlb_rb (Pervasives.snd f) g)
          (EcIArray._dtlb_rb aa g) (EcIArray._dtlb_rb bb g)
          (Pervasives.(+) n g)
      
      (* Concrete.ES.Local.randFormat *)
      let randFormat (nwires : int) (nouts : int) (r : tokens_t) =
        (if Pervasives.(<) (EcIArray.size r) nwires then
          EcIArray.offun
            (fun k -> (W.setlsb W.zeros false, W.setlsb W.zeros true)) nwires
        else
          EcIArray.ArrayExt.mapi
            (fun i x ->
               (if Pervasives.(<) i
                     (Pervasives.(+) nwires (Pervasives.(~-) nouts)) then
                 (W.setlsb ((fun (x_0, x_1) -> x_0) x)
                    (W.getlsb ((fun (x_0, x_1) -> x_0) x)),
                   W.setlsb (Pervasives.snd x)
                     (Pervasives.not (W.getlsb ((fun (x_0, x_1) -> x_0) x))))
               else
                 (W.setlsb ((fun (x_0, x_1) -> x_0) x) false,
                   W.setlsb (Pervasives.snd x) true))) r)
      
      (* Concrete.ES.Local.evalG *)
      let evalG (fn : W.word funct_t) (i : W.word EcIArray.array0) =
        evalGen fn i extractG
      
      (* Concrete.ES.Local.funG *)
      let funG (fn : bool funct_t) (r : tokens_t) =
        let (n, m, q, a, b) = (fun (x_0, x_1) -> x_0) fn in
        ((fun (x_0, x_1) -> x_0) fn, EcIArray.offun (garbMap r fn) q)
      
      (* Concrete.ES.Local.inputK *)
      let inputK (fn : bool funct_t) (r : tokens_t) =
        let (n, m, q, a, b) = (fun (x_0, x_1) -> x_0) fn in
        EcIArray.ArrayExt.sub r 0 n
      
      (* Concrete.ES.Local.outputK *)
      let outputK (fn : bool funct_t) (r : tokens_t) =
        ()
      
      (* Concrete.ES.Local.decode *)
      let decode (k : unit) (o : W.word EcIArray.array0) =
        EcIArray.map W.getlsb o
    
    end
    
    (* Concrete.ES.ProjScheme *)
    module ProjScheme = struct
    
      (* Concrete.ES.ProjScheme.token_t *)
      type token_t = W.word
      
      (* Concrete.ES.ProjScheme.Sch *)
      module Sch = struct
      
        (* Concrete.ES.ProjScheme.Sch.Scheme *)
        module Scheme = struct
        
          (* Concrete.ES.ProjScheme.Sch.Scheme.Input *)
          module Input = struct
          
            (* Concrete.ES.ProjScheme.Sch.Scheme.Input.input_t *)
            type input_t = bool EcIArray.array0
            
            (* Concrete.ES.ProjScheme.Sch.Scheme.Input.inputK_t *)
            type inputK_t = (token_t * token_t) EcIArray.array0
            
            (* Concrete.ES.ProjScheme.Sch.Scheme.Input.encode *)
            let encode (iK : inputK_t) (x : input_t) =
              EcIArray.offun
                (fun k ->
                   ((if EcIArray._dtlb_rb x k then Pervasives.snd
                    else Pervasives.fst)) (EcIArray._dtlb_rb iK k))
                (EcIArray.size iK)
          
          end
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.fun_t *)
          type fun_t = bool Local.funct_t
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.funG_t *)
          type funG_t = W.word Local.funct_t
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.outputK_t *)
          type outputK_t = unit
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.rand_t *)
          type rand_t = (W.word * W.word) EcIArray.array0
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.decode *)
          let decode  =
            Local.decode
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.evalG *)
          let evalG  =
            Local.evalG
        
        end
      
      end
    
    end
  
  end
  
  (* Concrete.state1_t *)
  type state1_t = SomeOT.st_c_t
  
  (* Concrete.rand1_t *)
  type rand1_t = SomeOT.OTSecurity.OT.rand1_t
  
  (* Concrete.state2_t *)
  type state2_t =
    SomeOT.st_s_t * ES.ProjScheme.Sch.Scheme.funG_t *
    ES.ProjScheme.Sch.Scheme.outputK_t * W.word EcIArray.array0 *
    SomeOT.rand2_s_t
  
  (* Concrete.rand2_t *)
  type rand2_t =
    SomeOT.OTSecurity.OT.rand2_t * ES.ProjScheme.Sch.Scheme.rand_t
  
  (* Concrete.msg1_t *)
  type msg1_t = SomeOT.msg1_t
  
  (* Concrete.msg2_t *)
  type msg2_t = SomeOT.msg2_t
  
  (* Concrete.msg3_t *)
  type msg3_t =
    SomeOT.msg3_t * ES.ProjScheme.Sch.Scheme.funG_t *
    ES.ProjScheme.Sch.Scheme.outputK_t * W.word EcIArray.array0
  
  (* Concrete.p1_stage1 *)
  let p1_stage1 (i1 : bool EcIArray.array0) (r1 : rand1_t) (m1 : msg1_t) =
    SomeOT.msg2 i1 r1 m1
  
  (* Concrete.p1_stage2 *)
  let p1_stage2 (st : state1_t) (m3 : msg3_t) =
    let (ot_msg_in, fg_in, ko_in, x2g_in) = m3 in
    let ot_out = SomeOT.result st ot_msg_in in
    let t = Sys.time () in
    let outG =
      ES.ProjScheme.Sch.Scheme.evalG fg_in (EcIArray.ArrayExt.brbr ot_out x2g_in) in
    (ES.ProjScheme.Sch.Scheme.decode ko_in outG,t)
  
  (* Concrete.p2_stage1 *)
  let p2_stage1 (i2 : ES.ProjScheme.Sch.Scheme.fun_t * bool EcIArray.array0)
                (r2 : rand2_t) =
    let (fn, x2) = i2 in
    let (r_ot, r_s) = r2 in
    let (n, m, q, a, b) = Pervasives.fst fn in
    let r_f = ES.Local.randFormat (Pervasives.(+) n q) m r_s in
    let fg = ES.Local.funG fn r_f in
    let ki = ES.Local.inputK fn r_f in
    let ko = ES.Local.outputK fn r_f in
    let x2g =
      ES.ProjScheme.Sch.Scheme.Input.encode
        (EcIArray.ArrayExt.drop
           (Pervasives.(-) n (EcIArray.size (Pervasives.snd i2))) ki) x2 in
    let t = Sys.time () in
    let (st_ot, m1) =
      SomeOT.msg1
        (EcIArray.ArrayExt.take
           (Pervasives.(-) n (EcIArray.size (Pervasives.snd i2))) ki)
        (Pervasives.fst r_ot) in
    (((st_ot, fg, ko, x2g, Pervasives.snd r_ot), m1),t)
  
  (* Concrete.p2_stage2 *)
  let p2_stage2 (st : state2_t) (m2 : msg2_t) =
    let (st_ot, fg, ko, x2g, r_ot2) = st in
    let m3 = SomeOT.msg3 st_ot r_ot2 m2 in (m3, fg, ko, x2g)

end
