(* GarbleTools *)
module GarbleTools = struct

  (* GarbleTools.topo_t *)
  type topo_t = int * int * int * int EcIArray.array0 * int EcIArray.array0

end

(* Concrete *)
module Concrete = struct

  (* Concrete.ES *)
  module ES = struct
  
    (* Concrete.ES.W *)
    module W = struct
    
      (* Concrete.ES.W.word *)
      type word = Word.word
      
      (* Concrete.ES.W.zeros *)
      let zeros  =
        Word.zeros
      
      (* Concrete.ES.W.getlsb *)
      let getlsb  =
        Word.getlsb
      
      (* Concrete.ES.W.setlsb *)
      let setlsb  =
        Word.setlsb
      
      (* Concrete.ES.W.^ *)
      let cf  =
        Word.cf
      
      (* Concrete.ES.W.from_int *)
      let from_int  =
        Word.from_int
    
    end
    
    (* Concrete.ES.DKCScheme *)
    module DKCScheme = struct
    
      (* Concrete.ES.DKCScheme.W *)
      module W = struct
      
        (* Concrete.ES.DKCScheme.W.from_int *)
        let from_int  =
          W.from_int
      
      end
      
      (* Concrete.ES.DKCScheme.DKCSecurity *)
      module DKCSecurity = struct
      
        (* Concrete.ES.DKCScheme.DKCSecurity.W *)
        module W = struct
        
          (* Concrete.ES.DKCScheme.DKCSecurity.W.from_int *)
          let from_int  =
            W.from_int
        
        end
      
      end
      
      (* Concrete.ES.DKCScheme.Tweak *)
      module Tweak = struct
      
        (* Concrete.ES.DKCScheme.Tweak.W *)
        module W = struct
        
          (* Concrete.ES.DKCScheme.Tweak.W.from_int *)
          let from_int  =
            DKCSecurity.W.from_int
        
        end
        
        (* Concrete.ES.DKCScheme.Tweak.bti *)
        let bti (x : bool) =
          (if x then 1 else 0)
        
        (* Concrete.ES.DKCScheme.Tweak.tweak *)
        let tweak (g : int) (a : bool) (b : bool) =
          W.from_int
            (Pervasives.(+)
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
        DKC.e (DKCScheme.Tweak.tweak g x1 x2) (getTok x a xx1)
          (getTok x b xx2) (getTok x g (evalTupleGate f xx1 xx2))
      
      (* Concrete.ES.Local.garbleGate *)
      let garbleGate (x : tokens_t) (f : bool tupleGate_t) (a : int)
                     (b : int) (g : int) =
        (enc x f a b g false false, enc x f a b g false true,
          enc x f a b g true false, enc x f a b g true true)
      
      (* Concrete.ES.Local.evalComplete *)
      let evalComplete (f : 'a funct_t) (x : 'a EcIArray.array0)
                       (extract : 'a funct_t ->
                                    int -> 'a EcIArray.array0 -> 'a) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        EcIArray.init_dep x q (extract f)
      
      (* Concrete.ES.Local.evalGen *)
      let evalGen (f : 'a funct_t) (x : 'a EcIArray.array0)
                  (extract : 'a funct_t -> int -> 'a EcIArray.array0 -> 'a) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        EcIArray.sub (evalComplete f x extract)
          (Pervasives.(-) (Pervasives.(+) n q) m) m
      
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
        let t = DKCScheme.Tweak.tweak (Pervasives.(+) n g) a0 b0 in
        DKC.d t aA bB
          (evalTupleGate (EcIArray._dtlb_rb (Pervasives.snd ff) g) a0 b0)
      
      (* Concrete.ES.Local.garbMap *)
      let garbMap (x : tokens_t) (f : bool funct_t) (g : int) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        garbleGate x (EcIArray._dtlb_rb (Pervasives.snd f) g)
          (EcIArray._dtlb_rb aa g) (EcIArray._dtlb_rb bb g)
          (Pervasives.(+) n g)
      
      (* Concrete.ES.Local.randFormat *)
      let randFormat (nwires : int) (nouts : int) (r : tokens_t) =
        (if Pervasives.(<) (EcIArray.length r) nwires then
          EcIArray.init nwires
            (fun k -> (W.setlsb W.zeros false, W.setlsb W.zeros true))
        else
          EcIArray.mapi
            (fun i x ->
               (if Pervasives.(<) i (Pervasives.(-) nwires nouts) then
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
        ((fun (x_0, x_1) -> x_0) fn, EcIArray.init q (garbMap r fn))
      
      (* Concrete.ES.Local.inputK *)
      let inputK (fn : bool funct_t) (r : tokens_t) =
        let (n, m, q, a, b) = (fun (x_0, x_1) -> x_0) fn in
        EcIArray.sub r 0 n
      
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
              EcIArray.init (EcIArray.length iK)
                (fun k ->
                   ((if EcIArray._dtlb_rb x k then Pervasives.snd
                    else Pervasives.fst)) (EcIArray._dtlb_rb iK k))
          
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
  
  (* Concrete.SomeOT *)
  module SomeOT = struct
  
    (* Concrete.SomeOT.W *)
    module W = struct
    
      (* Concrete.SomeOT.W.word *)
      type word = ES.W.word
      
      (* Concrete.SomeOT.W.^ *)
      let cf  =
        ES.W.cf
    
    end
    
    (* Concrete.SomeOT.^^ *)
    let cfcf (w : W.word) =
      W.cf w
    
    (* Concrete.SomeOT.ESn *)
    module ESn = struct
    
      (* Concrete.SomeOT.ESn.hkey_t *)
      type hkey_t = W.word
    
    end
    
    (* Concrete.SomeOT.H *)
    let h  =
      Hash.hash
    
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
      EcIArray.mapi
        (fun k choice ->
           (if choice then
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
        EcIArray.mapi
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
      EcIArray.mapi
        (fun k choice ->
           cfcf
             (h hkey
                (Cyclic_group_prime.cf (Pervasives.fst m3)
                   (EcIArray._dtlb_rb x k)))
             ((if choice then
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
  
  (* Concrete.state1_t *)
  type state1_t = SomeOT.st_c_t
  
  (* Concrete.rand1_t *)
  type rand1_t = SomeOT.OTSecurity.OT.rand1_t
  
  (* Concrete.state2_t *)
  type state2_t =
    SomeOT.st_s_t * ES.ProjScheme.Sch.Scheme.funG_t *
    ES.ProjScheme.Sch.Scheme.outputK_t * Word.word EcIArray.array0 *
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
    ES.ProjScheme.Sch.Scheme.outputK_t * Word.word EcIArray.array0
  
  (* Concrete.p1_stage1 *)
  let p1_stage1 (i1 : bool EcIArray.array0) (r1 : rand1_t) (m1 : msg1_t) =
    SomeOT.msg2 i1 r1 m1
  
  (* Concrete.p1_stage2 *)
  let p1_stage2 (st : state1_t) (m3 : msg3_t) =
    let (ot_msg_in, fg_in, ko_in, x2g_in) = m3 in
    let ot_out = SomeOT.result st ot_msg_in in
    let t = Sys.time () in
    let outG =
      ES.ProjScheme.Sch.Scheme.evalG fg_in (EcIArray.brbr ot_out x2g_in) in
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
        (EcIArray.drop
           (Pervasives.(-) n (EcIArray.length (Pervasives.snd i2))) ki) x2 in
    let t = Sys.time () in
    let (st_ot, m1) =
      SomeOT.msg1
        (EcIArray.take
           (Pervasives.(-) n (EcIArray.length (Pervasives.snd i2))) ki)
        (Pervasives.fst r_ot) in
    (((st_ot, fg, ko, x2g, Pervasives.snd r_ot), m1),t)
  
  (* Concrete.p2_stage2 *)
  let p2_stage2 (st : state2_t) (m2 : msg2_t) =
    let (st_ot, fg, ko, x2g, r_ot2) = st in
    let m3 = SomeOT.msg3 st_ot r_ot2 m2 in (m3, fg, ko, x2g)

end