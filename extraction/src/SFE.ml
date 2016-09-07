(* GarbleTools *)
module GarbleTools = struct

  (* GarbleTools.topo_t *)
  type top_GarbleTools_topo_t = int * int * int * int EcIArray.top_Array_array * int EcIArray.top_Array_array
                                                                                     
end

(* Concrete *)
module Concrete = struct

  (* Concrete.ES *)
  module ES = struct
  
    (* Concrete.ES.W *)
    module W = struct
    
      (* Concrete.ES.W.word *)
      type top_Concrete_ES_W_word = Word.top_Concrete_W_word
      
      (* Concrete.ES.W.zeros *)
      let top_Concrete_ES_W_zeros  =
        Word.top_Concrete_W_zeros
      
      (* Concrete.ES.W.getlsb *)
      let top_Concrete_ES_W_getlsb  =
        Word.top_Concrete_W_getlsb
      
      (* Concrete.ES.W.setlsb *)
      let top_Concrete_ES_W_setlsb  =
        Word.top_Concrete_W_setlsb
      
      (* Concrete.ES.W.^ *)
      let top_Concrete_ES_W_cf  =
        Word.top_Concrete_W_cf
      
      (* Concrete.ES.W.from_int *)
      let top_Concrete_ES_W_from_int  =
        Word.top_Concrete_W_from_int
    
    end
    
    (* Concrete.ES.DKCScheme *)
    module DKCScheme = struct
    
      (* Concrete.ES.DKCScheme.W *)
      module W = struct
      
        (* Concrete.ES.DKCScheme.W.from_int *)
        let top_Concrete_ES_DKCScheme_W_from_int  =
          W.top_Concrete_ES_W_from_int
      
      end
      
      (* Concrete.ES.DKCScheme.DKCSecurity *)
      module DKCSecurity = struct
      
        (* Concrete.ES.DKCScheme.DKCSecurity.W *)
        module W = struct
        
          (* Concrete.ES.DKCScheme.DKCSecurity.W.from_int *)
          let top_Concrete_ES_DKCScheme_DKCSecurity_W_from_int  =
            W.top_Concrete_ES_DKCScheme_W_from_int
        
        end
      
      end
      
      (* Concrete.ES.DKCScheme.Tweak *)
      module Tweak = struct
      
        (* Concrete.ES.DKCScheme.Tweak.W *)
        module W = struct
        
          (* Concrete.ES.DKCScheme.Tweak.W.from_int *)
          let top_Concrete_ES_DKCScheme_Tweak_W_from_int  =
            DKCSecurity.W.top_Concrete_ES_DKCScheme_DKCSecurity_W_from_int
        
        end
        
        (* Concrete.ES.DKCScheme.Tweak.bti *)
        let top_Concrete_ES_DKCScheme_Tweak_bti (b : bool) =
          if (b = true)
          then 1
          else 2
              
        (* Concrete.ES.DKCScheme.Tweak.tweak *)
        let top_Concrete_ES_DKCScheme_Tweak_tweak (g : int) (a : bool) (b : bool) =
          W.top_Concrete_ES_DKCScheme_Tweak_W_from_int
            (Pervasives.(+)
               (Pervasives.(+) (Pervasives.( * ) 4 g)
                  (Pervasives.( * ) 2 (top_Concrete_ES_DKCScheme_Tweak_bti a))) (top_Concrete_ES_DKCScheme_Tweak_bti b))
      
      end
    
    end
    
    (* Concrete.ES.Local *)
    module Local = struct
    
      (* Concrete.ES.Local.tupleGate_t *)
      type 'a top_Concrete_ES_Local_tupleGate_t = 'a * 'a * 'a * 'a
      
      (* Concrete.ES.Local.tokens_t *)
      type top_Concrete_ES_Local_tokens_t = (W.top_Concrete_ES_W_word * W.top_Concrete_ES_W_word) EcIArray.top_Array_array
      
      (* Concrete.ES.Local.gates_t *)
      type 'a top_Concrete_ES_Local_gates_t = 'a top_Concrete_ES_Local_tupleGate_t EcIArray.top_Array_array
      
      (* Concrete.ES.Local.funct_t *)
      type 'a top_Concrete_ES_Local_funct_t = GarbleTools.top_GarbleTools_topo_t * 'a top_Concrete_ES_Local_gates_t
      
      (* Concrete.ES.Local.getTok *)
      let top_Concrete_ES_Local_getTok (x : top_Concrete_ES_Local_tokens_t) (a : int) (i : bool) =
        (if i then (fun (x_0, x_1) -> x_1) (EcIArray.top_Array___lb_rb x a)
        else (fun (x_0, x_1) -> x_0) (EcIArray.top_Array___lb_rb x a))
      
      (* Concrete.ES.Local.evalTupleGate *)
      let top_Concrete_ES_Local_evalTupleGate (f : 'a top_Concrete_ES_Local_tupleGate_t) (x1 : bool) (x2 : bool) =
        let (ff, ft, tf, tt) = f in
        (if Pervasives.(&&) (Pervasives.not x1) (Pervasives.not x2) then ff
        else
          (if Pervasives.(&&) (Pervasives.not x1) x2 then ft
          else (if Pervasives.(&&) x1 (Pervasives.not x2) then tf else tt)))
      
      (* Concrete.ES.Local.enc *)
      let top_Concrete_ES_Local_enc (x : top_Concrete_ES_Local_tokens_t) (f : bool top_Concrete_ES_Local_tupleGate_t) (a : int) (b : int)
              (g : int) (x1 : bool) (x2 : bool) =
        let xx1 = Pervasives.(=) (W.top_Concrete_ES_W_getlsb (top_Concrete_ES_Local_getTok x a true)) x1 in
        let xx2 = Pervasives.(=) (W.top_Concrete_ES_W_getlsb (top_Concrete_ES_Local_getTok x b true)) x2 in
        DKC.top_Concrete_ES_SomeGarble_DKCSecurity_D_E (DKCScheme.Tweak.top_Concrete_ES_DKCScheme_Tweak_tweak g x1 x2) (top_Concrete_ES_Local_getTok x a xx1)
          (top_Concrete_ES_Local_getTok x b xx2) (top_Concrete_ES_Local_getTok x g (top_Concrete_ES_Local_evalTupleGate f xx1 xx2))
      
      (* Concrete.ES.Local.garbleGate *)
      let top_Concrete_ES_Local_garbleGate (x : top_Concrete_ES_Local_tokens_t) (f : bool top_Concrete_ES_Local_tupleGate_t) (a : int)
                     (b : int) (g : int) =
        (top_Concrete_ES_Local_enc x f a b g false false, top_Concrete_ES_Local_enc x f a b g false true,
          top_Concrete_ES_Local_enc x f a b g true false, top_Concrete_ES_Local_enc x f a b g true true)
      
      (* Concrete.ES.Local.evalComplete *)
      let top_Concrete_ES_Local_evalComplete (f : 'a top_Concrete_ES_Local_funct_t) (x : 'a EcIArray.top_Array_array)
                       (extract : 'a top_Concrete_ES_Local_funct_t ->
                                    int -> 'a EcIArray.top_Array_array -> 'a) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        EcIArray.top_ArrayExt_init_dep x q (extract f)
      
      (* Concrete.ES.Local.evalGen *)
      let top_Concrete_ES_Local_evalGen (f : 'a top_Concrete_ES_Local_funct_t) (x : 'a EcIArray.top_Array_array)
                  (extract : 'a top_Concrete_ES_Local_funct_t -> int -> 'a EcIArray.top_Array_array -> 'a) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        EcIArray.top_ArrayExt_sub (top_Concrete_ES_Local_evalComplete f x extract)
          (Pervasives.(-) (Pervasives.(+) n q) m) m
      
      (* Concrete.ES.Local.extractG *)
      let top_Concrete_ES_Local_extractG (ff : W.top_Concrete_ES_W_word top_Concrete_ES_Local_funct_t) (g : int)
                   (x : W.top_Concrete_ES_W_word EcIArray.top_Array_array) : W.top_Concrete_ES_W_word =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) ff in
        let a = EcIArray.top_Array___lb_rb aa g in
        let b = EcIArray.top_Array___lb_rb bb g in
        let aA = EcIArray.top_Array___lb_rb x a in
        let bB = EcIArray.top_Array___lb_rb x b in
        let a0 = W.top_Concrete_ES_W_getlsb aA in
        let b0 = W.top_Concrete_ES_W_getlsb bB in
        let t = DKCScheme.Tweak.top_Concrete_ES_DKCScheme_Tweak_tweak (Pervasives.(+) n g) a0 b0 in
        DKC.top_Concrete_ES_SomeGarble_DKCSecurity_D_D t aA bB
          (top_Concrete_ES_Local_evalTupleGate (EcIArray.top_Array___lb_rb (Pervasives.snd ff) g) a0 b0)
      
      (* Concrete.ES.Local.garbMap *)
      let top_Concrete_ES_Local_garbMap (x : top_Concrete_ES_Local_tokens_t) (f : bool top_Concrete_ES_Local_funct_t) (g : int) =
        let (n, m, q, aa, bb) = (fun (x_0, x_1) -> x_0) f in
        top_Concrete_ES_Local_garbleGate x (EcIArray.top_Array___lb_rb (Pervasives.snd f) g)
          (EcIArray.top_Array___lb_rb aa g) (EcIArray.top_Array___lb_rb bb g)
          (Pervasives.(+) n g)
      
      (* Concrete.ES.Local.randFormat *)
      let top_Concrete_ES_Local_randFormat (nwires : int) (nouts : int) (r : top_Concrete_ES_Local_tokens_t) =
        (if Pervasives.(<) (EcIArray.top_Array_size r) nwires then
          EcIArray.top_Array_offun (fun k -> (W.top_Concrete_ES_W_setlsb W.top_Concrete_ES_W_zeros false, W.top_Concrete_ES_W_setlsb W.top_Concrete_ES_W_zeros true)) nwires
        else
          EcIArray.top_ArrayExt_mapi
            (fun i x ->
               (if Pervasives.(<) i (Pervasives.(-) nwires nouts) then
                 (W.top_Concrete_ES_W_setlsb ((fun (x_0, x_1) -> x_0) x)
                    (W.top_Concrete_ES_W_getlsb ((fun (x_0, x_1) -> x_0) x)),
                   W.top_Concrete_ES_W_setlsb (Pervasives.snd x)
                     (Pervasives.not (W.top_Concrete_ES_W_getlsb ((fun (x_0, x_1) -> x_0) x))))
               else
                 (W.top_Concrete_ES_W_setlsb ((fun (x_0, x_1) -> x_0) x) false,
                   W.top_Concrete_ES_W_setlsb (Pervasives.snd x) true))) r)
      
      (* Concrete.ES.Local.evalG *)
      let top_Concrete_ES_Local_evalG (fn : W.top_Concrete_ES_W_word top_Concrete_ES_Local_funct_t) (i : W.top_Concrete_ES_W_word EcIArray.top_Array_array) =
        top_Concrete_ES_Local_evalGen fn i top_Concrete_ES_Local_extractG
      
      (* Concrete.ES.Local.funG *)
      let top_Concrete_ES_Local_funG (fn : bool top_Concrete_ES_Local_funct_t) (r : top_Concrete_ES_Local_tokens_t) =
        let (n, m, q, a, b) = (fun (x_0, x_1) -> x_0) fn in
        ((fun (x_0, x_1) -> x_0) fn, EcIArray.top_Array_offun (top_Concrete_ES_Local_garbMap r fn) q)
      
      (* Concrete.ES.Local.inputK *)
      let top_Concrete_ES_Local_inputK (fn : bool top_Concrete_ES_Local_funct_t) (r : top_Concrete_ES_Local_tokens_t) =
        let (n, m, q, a, b) = (fun (x_0, x_1) -> x_0) fn in
        EcIArray.top_ArrayExt_sub r 0 n
      
      (* Concrete.ES.Local.outputK *)
      let top_Concrete_ES_Local_outputK (fn : bool top_Concrete_ES_Local_funct_t) (r : top_Concrete_ES_Local_tokens_t) =
        ()
      
      (* Concrete.ES.Local.decode *)
      let top_Concrete_ES_Local_decode (k : unit) (o : W.top_Concrete_ES_W_word EcIArray.top_Array_array) =
        EcIArray.top_Array_map W.top_Concrete_ES_W_getlsb o
    
    end
    
    (* Concrete.ES.ProjScheme *)
    module ProjScheme = struct
    
      (* Concrete.ES.ProjScheme.token_t *)
      type top_Concrete_ES_ProjScheme_token_t = W.top_Concrete_ES_W_word
      
      (* Concrete.ES.ProjScheme.Sch *)
      module Sch = struct
      
        (* Concrete.ES.ProjScheme.Sch.Scheme *)
        module Scheme = struct
        
          (* Concrete.ES.ProjScheme.Sch.Scheme.Input *)
          module Input = struct
          
            (* Concrete.ES.ProjScheme.Sch.Scheme.Input.input_t *)
            type top_Concrete_ES_ProjScheme_Sch_Scheme_Input_input_t = bool EcIArray.top_Array_array
            
            (* Concrete.ES.ProjScheme.Sch.Scheme.Input.inputK_t *)
            type top_Concrete_ES_ProjScheme_Sch_Scheme_Input_inputK_t = (top_Concrete_ES_ProjScheme_token_t * top_Concrete_ES_ProjScheme_token_t) EcIArray.top_Array_array
            
            (* Concrete.ES.ProjScheme.Sch.Scheme.Input.encode *)
            let top_Concrete_ES_ProjScheme_Sch_Scheme_Input_encode (iK : top_Concrete_ES_ProjScheme_Sch_Scheme_Input_inputK_t) (x : top_Concrete_ES_ProjScheme_Sch_Scheme_Input_input_t) =
              EcIArray.top_Array_offun (fun k ->
                   ((if EcIArray.top_Array___lb_rb x k then Pervasives.snd
                     else Pervasives.fst)) (EcIArray.top_Array___lb_rb iK k))
                                       (EcIArray.top_Array_size iK)
          
          end
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.fun_t *)
          type top_Concrete_ES_ProjScheme_Sch_Scheme_fun_t = bool Local.top_Concrete_ES_Local_funct_t
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.funG_t *)
          type top_Concrete_ES_ProjScheme_Sch_Scheme_funG_t = W.top_Concrete_ES_W_word Local.top_Concrete_ES_Local_funct_t
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.outputK_t *)
          type top_Concrete_ES_ProjScheme_Sch_Scheme_outputK_t = unit
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.rand_t *)
          type top_Concrete_ES_ProjScheme_Sch_Scheme_rand_t = (W.top_Concrete_ES_W_word * W.top_Concrete_ES_W_word) EcIArray.top_Array_array
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.decode *)
          let top_Concrete_ES_ProjScheme_Sch_Scheme_decode  =
            Local.top_Concrete_ES_Local_decode
          
          (* Concrete.ES.ProjScheme.Sch.Scheme.evalG *)
          let top_Concrete_ES_ProjScheme_Sch_Scheme_evalG  =
            Local.top_Concrete_ES_Local_evalG
        
        end
      
      end
    
    end
  
  end
  
  (* Concrete.SomeOT *)
  module SomeOT = struct
  
    (* Concrete.SomeOT.W *)
    module W = struct
    
      (* Concrete.SomeOT.W.word *)
      type top_Concrete_SomeOT_W_word = ES.W.top_Concrete_ES_W_word
      
      (* Concrete.SomeOT.W.^ *)
      let top_Concrete_SomeOT_W_cf  =
        ES.W.top_Concrete_ES_W_cf
    
    end
    
    (* Concrete.SomeOT.^^ *)
    let top_Concrete_SomeOT_cfcf (w : W.top_Concrete_SomeOT_W_word) =
      W.top_Concrete_SomeOT_W_cf w
    
    (* Concrete.SomeOT.ESn *)
    module ESn = struct
    
      (* Concrete.SomeOT.ESn.hkey_t *)
      type top_Concrete_SomeOT_ESn_hkey_t = W.top_Concrete_SomeOT_W_word
    
    end
    
    (* Concrete.SomeOT.H *)
    let top_Concrete_SomeOT_H  =
      Hash.top_SomeOT_SomeOT_ESn_H_hash
    
    (* Concrete.SomeOT.rand1_s_t *)
    type top_Concrete_SomeOT_rand1_s_t = Prime_field.top_Prime_field_gf_q EcIArray.top_Array_array * ESn.top_Concrete_SomeOT_ESn_hkey_t
    
    (* Concrete.SomeOT.rand2_s_t *)
    type top_Concrete_SomeOT_rand2_s_t = Prime_field.top_Prime_field_gf_q
    
    (* Concrete.SomeOT.rand_c_t *)
    type top_Concrete_SomeOT_rand_c_t = Prime_field.top_Prime_field_gf_q EcIArray.top_Array_array
    
    (* Concrete.SomeOT.st_s_t *)
    type top_Concrete_SomeOT_st_s_t =
      (W.top_Concrete_SomeOT_W_word * W.top_Concrete_SomeOT_W_word) EcIArray.top_Array_array *
      Cyclic_group_prime.top_Cyclic_group_prime_group EcIArray.top_Array_array * ESn.top_Concrete_SomeOT_ESn_hkey_t
    
    (* Concrete.SomeOT.st_c_t *)
    type top_Concrete_SomeOT_st_c_t =
      bool EcIArray.top_Array_array * ESn.top_Concrete_SomeOT_ESn_hkey_t * Prime_field.top_Prime_field_gf_q EcIArray.top_Array_array
    
    (* Concrete.SomeOT.msg1_t *)
    type top_Concrete_SomeOT_msg1_t = ESn.top_Concrete_SomeOT_ESn_hkey_t * Cyclic_group_prime.top_Cyclic_group_prime_group EcIArray.top_Array_array
    
    (* Concrete.SomeOT.msg2_t *)
    type top_Concrete_SomeOT_msg2_t = Cyclic_group_prime.top_Cyclic_group_prime_group EcIArray.top_Array_array
    
    (* Concrete.SomeOT.msg3_t *)
    type top_Concrete_SomeOT_msg3_t =
      Cyclic_group_prime.top_Cyclic_group_prime_group * (W.top_Concrete_SomeOT_W_word * W.top_Concrete_SomeOT_W_word) EcIArray.top_Array_array
    
    (* Concrete.SomeOT.gpow *)
    let top_Concrete_SomeOT_gpow (xs : Prime_field.top_Prime_field_gf_q EcIArray.top_Array_array) =
      EcIArray.top_Array_map (fun x -> Cyclic_group_prime.top_Cyclic_group_prime_cf Cyclic_group_prime.top_Cyclic_group_prime_g x) xs
    
    (* Concrete.SomeOT.pk0s *)
    let top_Concrete_SomeOT_pk0s (inp : bool EcIArray.top_Array_array)
             (gcs : Cyclic_group_prime.top_Cyclic_group_prime_group EcIArray.top_Array_array)
             (xs : Prime_field.top_Prime_field_gf_q EcIArray.top_Array_array) =
      EcIArray.top_ArrayExt_mapi
        (fun k choice ->
           (if choice then
             Cyclic_group_prime.top_Cyclic_group_prime_sl (EcIArray.top_Array___lb_rb gcs k)
               (Cyclic_group_prime.top_Cyclic_group_prime_cf Cyclic_group_prime.top_Cyclic_group_prime_g
                  (EcIArray.top_Array___lb_rb xs k))
           else
             Cyclic_group_prime.top_Cyclic_group_prime_cf Cyclic_group_prime.top_Cyclic_group_prime_g
               (EcIArray.top_Array___lb_rb xs k))) inp
    
    (* Concrete.SomeOT.msg1 *)
    let top_Concrete_SomeOT_msg1 (inp : (W.top_Concrete_SomeOT_W_word * W.top_Concrete_SomeOT_W_word) EcIArray.top_Array_array) (r : top_Concrete_SomeOT_rand1_s_t) =
      let (cs, hkey) = r in
      let gcs = top_Concrete_SomeOT_gpow cs in ((inp, gcs, hkey), (hkey, gcs))
    
    (* Concrete.SomeOT.msg2 *)
    let top_Concrete_SomeOT_msg2 (inp : bool EcIArray.top_Array_array) (r : top_Concrete_SomeOT_rand_c_t) (m1 : top_Concrete_SomeOT_msg1_t) =
      let (hkey, gcs) = m1 in ((inp, hkey, r), top_Concrete_SomeOT_pk0s inp gcs r)
    
    (* Concrete.SomeOT.msg3 *)
    let top_Concrete_SomeOT_msg3 (st : top_Concrete_SomeOT_st_s_t) (r : Prime_field.top_Prime_field_gf_q) (m2 : top_Concrete_SomeOT_msg2_t) =
      let (inp, gc, hkey) = st in
      let e =
        EcIArray.top_ArrayExt_mapi
          (fun k m ->
             (top_Concrete_SomeOT_cfcf
                (top_Concrete_SomeOT_H hkey (Cyclic_group_prime.top_Cyclic_group_prime_cf (EcIArray.top_Array___lb_rb m2 k) r))
                (Pervasives.fst m),
               top_Concrete_SomeOT_cfcf
                 (top_Concrete_SomeOT_H hkey
                    (Cyclic_group_prime.top_Cyclic_group_prime_cf
                       (Cyclic_group_prime.top_Cyclic_group_prime_sl (EcIArray.top_Array___lb_rb gc k)
                          (EcIArray.top_Array___lb_rb m2 k)) r)) (Pervasives.snd m)))
          inp in (Cyclic_group_prime.top_Cyclic_group_prime_cf Cyclic_group_prime.top_Cyclic_group_prime_g r, e)
    
    (* Concrete.SomeOT.result *)
    let top_Concrete_SomeOT_result (st : top_Concrete_SomeOT_st_c_t) (m3 : top_Concrete_SomeOT_msg3_t) =
      let (inp, hkey, x) = st in
      EcIArray.top_ArrayExt_mapi
        (fun k choice ->
           top_Concrete_SomeOT_cfcf
             (top_Concrete_SomeOT_H hkey
                (Cyclic_group_prime.top_Cyclic_group_prime_cf (Pervasives.fst m3)
                   (EcIArray.top_Array___lb_rb x k)))
             ((if choice then
                Pervasives.snd (EcIArray.top_Array___lb_rb (Pervasives.snd m3) k)
              else Pervasives.fst (EcIArray.top_Array___lb_rb (Pervasives.snd m3) k))))
        inp
    
    (* Concrete.SomeOT.OTSecurity *)
    module OTSecurity = struct
    
      (* Concrete.SomeOT.OTSecurity.OT *)
      module OT = struct
      
        (* Concrete.SomeOT.OTSecurity.OT.rand1_t *)
        type top_Concrete_SomeOT_OTSecurity_OT_rand1_t = top_Concrete_SomeOT_rand_c_t
        
        (* Concrete.SomeOT.OTSecurity.OT.rand2_t *)
        type top_Concrete_SomeOT_OTSecurity_OT_rand2_t = top_Concrete_SomeOT_rand1_s_t * top_Concrete_SomeOT_rand2_s_t
      
      end
    
    end
  
  end
  
  (* Concrete.state1_t *)
  type top_Concrete_state1_t = SomeOT.top_Concrete_SomeOT_st_c_t
  
  (* Concrete.rand1_t *)
  type top_Concrete_rand1_t = SomeOT.OTSecurity.OT.top_Concrete_SomeOT_OTSecurity_OT_rand1_t
  
  (* Concrete.state2_t *)
  type top_Concrete_state2_t =
    SomeOT.top_Concrete_SomeOT_st_s_t * ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_funG_t *
    ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_outputK_t * Word.top_Concrete_W_word EcIArray.top_Array_array *
    SomeOT.top_Concrete_SomeOT_rand2_s_t
  
  (* Concrete.rand2_t *)
  type top_Concrete_rand2_t =
    SomeOT.OTSecurity.OT.top_Concrete_SomeOT_OTSecurity_OT_rand2_t * ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_rand_t
  
  (* Concrete.msg1_t *)
  type top_Concrete_msg1_t = SomeOT.top_Concrete_SomeOT_msg1_t
  
  (* Concrete.msg2_t *)
  type top_Concrete_msg2_t = SomeOT.top_Concrete_SomeOT_msg2_t
  
  (* Concrete.msg3_t *)
  type top_Concrete_msg3_t =
    SomeOT.top_Concrete_SomeOT_msg3_t * ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_funG_t *
    ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_outputK_t * Word.top_Concrete_W_word EcIArray.top_Array_array
  
  (* Concrete.p1_stage1 *)
  let top_Concrete_p1_stage1 (i1 : bool EcIArray.top_Array_array) (r1 : top_Concrete_rand1_t) (m1 : top_Concrete_msg1_t) =
    SomeOT.top_Concrete_SomeOT_msg2 i1 r1 m1
  
  (* Concrete.p1_stage2 *)
  let top_Concrete_p1_stage2 (st : top_Concrete_state1_t) (m3 : top_Concrete_msg3_t) =
    let (ot_msg_in, fg_in, ko_in, x2g_in) = m3 in
    let ot_out = SomeOT.top_Concrete_SomeOT_result st ot_msg_in in
    let t = Sys.time () in
    let outG =
      ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_evalG fg_in (EcIArray.top_ArrayExt_brbr ot_out x2g_in) in
    (ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_decode ko_in outG,t)
  
  (* Concrete.p2_stage1 *)
  let top_Concrete_p2_stage1 (i2 : ES.ProjScheme.Sch.Scheme.top_Concrete_ES_ProjScheme_Sch_Scheme_fun_t * bool EcIArray.top_Array_array)
                (r2 : top_Concrete_rand2_t) =
    let (fn, x2) = i2 in
    let (r_ot, r_s) = r2 in
    let (n, m, q, a, b) = Pervasives.fst fn in
    let r_f = ES.Local.top_Concrete_ES_Local_randFormat (Pervasives.(+) n q) m r_s in
    let fg = ES.Local.top_Concrete_ES_Local_funG fn r_f in
    let ki = ES.Local.top_Concrete_ES_Local_inputK fn r_f in
    let ko = ES.Local.top_Concrete_ES_Local_outputK fn r_f in
    let x2g =
      ES.ProjScheme.Sch.Scheme.Input.top_Concrete_ES_ProjScheme_Sch_Scheme_Input_encode
        (EcIArray.top_ArrayExt_drop
           (Pervasives.(-) n (EcIArray.top_Array_size (Pervasives.snd i2))) ki) x2 in
    let t = Sys.time () in
    let (st_ot, m1) =
      SomeOT.top_Concrete_SomeOT_msg1
        (EcIArray.top_ArrayExt_take
           (Pervasives.(-) n (EcIArray.top_Array_size (Pervasives.snd i2))) ki)
        (Pervasives.fst r_ot) in
    (((st_ot, fg, ko, x2g, Pervasives.snd r_ot), m1),t)
  
  (* Concrete.p2_stage2 *)
  let top_Concrete_p2_stage2 (st : top_Concrete_state2_t) (m2 : top_Concrete_msg2_t) =
    let (st_ot, fg, ko, x2g, r_ot2) = st in
    let m3 = SomeOT.top_Concrete_SomeOT_msg3 st_ot r_ot2 m2 in (m3, fg, ko, x2g)

end
