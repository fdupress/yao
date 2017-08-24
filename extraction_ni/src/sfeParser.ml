
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | SCOLON
    | RANGLE
    | OTR2
    | OTR1
    | LANGLE
    | INT of (
# 57 "src/sfeParser.mly"
       (string)
# 16 "src/sfeParser.ml"
  )
    | I2
    | I1
    | GR
    | FN
    | EQ
    | EOF
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState42
  | MenhirState41
  | MenhirState39
  | MenhirState38
  | MenhirState36
  | MenhirState33
  | MenhirState31
  | MenhirState29
  | MenhirState27
  | MenhirState24
  | MenhirState23

# 1 "src/sfeParser.mly"
  
open Utils
open SFE

let toBoolArray s =
  (* Printf.printf "Reading %i bits.\n" (String.length s); flush stdout; *)
  Array.init (String.length s) (fun i -> s.[i] <> '0')

let of_hex (s:string): string =
  (* Printf.printf "Reading %i hex digits.\n" (String.length s); flush stdout; *)
  let res = String.make (String.length s / 2) '\000' in
  for i = 0 to (String.length s / 2 - 1) do
    res.[i] <- char_of_int (int_of_string (String.concat "" ["0x";String.sub s (i * 2) 2]));
  done;
  res

let intlist_to_tokenarray is =
  let ia = Array.of_list is in
  (* Printf.printf "Reading %i tokens.\n" (Array.length ia); flush stdout; *)
  Array.init (Array.length ia / 2)
    (fun i -> assert (String.length ia.(i * 2) = 32);
              assert (String.length ia.(i * 2 + 1) = 32);
              (of_hex ia.(i * 2),of_hex ia.(i * 2 + 1)))

let intlist_to_intarray is =
  let ia = Array.of_list is in
  (* Printf.printf "Reading %i short integers.\n" (Array.length ia); flush stdout; *)
  Array.map int_of_string ia

let intlist_to_gatearray is =
  let ia = Array.of_list is in
  (* Printf.printf "Reading %i gates.\n" (Array.length ia); flush stdout; *)
  Array.map (fun g -> assert (String.length g = 4); (g.[0] <> '0',g.[1] <> '0',g.[2] <> '0',g.[3] <> '0')) ia

let toCircuit n m q a b g = 
  ((int_of_string n,
   int_of_string m,
   int_of_string q,
   intlist_to_intarray a,
   intlist_to_intarray b),
   intlist_to_gatearray g)

let intlist_to_gfqarray is =
  let ia = Array.of_list is in
  (* Printf.printf "Reading %i long integers.\n" (Array.length ia); flush stdout;  *)
  Array.map Lint.of_string ia

let otr1 rands = OTR1 (intlist_to_gfqarray rands)

let otr2 rands rand = OTR2 (intlist_to_gfqarray rands,Lint.of_string rand)

let gr tokens =
  assert (List.length tokens mod 2 = 0);
  GR (intlist_to_tokenarray tokens)

# 108 "src/sfeParser.ml"

let rec _menhir_goto_randoms : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_randoms -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv165 * _menhir_state)) * _menhir_state * 'tv_intlist) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv163 * _menhir_state)) * _menhir_state * 'tv_intlist) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (_3 : 'tv_intlist)), _, (_4 : 'tv_randoms)) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_randoms = 
# 89 "src/sfeParser.mly"
                                      ( (gr _3)::_4      )
# 125 "src/sfeParser.ml"
         in
        _menhir_goto_randoms _menhir_env _menhir_stack _menhir_s _v) : 'freshtv164)) : 'freshtv166)
    | MenhirState39 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv169 * _menhir_state)) * _menhir_state * 'tv_intlist) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv167 * _menhir_state)) * _menhir_state * 'tv_intlist) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (_3 : 'tv_intlist)), _, (_4 : 'tv_randoms)) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_randoms = 
# 87 "src/sfeParser.mly"
                                      ( (otr1 _3)::_4    )
# 139 "src/sfeParser.ml"
         in
        _menhir_goto_randoms _menhir_env _menhir_stack _menhir_s _v) : 'freshtv168)) : 'freshtv170)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv173 * _menhir_state)) * _menhir_state * 'tv_intlist)) * (
# 57 "src/sfeParser.mly"
       (string)
# 147 "src/sfeParser.ml"
        )) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv171 * _menhir_state)) * _menhir_state * 'tv_intlist)) * (
# 57 "src/sfeParser.mly"
       (string)
# 153 "src/sfeParser.ml"
        )) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _menhir_s), _, (_3 : 'tv_intlist)), (_5 : (
# 57 "src/sfeParser.mly"
       (string)
# 158 "src/sfeParser.ml"
        ))), _, (_6 : 'tv_randoms)) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_randoms = 
# 88 "src/sfeParser.mly"
                                      ( (otr2 _3 _5)::_6 )
# 166 "src/sfeParser.ml"
         in
        _menhir_goto_randoms _menhir_env _menhir_stack _menhir_s _v) : 'freshtv172)) : 'freshtv174)
    | MenhirState31 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv187 * 'tv_i1) * 'tv_i2) * 'tv_fn) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv183 * 'tv_i1) * 'tv_i2) * 'tv_fn) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv181 * 'tv_i1) * 'tv_i2) * 'tv_fn) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, (_1 : 'tv_i1)), (_2 : 'tv_i2)), (_3 : 'tv_fn)), _, (_4 : 'tv_randoms)) = _menhir_stack in
            let _5 = () in
            let _v : (
# 73 "src/sfeParser.mly"
      (Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list)
# 185 "src/sfeParser.ml"
            ) = 
# 75 "src/sfeParser.mly"
                           ( (_1,_2,_3,_4) )
# 189 "src/sfeParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv179) = _menhir_stack in
            let (_v : (
# 73 "src/sfeParser.mly"
      (Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list)
# 196 "src/sfeParser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv177) = Obj.magic _menhir_stack in
            let (_v : (
# 73 "src/sfeParser.mly"
      (Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list)
# 203 "src/sfeParser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv175) = Obj.magic _menhir_stack in
            let ((_1 : (
# 73 "src/sfeParser.mly"
      (Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list)
# 210 "src/sfeParser.ml"
            )) : (
# 73 "src/sfeParser.mly"
      (Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list)
# 214 "src/sfeParser.ml"
            )) = _v in
            (Obj.magic _1 : 'freshtv176)) : 'freshtv178)) : 'freshtv180)) : 'freshtv182)) : 'freshtv184)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv185 * 'tv_i1) * 'tv_i2) * 'tv_fn) * _menhir_state * 'tv_randoms) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)) : 'freshtv188)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_reduce12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_randoms = 
# 90 "src/sfeParser.mly"
                                      ( []               )
# 237 "src/sfeParser.ml"
     in
    _menhir_goto_randoms _menhir_env _menhir_stack _menhir_s _v

and _menhir_run32 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv159 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | INT _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
        | SCOLON ->
            _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33) : 'freshtv160)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv161 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)

and _menhir_run37 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv155 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | INT _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
        | EOF | GR | OTR1 | OTR2 ->
            _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38) : 'freshtv156)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv157 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv151 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | INT _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
        | EOF | GR | OTR1 | OTR2 ->
            _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState41
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41) : 'freshtv152)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv153 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)

and _menhir_goto_intlist : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_intlist -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv115 * _menhir_state * (
# 57 "src/sfeParser.mly"
       (string)
# 334 "src/sfeParser.ml"
        )) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv113 * _menhir_state * (
# 57 "src/sfeParser.mly"
       (string)
# 340 "src/sfeParser.ml"
        )) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (_1 : (
# 57 "src/sfeParser.mly"
       (string)
# 345 "src/sfeParser.ml"
        ))), _, (_2 : 'tv_intlist)) = _menhir_stack in
        let _v : 'tv_intlist = 
# 95 "src/sfeParser.mly"
              ( _1::_2 )
# 350 "src/sfeParser.ml"
         in
        _menhir_goto_intlist _menhir_env _menhir_stack _menhir_s _v) : 'freshtv114)) : 'freshtv116)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((((('freshtv121)) * (
# 57 "src/sfeParser.mly"
       (string)
# 358 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 362 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 366 "src/sfeParser.ml"
        ))) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SCOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv117)) * (
# 57 "src/sfeParser.mly"
       (string)
# 376 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 380 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 384 "src/sfeParser.ml"
            ))) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
            | SCOLON ->
                _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState27
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27) : 'freshtv118)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv119)) * (
# 57 "src/sfeParser.mly"
       (string)
# 404 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 408 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 412 "src/sfeParser.ml"
            ))) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)) : 'freshtv122)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((((((('freshtv127)) * (
# 57 "src/sfeParser.mly"
       (string)
# 421 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 425 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 429 "src/sfeParser.ml"
        ))) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SCOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((((('freshtv123)) * (
# 57 "src/sfeParser.mly"
       (string)
# 439 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 443 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 447 "src/sfeParser.ml"
            ))) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
            | EOF | GR | OTR1 | OTR2 ->
                _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29) : 'freshtv124)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((((('freshtv125)) * (
# 57 "src/sfeParser.mly"
       (string)
# 467 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 471 "src/sfeParser.ml"
            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 475 "src/sfeParser.ml"
            ))) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)) : 'freshtv128)
    | MenhirState29 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((((((((('freshtv135)) * (
# 57 "src/sfeParser.mly"
       (string)
# 484 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 488 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 492 "src/sfeParser.ml"
        ))) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((((((((('freshtv133)) * (
# 57 "src/sfeParser.mly"
       (string)
# 498 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 502 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 506 "src/sfeParser.ml"
        ))) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((let ((((((_menhir_stack, (_3 : (
# 57 "src/sfeParser.mly"
       (string)
# 511 "src/sfeParser.ml"
        ))), (_5 : (
# 57 "src/sfeParser.mly"
       (string)
# 515 "src/sfeParser.ml"
        ))), (_7 : (
# 57 "src/sfeParser.mly"
       (string)
# 519 "src/sfeParser.ml"
        ))), _, (_9 : 'tv_intlist)), _, (_11 : 'tv_intlist)), _, (_13 : 'tv_intlist)) = _menhir_stack in
        let _12 = () in
        let _10 = () in
        let _8 = () in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_fn = 
# 84 "src/sfeParser.mly"
                                                                                 ( toCircuit _3 _5 _7 _9 _11 _13 )
# 531 "src/sfeParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv131) = _menhir_stack in
        let (_v : 'tv_fn) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv129 * 'tv_i1) * 'tv_i2) * 'tv_fn) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | GR ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | OTR1 ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | OTR2 ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | EOF ->
            _menhir_reduce12 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31) : 'freshtv130)) : 'freshtv132)) : 'freshtv134)) : 'freshtv136)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv145 * _menhir_state)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SCOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv141 * _menhir_state)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv137 * _menhir_state)) * _menhir_state * 'tv_intlist)) = Obj.magic _menhir_stack in
                let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 572 "src/sfeParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | GR ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                | OTR1 ->
                    _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                | OTR2 ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                | EOF ->
                    _menhir_reduce12 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36) : 'freshtv138)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv139 * _menhir_state)) * _menhir_state * 'tv_intlist)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)) : 'freshtv142)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv143 * _menhir_state)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)) : 'freshtv146)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv147 * _menhir_state)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | GR ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState39
        | OTR1 ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState39
        | OTR2 ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState39
        | EOF ->
            _menhir_reduce12 _menhir_env (Obj.magic _menhir_stack) MenhirState39
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39) : 'freshtv148)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv149 * _menhir_state)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | GR ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | OTR1 ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | OTR2 ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | EOF ->
            _menhir_reduce12 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42) : 'freshtv150)
    | _ ->
        _menhir_fail ()

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv91 * _menhir_state)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState39 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv95 * _menhir_state)) * _menhir_state * 'tv_intlist) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv97 * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv99 * _menhir_state)) * _menhir_state * 'tv_intlist)) * (
# 57 "src/sfeParser.mly"
       (string)
# 671 "src/sfeParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv101 * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState31 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv103 * 'tv_i1) * 'tv_i2) * 'tv_fn) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv104)
    | MenhirState29 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((((((('freshtv105)) * (
# 57 "src/sfeParser.mly"
       (string)
# 689 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 693 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 697 "src/sfeParser.ml"
        ))) * _menhir_state * 'tv_intlist)) * _menhir_state * 'tv_intlist)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((((('freshtv107)) * (
# 57 "src/sfeParser.mly"
       (string)
# 706 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 710 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 714 "src/sfeParser.ml"
        ))) * _menhir_state * 'tv_intlist)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv109 * _menhir_state * (
# 57 "src/sfeParser.mly"
       (string)
# 723 "src/sfeParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv111)) * (
# 57 "src/sfeParser.mly"
       (string)
# 732 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 736 "src/sfeParser.ml"
        ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 740 "src/sfeParser.ml"
        ))) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv112)

and _menhir_reduce6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_intlist = 
# 94 "src/sfeParser.mly"
  ( [] )
# 749 "src/sfeParser.ml"
     in
    _menhir_goto_intlist _menhir_env _menhir_stack _menhir_s _v

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "src/sfeParser.mly"
       (string)
# 756 "src/sfeParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | EOF | GR | OTR1 | OTR2 | SCOLON ->
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24

and _menhir_goto_i2 : _menhir_env -> 'ttv_tail -> 'tv_i2 -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv89 * 'tv_i1) * 'tv_i2) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv85) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv81) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv77)) = Obj.magic _menhir_stack in
                let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 798 "src/sfeParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | SCOLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv73)) * (
# 57 "src/sfeParser.mly"
       (string)
# 809 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | INT _v ->
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : ((('freshtv69)) * (
# 57 "src/sfeParser.mly"
       (string)
# 819 "src/sfeParser.ml"
                        ))) = Obj.magic _menhir_stack in
                        let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 824 "src/sfeParser.ml"
                        )) = _v in
                        ((let _menhir_stack = (_menhir_stack, _v) in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        match _tok with
                        | SCOLON ->
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : (((('freshtv65)) * (
# 57 "src/sfeParser.mly"
       (string)
# 835 "src/sfeParser.ml"
                            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 839 "src/sfeParser.ml"
                            )) = Obj.magic _menhir_stack in
                            ((let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            match _tok with
                            | INT _v ->
                                let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : ((((('freshtv61)) * (
# 57 "src/sfeParser.mly"
       (string)
# 849 "src/sfeParser.ml"
                                ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 853 "src/sfeParser.ml"
                                ))) = Obj.magic _menhir_stack in
                                let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 858 "src/sfeParser.ml"
                                )) = _v in
                                ((let _menhir_stack = (_menhir_stack, _v) in
                                let _menhir_env = _menhir_discard _menhir_env in
                                let _tok = _menhir_env._menhir_token in
                                match _tok with
                                | SCOLON ->
                                    let (_menhir_env : _menhir_env) = _menhir_env in
                                    let (_menhir_stack : (((((('freshtv57)) * (
# 57 "src/sfeParser.mly"
       (string)
# 869 "src/sfeParser.ml"
                                    ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 873 "src/sfeParser.ml"
                                    ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 877 "src/sfeParser.ml"
                                    )) = Obj.magic _menhir_stack in
                                    ((let _menhir_env = _menhir_discard _menhir_env in
                                    let _tok = _menhir_env._menhir_token in
                                    match _tok with
                                    | INT _v ->
                                        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
                                    | SCOLON ->
                                        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState23
                                    | _ ->
                                        assert (not _menhir_env._menhir_error);
                                        _menhir_env._menhir_error <- true;
                                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23) : 'freshtv58)
                                | _ ->
                                    assert (not _menhir_env._menhir_error);
                                    _menhir_env._menhir_error <- true;
                                    let (_menhir_env : _menhir_env) = _menhir_env in
                                    let (_menhir_stack : (((((('freshtv59)) * (
# 57 "src/sfeParser.mly"
       (string)
# 897 "src/sfeParser.ml"
                                    ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 901 "src/sfeParser.ml"
                                    ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 905 "src/sfeParser.ml"
                                    )) = Obj.magic _menhir_stack in
                                    (raise _eRR : 'freshtv60)) : 'freshtv62)
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : ((((('freshtv63)) * (
# 57 "src/sfeParser.mly"
       (string)
# 915 "src/sfeParser.ml"
                                ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 919 "src/sfeParser.ml"
                                ))) = Obj.magic _menhir_stack in
                                (raise _eRR : 'freshtv64)) : 'freshtv66)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : (((('freshtv67)) * (
# 57 "src/sfeParser.mly"
       (string)
# 929 "src/sfeParser.ml"
                            ))) * (
# 57 "src/sfeParser.mly"
       (string)
# 933 "src/sfeParser.ml"
                            )) = Obj.magic _menhir_stack in
                            (raise _eRR : 'freshtv68)) : 'freshtv70)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : ((('freshtv71)) * (
# 57 "src/sfeParser.mly"
       (string)
# 943 "src/sfeParser.ml"
                        ))) = Obj.magic _menhir_stack in
                        (raise _eRR : 'freshtv72)) : 'freshtv74)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv75)) * (
# 57 "src/sfeParser.mly"
       (string)
# 953 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    (raise _eRR : 'freshtv76)) : 'freshtv78)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv79)) = Obj.magic _menhir_stack in
                (raise _eRR : 'freshtv80)) : 'freshtv82)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv83) = Obj.magic _menhir_stack in
            (raise _eRR : 'freshtv84)) : 'freshtv86)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv87 * 'tv_i1) * 'tv_i2) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv88)) : 'freshtv90)

and _menhir_goto_i1 : _menhir_env -> 'ttv_tail -> 'tv_i1 -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv55 * 'tv_i1) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | I2 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv51) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv35) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv31)) = Obj.magic _menhir_stack in
                let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 1001 "src/sfeParser.ml"
                )) = _v in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv29)) = Obj.magic _menhir_stack in
                let ((_3 : (
# 57 "src/sfeParser.mly"
       (string)
# 1009 "src/sfeParser.ml"
                )) : (
# 57 "src/sfeParser.mly"
       (string)
# 1013 "src/sfeParser.ml"
                )) = _v in
                ((let _2 = () in
                let _1 = () in
                let _v : 'tv_i2 = 
# 81 "src/sfeParser.mly"
                        ( Full (toBoolArray _3) )
# 1020 "src/sfeParser.ml"
                 in
                _menhir_goto_i2 _menhir_env _menhir_stack _v) : 'freshtv30)) : 'freshtv32)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv33)) = Obj.magic _menhir_stack in
                (raise _eRR : 'freshtv34)) : 'freshtv36)
        | LANGLE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv47) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv43)) = Obj.magic _menhir_stack in
                let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 1041 "src/sfeParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RANGLE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv39)) * (
# 57 "src/sfeParser.mly"
       (string)
# 1052 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv37)) * (
# 57 "src/sfeParser.mly"
       (string)
# 1059 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, (_3 : (
# 57 "src/sfeParser.mly"
       (string)
# 1064 "src/sfeParser.ml"
                    ))) = _menhir_stack in
                    let _4 = () in
                    let _2 = () in
                    let _1 = () in
                    let _v : 'tv_i2 = 
# 82 "src/sfeParser.mly"
                        ( Rand (int_of_string _3) )
# 1072 "src/sfeParser.ml"
                     in
                    _menhir_goto_i2 _menhir_env _menhir_stack _v) : 'freshtv38)) : 'freshtv40)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv41)) * (
# 57 "src/sfeParser.mly"
       (string)
# 1082 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    (raise _eRR : 'freshtv42)) : 'freshtv44)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv45)) = Obj.magic _menhir_stack in
                (raise _eRR : 'freshtv46)) : 'freshtv48)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv49) = Obj.magic _menhir_stack in
            (raise _eRR : 'freshtv50)) : 'freshtv52)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv53 * 'tv_i1) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv54)) : 'freshtv56)

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and main : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 73 "src/sfeParser.mly"
      (Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list)
# 1119 "src/sfeParser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = Obj.magic () in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_error = false;
      }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv27) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | I1 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv7) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv3)) = Obj.magic _menhir_stack in
                let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 1156 "src/sfeParser.ml"
                )) = _v in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1)) = Obj.magic _menhir_stack in
                let ((_3 : (
# 57 "src/sfeParser.mly"
       (string)
# 1164 "src/sfeParser.ml"
                )) : (
# 57 "src/sfeParser.mly"
       (string)
# 1168 "src/sfeParser.ml"
                )) = _v in
                ((let _2 = () in
                let _1 = () in
                let _v : 'tv_i1 = 
# 78 "src/sfeParser.mly"
                        ( Full (toBoolArray _3) )
# 1175 "src/sfeParser.ml"
                 in
                _menhir_goto_i1 _menhir_env _menhir_stack _v) : 'freshtv2)) : 'freshtv4)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv5)) = Obj.magic _menhir_stack in
                (raise _eRR : 'freshtv6)) : 'freshtv8)
        | LANGLE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv19) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv15)) = Obj.magic _menhir_stack in
                let (_v : (
# 57 "src/sfeParser.mly"
       (string)
# 1196 "src/sfeParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RANGLE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv11)) * (
# 57 "src/sfeParser.mly"
       (string)
# 1207 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv9)) * (
# 57 "src/sfeParser.mly"
       (string)
# 1214 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, (_3 : (
# 57 "src/sfeParser.mly"
       (string)
# 1219 "src/sfeParser.ml"
                    ))) = _menhir_stack in
                    let _4 = () in
                    let _2 = () in
                    let _1 = () in
                    let _v : 'tv_i1 = 
# 79 "src/sfeParser.mly"
                        ( Rand (int_of_string _3) )
# 1227 "src/sfeParser.ml"
                     in
                    _menhir_goto_i1 _menhir_env _menhir_stack _v) : 'freshtv10)) : 'freshtv12)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv13)) * (
# 57 "src/sfeParser.mly"
       (string)
# 1237 "src/sfeParser.ml"
                    )) = Obj.magic _menhir_stack in
                    (raise _eRR : 'freshtv14)) : 'freshtv16)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv17)) = Obj.magic _menhir_stack in
                (raise _eRR : 'freshtv18)) : 'freshtv20)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv21) = Obj.magic _menhir_stack in
            (raise _eRR : 'freshtv22)) : 'freshtv24)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv25) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv26)) : 'freshtv28))

# 219 "/Users/vm2p/.opam/4.02.3/lib/menhir/standard.mly"
  


# 1263 "src/sfeParser.ml"
