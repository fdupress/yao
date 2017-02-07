%{
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
%}

%token <string> INT
%token I1
%token I2
%token FN
%token OTR1
%token OTR2
%token GR

%token SCOLON
%token EQ
%token LANGLE
%token RANGLE

%token EOF

%start main
%type <Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list> main
%%
main: i1 i2 fn randoms EOF { ($1,$2,$3,$4) };

i1:
 | I1 EQ INT            { Full (toBoolArray $3) }
 | I1 LANGLE INT RANGLE { Rand (int_of_string $3) };
i2:
 | I2 EQ INT            { Full (toBoolArray $3) }
 | I2 LANGLE INT RANGLE { Rand (int_of_string $3) };

fn: FN EQ INT SCOLON INT SCOLON INT SCOLON intlist SCOLON intlist SCOLON intlist { toCircuit $3 $5 $7 $9 $11 $13 };

randoms: 
 | OTR1 EQ intlist randoms            { (otr1 $3)::$4    }
 | OTR2 EQ intlist SCOLON INT randoms { (otr2 $3 $5)::$6 }
 | GR   EQ intlist randoms            { (gr $3)::$4      }
 |                                    { []               }
;

intlist:
| { [] }
| INT intlist { $1::$2 };
