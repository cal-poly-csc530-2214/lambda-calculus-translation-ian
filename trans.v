(*
LC = num
   |	 	id
   |	 	(/ id => LC)
   |	 	(LC LC)
   |	 	(+ LC LC)
   |	 	( * LC LC)
   |	 	(ifleq0 LC LC LC)
   |	 	(println LC)
*)

From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Numbers.DecimalString.
Import ListNotations.
Import NilEmpty.

(*Lexing*)

Definition isWhite (c : ascii) : bool :=
  let n:= nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* LF *)
           (n =? 13)). (* CR *)

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype :=
  | white
  | alpha
  | digit
  | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s => c :: (list_of_string s)
  end.

Definition classifyString (s :string) : chartype :=
  let c := (hd (ascii_of_nat 0) (list_of_string s)) in
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition natToDigit (n : nat) : ascii :=
    match n with
      | 0 => "0"
      | 1 => "1"
      | 2 => "2"
      | 3 => "3"
      | 4 => "4"
      | 5 => "5"
      | 6 => "6"
      | 7 => "7"
      | 8 => "8"
      | _ => "9"
    end.


Fixpoint writeNatAux (steps n : nat) (acc : string) : string :=
      let acc' := String (natToDigit (n mod 10)) acc in
      match steps with
        | 0 => acc'
        | S steps' =>
          match n / 10 with
            | 0 => acc'
            | n' => writeNatAux steps' n' acc'
          end
      end.

Definition writeNat (n : nat) : string :=
        writeNatAux n n "".

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii) : list (list ascii) :=
  let tk := match acc with nil => nil | _::_ => [rev acc] end in 
  match xs with
  | nil => tk
  | (x :: xs') =>
    match cls, classifyChar x, x with
    | _, _, "(" =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")" =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
  tokenize "abc12=3 223*(3+(a+c))" %string = 
  ["abc"; "12"; "="; "3"; "223";
     "*"; "("; "3"; "+"; "(";
     "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.

Example tokenize_ex2 : 
  tokenize "(+ 5 3)" %string =
  ["("; "+"; "5"; "3"; ")"]%string.
Proof. reflexivity. Qed.

Example tokenize_ex3 :
  tokenize "(println ((/ x => x) (+ 343 201)))" %string =
  ["("; "println"; "("; "("; "/"; "x"; "=>"; "x"; ")";
   "(";"+"; "343"; "201"; ")"; ")";")"]%string.
Proof. reflexivity. Qed.

(*
Parse to AST
Adapted from Software Foundations ImpParser
Uses step-indexed parsing to ensure termination
*)

Inductive expr : Type :=
  | num : nat -> expr
  | id : string -> expr
  | app : expr -> expr -> expr
  | abs : string -> expr -> expr
  | plus : expr -> expr -> expr
  | mult : expr -> expr -> expr
  | ifleq0 : expr -> expr -> expr -> expr
  | println : expr -> expr
  | empty.

Inductive OptionE (X : Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3"
   := (match e1 with
       | SomeE p => e2
       | NoneE _ => e3
       end)
   (right associativity, p pattern,
    at level 60, e1 at next level, e2 at next level).

Definition parser (T : Type) :=
  list token -> OptionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
    match steps, p xs with
    | 0, _ =>
        NoneE "Too many recursive calls"
    | _, NoneE _ =>
        SomeE ((rev acc), xs)
    | S steps', SomeE (t, xs') =>
        many_helper p (t :: acc) steps' xs'
    end.

Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Definition firstExpect {T} (t : token) (p : parser T) : parser T :=
  fun xs => match xs with
            | x :: xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>  NoneE ("expected '" ++ t  ++ "'.")
            end.

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

Definition parseID (xs : list token) : OptionE (string * list token) := 
  match xs with 
  | [] => NoneE "Expected identifier"
  | x :: xs' => if forallb isAlpha (list_of_string x) then
                  SomeE (x, xs')
                else
                  NoneE ("Illegal ID: '" ++ x ++ "'")
  end.

Definition parseNum (xs : list token) : OptionE (nat * list token) :=
  match xs with
  | [] => NoneE "Expected number"
  | x :: xs' => if forallb isDigit (list_of_string x) then
                  SomeE (fold_left
                              (fun n d => 
                                10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
                                (list_of_string x) 0
                        , xs')
                else
                  NoneE ("Illegal number: '" ++ x ++ "'")
  end.

Example parsenum_ex1 :
  parseNum (tokenize "222" %string) =
  SomeE(222, []).
Proof. reflexivity. Qed.

Example parsenum_ex2 :
  parseNum (tokenize "abc" %string) =
  NoneE("Illegal number: 'abc'").
Proof. reflexivity. Qed.

Example parseid_ex1 :
  parseID (tokenize "abc" %string) =
  SomeE("abc" %string, []).
Proof. reflexivity. Qed.

Example parseid_ex2 :
  parseID (tokenize "222" %string) =
  NoneE("Illegal ID: '222'").
Proof. reflexivity. Qed.

Fixpoint parseProg (steps : nat) (xs : list token) : OptionE (expr * list token) :=
  match steps with
  | O => NoneE "Too many recursive calls"
  | S steps' =>
    TRY ' (i, rest) <- parseID xs ;; 
      SomeE (id(i), rest) (* Just an id *)
    OR
    TRY ' (n, rest) <- parseNum xs ;;
      SomeE (num(n), rest) (* Just a number *)
    OR
    ' (e, rest) <- firstExpect "(" %string (parseExpr steps') xs ;;
    ' (u, rest') <- expect ")" %string rest ;;
    SomeE (e, rest') (* Otherwise, an expression *)
  end

with parseExpr (steps : nat) (xs : list token) :=
  match steps with 
  | O => NoneE "Too many recursive calls"
  | S steps' =>
    TRY ' (e1, rest) <- firstExpect "*" %string (parseProg steps') xs ;;
        ' (e2, rest') <- parseProg steps' rest ;;
          SomeE (mult e1 e2, rest') (* Multiplication expression *)
    OR
    TRY ' (e1, rest) <- firstExpect "+" %string (parseProg steps') xs ;;
        ' (e2, rest') <- parseProg steps' rest ;;
          SomeE (plus e1 e2, rest') (* Addition expression *)
    OR
    TRY ' (i, rest) <- firstExpect "/" %string parseID xs ;;
        ' (u, rest') <- expect "=>" %string rest ;;
        ' (e, rest'') <- parseProg steps' rest' ;;
          SomeE (abs i e, rest'') (* Lambda expression *)
    OR
    TRY ' (e1, rest) <- firstExpect "ifleq0" %string (parseProg steps') xs ;;
        ' (e2, rest') <- parseProg steps' rest ;;
        ' (e3, rest'') <- parseProg steps' rest' ;;
          SomeE (ifleq0 e1 e2 e3, rest'') (* ifleq0 expression *)
    OR
    TRY ' (e, rest) <- firstExpect "println" %string (parseProg steps') xs ;;
          SomeE (println e, rest) (* println expression *)
    OR
        ' (e1, rest) <- parseProg steps' xs ;;
        ' (e2, rest') <- parseProg steps' rest ;;
          SomeE (app e1 e2, rest') (* application *)
  end.

Definition stepnumber := 1000.

Definition parse (str : string) : OptionE expr :=
  let tokens := tokenize str in
  match parseProg stepnumber tokens with
  | SomeE (e, []) => SomeE e
  | SomeE (_, t::_) => NoneE ("Trailing tokens remaining: " ++ t)
  | NoneE err => NoneE err
  end.

Example parse_ex1 :
  parse "(println ((/ x => x) (+ 343 201)))" =
  SomeE (println (app (abs "x" (id "x")) (plus (num 343) (num 201)))).
Proof. reflexivity. Qed. 

Example parse_ex2 :
  parse "(println 5) z" =
  NoneE "Trailing tokens remaining: z".
Proof. reflexivity. Qed.

(*Translate AST to Python code*)

Fixpoint python (e : expr) : string :=
  match e with 
  | num n => writeNat n
  | id i => i
  | app f v => "(" ++ python f ++ "(" ++ python v ++ "))"
  | abs x e => "(lambda " ++ x ++ ": " ++ python e ++ ")" 
  | plus e1 e2 => "(" ++ python e1 ++ " + " ++ python e2 ++ ")"
  | mult e1 e2 => "(" ++ python e1 ++ " * " ++ python e2 ++ ")"
  | ifleq0 g t e => "(" ++ python t ++ " if (" ++ python g ++ " <= 0) else " ++ python e ++ ")"
  | println e => "print(" ++ python e ++ ")"
  | empty => ""
  end.

Definition pyOption (e : OptionE expr) : string :=
  match e with
  | SomeE e => python e
  | NoneE err => err
  end.

Example py_ex1 :
  pyOption (parse "(println ((/ x => x) (+ 343 201)))") =
  "print(((lambda x: x)((343 + 201))))"%string.
Proof. reflexivity. Qed.
