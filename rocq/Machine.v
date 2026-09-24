From BusyCoq Require Export Individual62.
From Coq Require Import NArith List String.
Import ListNotations.

Open Scope nat_scope.

Definition tm : TM := Eval compute in
  TM_from_str "1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC".

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Definition gap (n : nat) (tail : side) : side :=
  [S1]^^n *> [S0] *> tail.

Fixpoint gaps (xs : list nat) (tail : side) : side :=
  match xs with
  | [] => tail
  | x :: xs => gap x (gaps xs tail)
  end.

Definition pivot (l r : side) : Q * tape :=
  l {{A}}> [S0] *> r.

Definition G (l r : list nat) : Q * tape :=
  pivot (gaps l 0inf) (gaps r 0inf).

Fixpoint paired (w : list nat) : list nat :=
  match w with [] => [] | x :: xs => x :: 1 :: paired xs end.

Definition Cword (w : list nat) : Q * tape := G (0 :: paired w) [].

Definition K (a b : nat) : Q * tape :=
  Cword ([2;0;2] ++ repeat 0 a ++ [3] ++ repeat 2 b).

Definition K2 (b : N) : Q * tape := K 2 (N.to_nat b).

Definition Hword (c z t : nat) : Q * tape :=
  Cword ([1] ++ repeat 3 c ++ [2] ++ repeat 0 z ++ [3] ++ repeat 2 t).

Fixpoint binary_word (width : nat) (value : N) : list nat :=
  match width with
  | 0 => []
  | S width => (if N.odd value then 2 else 0) ::
      binary_word width (N.div2 value)
  end.

Definition register (h : nat) (u : list nat) (v : N) (width : nat)
    (suffix : list nat) : Q * tape :=
  Cword (h :: u ++ binary_word width v ++ suffix).

Definition Pside (w : list nat) : side := gaps (paired w) 0inf.

Definition marker_word (prefix : list nat) (z t : nat) : Q * tape :=
  Cword (prefix ++ repeat 0 z ++ [3] ++ repeat 2 t).
