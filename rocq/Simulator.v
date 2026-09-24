From Coq Require Import NArith ZArith List Bool.
From MinimalSim Require Export Derivation.
Import ListNotations.

Open Scope N_scope.

Inductive outcome (S R : Type) :=
| Continue : S -> outcome S R
| Stop : R -> outcome S R.
Arguments Continue {S R} _.
Arguments Stop {S R} _.

Definition bind {S R} (x : outcome S R) (f : S -> outcome S R) :=
  match x with Continue s => f s | Stop r => Stop r end.

Section Iteration.
Context {S R : Type} (next : S -> outcome S R).

Fixpoint iter_pos (p : positive) (s : S) : outcome S R :=
  match p with
  | xH => next s
  | xO q => bind (iter_pos q s) (iter_pos q)
  | xI q => bind (iter_pos q s) (fun t => bind (iter_pos q t) next)
  end.

Definition iter (n : N) (s : S) : outcome S R :=
  match n with N0 => Continue s | Npos p => iter_pos p s end.
End Iteration.

Record register := Reg {
  rg_head : N;
  rg_word : list N;
  rg_value : N;
  rg_width : N
}.

Fixpoint positive_population (p : positive) : N :=
  match p with
  | xH => 1
  | xO q => positive_population q
  | xI q => 1 + positive_population q
  end.

Definition popcount (v : N) : N :=
  match v with N0 => 0 | Npos p => positive_population p end.

Fixpoint positive_lowbit (p : positive) : N :=
  match p with xO q => 2 * positive_lowbit q | _ => 1 end.

Definition lowbit (v : N) : N :=
  match v with N0 => 0 | Npos p => positive_lowbit p end.

Definition word_length (w : list N) : N := N.of_nat (length w).

Definition odd_word (w : list N) : bool :=
  forallb (fun d => (d =? 1) || (d =? 3)) w.

Definition register_mode (s : register) : option mode :=
  match rg_word s with
  | [] =>
      if (rg_head s =? 2) && (rg_value s =? 2) then Some M202 else
      if (rg_head s =? 0) && (rg_value s =? 4) then Some M0002 else
      if (rg_head s =? 1) && (rg_value s =? 3) then Some M122 else None
  | _ =>
      if (rg_head s =? 1) && (rg_value s =? 1) &&
         forallb (fun d => d =? 3) (rg_word s)
      then Some MH else None
  end.

Definition register_guard (s : register) : bool :=
  (rg_head s <? 5) && (0 <? rg_value s) && odd_word (rg_word s) &&
  (N.size (rg_value s) + 4 <=? rg_width s).

Definition advance_raw (s : register) : register * N * N :=
  let '(Reg h u v n) := s in
  let '(first, rest) := match u with [] => (3, []) | d :: w => (d,w) end in
  let marker := match u with [] => [] | _ => [3] end in
  let r := v mod 4 in
  if (h =? 0) || (h =? 2) then
    match u with
    | _ :: _ => (Reg (first + (if h =? 0 then 1 else 0)) rest (v+1) n, 3, 1)
    | [] =>
        (Reg ((if h =? 0 then 3 else 2) - (if N.odd v then 2 else 0)) []
             ((v+1)/2) (n-1), (if N.odd v then 3 else 2), 1)
    end
  else if (h =? 1) || (h =? 3) then
    if N.odd v then (Reg (h-1) u (v+1) n, 2, 1)
    else (Reg (first + (if h =? 1 then 1 else 0))
              (rest ++ marker ++ [3-r]) ((v+3)/4) (n-2),
          (if r =? 2 then 3 else 2), 1)
  else if match u with [] => false | d :: _ => d =? 1 end then
    if N.odd v then (Reg 3 rest (v+2) n, 6, 1)
    else (Reg 3 (rest ++ [3;3-r]) ((v+3)/4) (n-2),
          (if r =? 2 then 4 else 3), (if r =? 2 then 2 else 1))
  else
    let value := if N.odd v then (v+3)/4 else
                 if r =? 2 then v/4+2 else (v+3*lowbit v)/4 in
    (Reg 1 (rest ++ marker ++ [if r =? 3 then 3 else 1]) value (n-2),
     (if r =? 3 then 5 else 6), (if r =? 2 then 2 else 1)).

Definition advance (s : register) : option (register * N * N) :=
  if register_guard s then Some (advance_raw s) else None.

Record summary := Summary {
  sum_state : register;
  sum_base : N;
  sum_returns : N;
  sum_equations : N
}.

Inductive normalize_result :=
| Normalized (result : summary)
| GuardError (result : summary)
| OutOfFuel (result : summary).

Definition initial_summary s := Summary s 0 0 0.

Definition summary_advance (a : summary) : option summary :=
  match advance (sum_state a) with
  | None => None
  | Some (s,b,r) => Some (Summary s (sum_base a+b)
                                  (sum_returns a+r) (sum_equations a+1))
  end.

Definition normalization_next (a : summary) : outcome summary normalize_result :=
  match register_mode (sum_state a) with
  | Some _ => Stop (Normalized a)
  | None =>
      match summary_advance a with
      | None => Stop (GuardError a)
      | Some b => Continue b
      end
  end.

Definition normalize_fuel (fuel : N) (s : register) : normalize_result :=
  match iter normalization_next fuel (initial_summary s) with
  | Stop result => result
  | Continue a => OutOfFuel a
  end.

Definition normalization_budget (s : register) : N :=
  2 * (rg_width s + word_length (rg_word s)) + 2.

Definition normalize (s : register) : normalize_result :=
  normalize_fuel (normalization_budget s) s.

Fixpoint valuation_pos (p : positive) : N :=
  match p with
  | xO q => 1 + valuation_pos q
  | _ => 0
  end.

Definition valuation (n : N) : N :=
  match n with N0 => 0 | Npos p => valuation_pos p end.

Definition k_one (b : N) : N :=
  if b mod 4 =? 3 then 64*b + 547 else 8*b + 56 + 3*(b mod 4).

Definition k_zero (b : N) : N :=
  if N.even b then
    let x := 7*b + 20 in
    let k := valuation x in
    (9^k * N.shiftr x k - 69)/7
  else
    let x := 721*b + 1917 in
    let k := valuation x in
    let count := (k - 1)/3 in
    let b' := (729^count * N.shiftr x (3*count) - 1917)/721 in
    let residue := k - 3*count in
    if residue =? 1 then k_one ((9*b' + 13)/2)
    else if residue =? 2 then k_one ((81*b' + 193)/4)
    else (729*b' + 1861)/8.

Definition k_three (b : N) : N :=
  let r := b mod 4 in
  if r =? 0 then (9*b + 94)/2
  else if r =? 2 then k_zero ((9*b + 108)/2)
  else if r =? 3 then k_one ((9*b + 101)/2)
  else
    let b' := (9*b + 87)/2 in
    if b' mod 4 =? 0 then (9*b' + 94)/2
    else k_zero ((9*b' + 108)/2).

Definition canonical (a b : N) : N :=
  let b' := b + 14*(a/4) in
  let r := a mod 4 in
  if r =? 0 then k_zero b'
  else if r =? 1 then k_one b'
  else if r =? 2 then b'
  else k_three b'.

Definition to_two (a b : N) : option N :=
  if 40 <=? b then Some (canonical a b) else None.

Definition minimum : N := 131072.

Inductive fault :=
| InputGuard | RegisterGuard | RegisterFuel | PopulationGuard
| MarkerGuard | MarkerDerivation | CanonicalGuard
| MiddleGuard | FinalDescent | FinalFuel | GrowthGuard
| BootstrapDerivation | BootstrapFuel.

Inductive checked (A : Type) := Good : A -> checked A | Error : fault -> checked A.

Arguments Good {A} _.

Arguments Error {A} _.

Definition check_bind {A B} (x : checked A) (f : A -> checked B) : checked B :=
  match x with Good a => f a | Error e => Error e end.

Notation "'let!' x ':=' e 'in' f" := (check_bind e (fun x => f))
  (at level 200, x name, e at level 100, f at level 200).

Record normal_form := Normal {
  nf_mode : mode;
  nf_c : N;
  nf_zeros : N;
  nf_tail : N
}.

Definition normal (h : N) (u : list N) (v width tail0 : N)
    : checked normal_form :=
  match normalize (Reg h u v width) with
  | Normalized s =>
    let r := sum_state s in
    match register_mode r with
    | None => Error RegisterGuard
    | Some m =>
      if popcount (rg_value r) <=? tail0 + sum_base s then
        Good (Normal m (N.of_nat (length (rg_word r)))
          (rg_width r - N.size (rg_value r))
          (tail0 + sum_base s - popcount (rg_value r)))
      else Error PopulationGuard
    end
  | GuardError _ => Error RegisterGuard
  | OutOfFuel _ => Error RegisterFuel
  end.

Definition period m : N :=
  match m with M202 => 4 | MH => 2 | _ => 3 end.

Definition growth m : N :=
  match m with M202 => 14 | MH => 10 | _ => 12 end.

Definition zero_remainder (s : normal_form) : normal_form :=
  Normal (nf_mode s) (nf_c s) (nf_zeros s mod period (nf_mode s))
    (nf_tail s + growth (nf_mode s)*(nf_zeros s / period (nf_mode s))).

Definition final_small_guard (s : normal_form) : bool :=
  match nf_mode s with
  | M0002 | M122 => (nf_c s =? 0) && (nf_zeros s <? 3)
  | MH => (nf_zeros s <=? 1) && N.even (nf_c s) && (2 <=? nf_c s)
      && (nf_c s <=? if nf_zeros s =? 1 then 16 else 14)
  | M202 => false
  end.

Definition checked_canonical (a b : N) : checked N :=
  match to_two a b with Some B => Good B | None => Error CanonicalGuard end.

Definition final_small (s : normal_form) : checked N :=
  if final_small_guard s && (100 <=? nf_tail s / 24) then
    match lookup_final (nf_mode s) (nf_c s) (nf_zeros s) (nf_tail s mod 24) with
    | Some (a,b) =>
      match evaluate a (nf_tail s / 24), evaluate b (nf_tail s / 24) with
      | Some av, Some bv => checked_canonical av bv
      | _, _ => Error MarkerDerivation
      end
    | None => Error MarkerDerivation
    end
  else Error MarkerGuard.

Inductive result :=
| Returned : N -> result
| Halted : N -> N -> result
| Invalid : fault -> result
| Exhausted : N -> result.

Definition returned_checked (x : checked N) : result :=
  match x with Good b => Returned b | Error e => Invalid e end.

Definition finish_next (s : normal_form) : outcome normal_form result :=
  if 2400 <=? nf_tail s then
    match nf_mode s with
    | M202 => Stop (returned_checked (checked_canonical (nf_zeros s) (nf_tail s)))
    | _ =>
      let s := zero_remainder s in
      match nf_mode s with
      | MH =>
        let c := nf_c s in let t := nf_tail s in
        if (2 <=? c) && N.even c && (3*c + 100 <=? t) then
          if nf_zeros s =? 1 then
            if 18 <=? c then Stop (Halted c t)
            else Stop (returned_checked (final_small s))
          else if c <=? 14 then Stop (returned_checked (final_small s))
          else
            match normal 2 [] (c/2-1) (t-c-9) (t+10*c+58) with
            | Good s' =>
              if (t <? nf_tail s') &&
                match nf_mode s' with MH => nf_c s' <=? c-4 | _ => true end
              then Continue s' else Stop (Invalid FinalDescent)
            | Error e => Stop (Invalid e)
            end
        else Stop (Invalid MarkerGuard)
      | _ => Stop (returned_checked (final_small s))
      end
    end
  else Stop (Invalid MarkerGuard).

Definition finish (s : normal_form) : result :=
  match iter finish_next (nf_c s + 1) s with
  | Stop r => r
  | Continue _ => Invalid FinalFuel
  end.

Definition middle_large (s : normal_form) (width : N) : checked normal_form :=
  let c := nf_c s in let z := nf_zeros s in
  if 2*c+100 <=? width then
    if z =? 1 then
      if N.even c then normal 1 [3;1] (c/2-1) (width-c-5) (nf_tail s+10*c+41)
      else normal 2 [] ((c+1)/2) (width-c-8) (nf_tail s+10*c+57)
    else if N.odd c then
      normal 2 [] ((c+3)/2) (width-c-5) (nf_tail s+10*c+34)
    else normal 2 [] (c/2+2) (width-c-2) (nf_tail s+10*c+25)
  else Error MiddleGuard.

Definition middle (s : normal_form) (width : N) : checked normal_form :=
  match nf_mode s with
  | MH => if 10 <=? nf_c s then middle_large s width else
      match lookup_middle (nf_mode s) (nf_c s) (nf_zeros s) with
      | Some (m,c,loss,extra) =>
        if loss <=? width then Good (Normal m c (width-loss) (nf_tail s+extra))
        else Error MiddleGuard
      | None => Error MarkerDerivation
      end
  | _ =>
      match lookup_middle (nf_mode s) (nf_c s) (nf_zeros s) with
      | Some (m,c,loss,extra) =>
        if loss <=? width then Good (Normal m c (width-loss) (nf_tail s+extra))
        else Error MiddleGuard
      | None => Error MarkerDerivation
      end
  end.

Definition entry (b : N) : checked normal_form :=
  let n := b/2 in
  if N.even b then normal 2 [] (n+6) (4*n+18) (9*n+51)
  else
    let! s := normal 1 [3] (2*n+11) (4*n+20) (9*n+48) in
    middle (zero_remainder s) (4*n+19).

Definition return_map (b : N) : result :=
  if 2 <=? b then
    match entry b with
    | Error e => Invalid e
    | Good s =>
      if 8*(b/2) <=? nf_tail s then
        match finish s with
        | Returned b' => if 4*b-4 <=? b' then Returned b' else Invalid GrowthGuard
        | r => r
        end
      else Invalid GrowthGuard
    end
  else Invalid InputGuard.

Definition step (b : N) : result :=
  if minimum <=? b then return_map b else Invalid InputGuard.

Definition run_next b : outcome N result :=
  match step b with Returned b' => Continue b' | r => Stop r end.

Definition run (fuel b : N) : result :=
  match iter run_next fuel b with
  | Continue b' => Exhausted b'
  | Stop r => r
  end.

Definition bootstrap_next b : outcome N result :=
  if minimum <=? b then Stop (Returned b)
  else match return_map b with Returned b' => Continue b' | r => Stop r end.

Fixpoint bootstrap_loop fuel t : option (N*N) :=
 match fuel with
 | O=>None
 | S fuel=>t <- Derivation.advance t ;;
   match k_shape t with
   | Some (a,b)=>a <- ae_N a ;; b <- ae_N b ;;
      if N.leb 40 b then Some (a,b) else bootstrap_loop fuel t
   | None=>bootstrap_loop fuel t
   end
 end.

Definition bootstrap_gap := bootstrap_loop 30000 initial_gap.

Definition blank_seed : result :=
  match bootstrap_gap with
  | None => Invalid BootstrapDerivation
  | Some (a,b) =>
    match to_two a b with
    | None => Invalid CanonicalGuard
    | Some B =>
      match iter bootstrap_next minimum B with
      | Stop r => r
      | Continue _ => Invalid BootstrapFuel
      end
    end
  end.

Definition run_from_blank (fuel : N) : result :=
  match blank_seed with Returned b => run fuel b | r => r end.
