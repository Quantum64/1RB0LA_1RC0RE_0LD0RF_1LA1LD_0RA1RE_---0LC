From Coq Require Import ZArith NArith List Bool.
Import ListNotations.

Open Scope Z_scope.

Inductive mode := M202 | M0002 | M122 | MH.

Record affine := Aff { slope : Z; intercept : Z }.

Definition ac (z : Z) := Aff 0 z.

Definition aa x y := Aff (slope x + slope y) (intercept x + intercept y).

Definition an x := Aff (-slope x) (-intercept x).

Definition asub x y := aa x (an y).

Definition amul x z := Aff (slope x*z) (intercept x*z).

Definition ae x y := (slope x =? slope y) && (intercept x =? intercept y).

Definition az x := ae x (ac 0).

Definition aone x := ae x (ac 1).

Definition eval_affine x n := slope x * Z.of_N n + intercept x.

Definition age x y : option bool :=
  let d := asub x y in
  if slope d =? 0 then Some (0 <=? intercept d)
  else if (0 <=? slope d) && (0 <=? 100*slope d+intercept d)
       then Some true
       else if (slope d <=? 0) && (100*slope d+intercept d <? 0)
            then Some false else None.

Definition agt x y := age x (aa y (ac 1)).

Definition bind {A B} (x:option A) (f:A->option B) :=
  match x with Some a => f a | None => None end.

Notation "x <- a ;; b" := (bind a (fun x => b))
  (at level 100, a at next level, right associativity).

Definition adiv x d : option affine :=
  ok <- age x (ac 0) ;;
  if ok && (0 <? d) && (slope x mod d =? 0)
  then Some (Aff (slope x / d) (intercept x / d)) else None.

Definition aconcrete x : option Z :=
  if slope x =? 0 then Some (intercept x) else None.

Definition anat x : option nat :=
  z <- aconcrete x ;; if 0 <=? z then Some (Z.to_nat z) else None.

Definition ae_N x : option N :=
  z <- aconcrete x ;; if 0 <=? z then Some (Z.to_N z) else None.

Definition digit := nat.

Definition word := list digit.

Definition weq := list_eq_dec Nat.eq_dec.

Definition wb (x y:word) := if weq x y then true else false.

Record block := Bl { letters : option word; count : affine }.

Definition bl w n := Bl (Some w) n.

Definition one w := bl w (ac 1).

Record stack := St { finite : word; powers : list block }.

Definition empty_stack := St [] [].

Definition allzero w := forallb (fun d => Nat.eqb d 0) w.

Definition block_zero b := match letters b with Some w=>allzero w | None=>false end.

Definition sempty s := allzero (finite s) && forallb block_zero (powers s).

Definition literal_eq x y := match letters x,letters y with
  | Some a,Some b => wb a b | _,_=>false end.

Fixpoint repeat_word (w:word) (n:nat) : word :=
  match n with O=>[] | S n=>w++repeat_word w n end.

Fixpoint primitive_word (fuel size:nat) (w:word) : word * nat :=
  match fuel with
  | O=>(w,1%nat)
  | S fuel=> if Nat.eqb ((length w mod size)%nat) 0 &&
              wb w (repeat_word (firstn size w) ((length w / size)%nat))
             then (firstn size w,(length w / size)%nat)
             else primitive_word fuel (S size) w
  end.

Definition compress_block b := match letters b with
  | None=>b
  | Some []=>b
  | Some w=>let '(w',n):=primitive_word (length w) 1 w in
            bl w' (amul (count b) (Z.of_nat n)) end.

Definition useless b := az (count b) || match letters b with Some []=>true|_=>false end.

Fixpoint normalize_blocks (xs acc:list block) : list block :=
  match xs with
  | []=>rev acc
  | b::xs=>if useless b then normalize_blocks xs acc else
      let b:=compress_block b in
      match acc with
      | a::acc'=>if literal_eq a b
                 then normalize_blocks xs (Bl (letters b) (aa (count a) (count b))::acc')
                 else normalize_blocks xs (b::acc)
      | []=>normalize_blocks xs [b]
      end
  end.

Fixpoint trim_blocks xs := match xs with
  | []=>[] | x::xs=>if block_zero x then trim_blocks xs else x::xs end.

Fixpoint trim_digits xs := match xs with
  | []=>[] | x::xs=>if Nat.eqb x 0 then trim_digits xs else x::xs end.

Definition snormalize s :=
  let p:=rev (trim_blocks (rev (normalize_blocks (powers s) []))) in
  St (match p with []=>rev (trim_digits (rev (finite s))) | _=>finite s end) p.

Definition sprepend parts s :=
  snormalize (St [] (parts ++ (match finite s with []=>powers s | f=>one f::powers s end))).

Definition sappend parts s := St (finite s) (powers s++parts).

Definition spop s : option (digit*stack) :=
  match finite s with
  | x::xs=>Some (x,St xs (powers s))
  | []=>match powers s with
      | []=>Some (0%nat,s)
      | b::bs=> match letters b with
        | None | Some []=>None
        | Some (x::xs)=>ok <- agt (count b) (ac 0) ;;
          if ok then Some (x,St xs (if aone (count b) then bs else
                                  Bl (letters b) (asub (count b) (ac 1))::bs)) else None
        end
      end
  end.

Fixpoint spops n s : option (word*stack) :=
 match n with O=>Some ([],s) | S n=>
  p <- spop s ;; let '(x,s):=p in
  p <- spops n s ;; let '(xs,s):=p in Some (x::xs,s) end.

Fixpoint smatches w s : option bool :=
 match w with
 | []=>Some true
 | x::xs=> match finite s,powers s with
   | [],Bl None _::_=>Some false
   | _,_=>p <- spop s ;; let '(y,s):=p in
           if Nat.eqb x y then smatches xs s else Some false end
 end.

Definition seven : word := [0;2;1;0;1;2;1]%nat.

Definition saligned (accept:word->bool) s : option (option (word*affine*stack)) :=
 match powers s with
 | []=>Some None
 | Bl None _::_=>Some None
 | Bl (Some w) n::ps=>
   match finite s with
   | []=>if Nat.even (length w) then
          if accept w then Some (Some (w,n,St [] ps)) else Some None
         else ok <- age n (ac 2) ;;
          if ok && accept (w++w) then
           q <- adiv n 2 ;; let r:=asub n (amul q 2) in
           Some (Some (w++w,q,St [] (if az r then ps else bl w r::ps)))
          else Some None
   | [x]=>if Nat.even (length w) && Nat.eqb x (last w 0%nat) then
      let rotated:=x::firstn (length w-1)%nat w in
      if accept rotated then Some (Some (rotated,n,St [x] ps)) else Some None
      else Some None
   | _=>Some None
   end
 end.

Fixpoint pair_accept pair w := match w with
 | []=>true | x::y::xs=>wb [x;y] pair && pair_accept pair xs | _=>false end.

Fixpoint spairs_loop fuel pair s total : option (affine*stack) :=
 match fuel with
 | O=>None
 | S fuel=>ok <- smatches pair s ;;
   if negb ok then Some (total,s) else
   found <- saligned (pair_accept pair) s ;;
   match found with
   | Some (w,n,s)=>spairs_loop fuel pair s (aa total (amul n (Z.of_nat ((length w/2)%nat))))
   | None=>p <- spops 2 s ;; spairs_loop fuel pair (snd p) (aa total (ac 1))
   end
 end.

Definition spairs pair s := spairs_loop 4096 pair s (ac 0).

Fixpoint check_pairs phase w : option bool := match w with
 | []=>Some phase
 | d::w=>if phase && negb (Nat.eqb d 1) then None else check_pairs (negb phase) w end.

Fixpoint paired_blocks phase bs : option bool :=
 match bs with
 | []=>Some (negb phase)
 | Bl None n::bs=>if phase || negb (aone n) then Some false else paired_blocks phase bs
 | Bl (Some w) n::bs=>
   if Nat.odd (length w) && negb (aone n) then
     if forallb (Nat.eqb 1) w then
       let size:=amul n (Z.of_nat (length w)) in
       q <- adiv size 2 ;; let r:=asub size (amul q 2) in
       if az r then paired_blocks phase bs else
       if aone r then paired_blocks (negb phase) bs else None
     else Some false
   else match check_pairs phase w with
        | None=>Some false | Some p=>paired_blocks p bs end
 end.

Definition spaired s := paired_blocks false (one (finite s)::powers s).

Definition run := (option digit * affine)%type.

Definition runs := list run.

Definition digit_eq x y := match x,y with
 | None,None=>true | Some x,Some y=>Nat.eqb x y | _,_=>false end.

Definition push_run d n out := if az n then out else
 match out with
 | (e,m)::xs=>if digit_eq d e then (d,aa n m)::xs else (d,n)::out
 | []=>[(d,n)] end.

Fixpoint eat_word w pending out : option (option digit*runs) :=
 match w with
 | []=>Some (pending,out)
 | d::w=>match pending with
    | None=>eat_word w (Some d) out
    | Some e=>if Nat.eqb d 1 then eat_word w None (push_run (Some e) (ac 1) out) else None
    end
 end.

Fixpoint runs_blocks bs pending out : option runs :=
 match bs with
 | []=>match pending with None=>Some (rev out)|_=>None end
 | Bl None n::bs=>match pending with
     | None=>if aone n then runs_blocks bs None (push_run None (ac 1) out) else None
     | _=>None end
 | Bl (Some w) n::bs=>
   if aone n then
     p <- eat_word w pending out ;; runs_blocks bs (fst p) (snd p)
   else match pending,w with
   | None,[d;1%nat]=>runs_blocks bs None (push_run (Some d) n out)
   | _,[1%nat]=>
     p <- (match pending with None=>Some (None,out,n) | Some _=>
              p <- eat_word [1%nat] pending out ;; Some (fst p,snd p,asub n (ac 1)) end) ;;
     let '(pending,out,n):=p in
     q <- adiv n 2 ;; let r:=asub n (amul q 2) in
     if az r then runs_blocks bs None (push_run (Some 1%nat) q out)
     else if aone r then runs_blocks bs (Some 1%nat) (push_run (Some 1%nat) q out)
     else None
   | _,_=>k <- anat n ;;
      if Nat.leb ((length w*k)%nat) 4096 then
       p <- eat_word (repeat_word w k) pending out ;; runs_blocks bs (fst p) (snd p)
      else None
   end
 end.

Definition sruns s : option runs :=
 p <- spop s ;; let '(d,s):=p in
 if Nat.eqb d 0 then
  p <- eat_word (finite s) None [] ;; runs_blocks (powers s) (fst p) (snd p)
 else None.

Definition boundary rs := sprepend
 (one [0%nat]::map (fun '(d,n)=>match d with
   | None=>Bl None n | Some d=>bl [d;1%nat] n end) rs) empty_stack.

Fixpoint motif w y : option (digit*word) :=
 match w with
 | []=>Some (y,[])
 | b::a::w=>if Nat.eqb y 1 then None else
    let part:=if Nat.eqb a 1 then [] else repeat 0%nat (a-2)%nat++[(b+3)%nat] in
    let part:=part++if Nat.leb 2 y then [0;(y-2)]%nat else [] in
    p <- motif w (if Nat.eqb a 1 then (b+3)%nat else 0%nat) ;;
    Some (fst p,snd p++part)
 | _=>None
 end.

Record gap_tape := GT { left : stack; right : stack; countdowns : bool }.

Definition initial_gap := GT empty_stack empty_stack true.

Definition tape_of_runs rs cd := GT (boundary rs) empty_stack cd.

Definition tnormalize t := GT (snormalize (left t)) (snormalize (right t)) (countdowns t).

Definition k_shape t : option (affine*affine) :=
 if sempty (right t) then
 ok <- smatches seven (left t) ;;
 if ok then
 p <- spops 7 (left t) ;;
 p <- spairs [0;1]%nat (snd p) ;; let '(a,s):=p in
 p <- spops 2 s ;;
 if wb (fst p) [3;1]%nat then
 p <- spairs [2;1]%nat (snd p) ;;
 if sempty (snd p) then Some (a,fst p) else None
 else None else None else None.

Definition run_is d n r := digit_eq (Some d) (fst r) && ae (snd r) (ac n).

Definition zero_loop_at ix period growth rs t : option (option gap_tape) :=
 match nth_error rs ix with
 | None=>Some None
 | Some (d,z)=>if digit_eq d (Some 0%nat) then
    ok <- age z (ac period) ;;
    if ok then q <- adiv z period ;;
      Some (Some (GT (boundary (firstn ix rs++
       (Some 0%nat,asub z (amul q period))::skipn (S ix) rs++[(Some 2%nat,amul q growth)]))
       (right t) (countdowns t)))
    else Some None
   else Some None
 end.

Definition zero_loop t : option (option gap_tape) :=
 if countdowns t && sempty (right t) then
 match sruns (left t) with
 | Some (a::b::c::rs)=>
   if (run_is 0%nat 3 a && run_is 2%nat 1 b) ||
      (run_is 1%nat 1 a && run_is 2%nat 2 b)
   then zero_loop_at 2 3 12 (a::b::c::rs) t
   else if negb (Nat.eqb (length rs) 0) && run_is 1%nat 1 a &&
           digit_eq (fst b) (Some 3%nat) && run_is 2%nat 1 c
        then zero_loop_at 3 2 10 (a::b::c::rs) t else Some None
 | _=>Some None end else Some None.

Definition countdown_three t : option (option gap_tape) :=
 ok <- smatches [0;3;1]%nat (left t) ;;
 if ok then
 p <- spop (left t) ;;
 p <- spairs [3;1]%nat (snd p) ;; let '(c,s):=p in
 p <- spairs [0;1]%nat s ;; let '(z,s):=p in
 paired <- spaired s ;;
 if paired then
 c_ok <- age c (ac 1) ;; z_ok <- age z (ac 2) ;;
 if c_ok && z_ok then
  q <- adiv z 2 ;;
  let s:=sprepend [one [0%nat];bl [3;1]%nat (aa c q);bl [0;1]%nat (asub z (amul q 2))] s in
  Some (Some (GT (sappend [bl [2;1]%nat (amul q 2)] s) (right t) (countdowns t)))
 else Some None else Some None else Some None.

Definition countdown_k t : option (option gap_tape) :=
 ok <- smatches seven (left t) ;;
 if ok then
 p <- spops 7 (left t) ;;
 p <- spairs [0;1]%nat (snd p) ;; let '(z,s):=p in
 paired <- spaired s ;;
 if paired then
 ok <- age z (ac 4) ;;
 if ok then q <- adiv z 4 ;;
  let s:=sprepend [one seven;bl [0;1]%nat (asub z (amul q 4))] s in
  Some (Some (GT (sappend [bl [2;1]%nat (amul q 14)] s) (right t) (countdowns t)))
 else Some None else Some None else Some None.

Definition countdown t : option (option gap_tape) :=
 if countdowns t && sempty (right t) then
 p <- countdown_three t ;; match p with Some _=>Some p |None=>countdown_k t end
 else Some None.

Definition transfer_prefix : word := [0;0;0;0;3;0;1]%nat.

Definition transfer t : option (option gap_tape) :=
 a <- smatches [2%nat] (left t) ;;
 b <- smatches transfer_prefix (right t) ;;
 if a && b then
 p <- spop (left t) ;;
 p <- spairs [0;1]%nat (snd p) ;; let '(budget,s):=p in
 ok <- agt budget (ac 0) ;;
 if ok then
 p <- spops 7 (right t) ;;
 Some (Some (GT (sprepend [one [2%nat]] s)
    (sprepend [one transfer_prefix;bl [0;1]%nat budget] (snd p)) (countdowns t)))
 else Some None else Some None.

Fixpoint take_fours fuel s budget : option (affine*stack) :=
 match fuel with
 | O=>None
 | S fuel=>match finite s,powers s with
   | 4%nat::xs,ps=>take_fours fuel (St xs ps) (aa budget (ac 1))
   | [],Bl (Some w) n::ps=>if forallb (Nat.eqb 4) w
        then take_fours fuel (St [] ps) (aa budget (amul n (Z.of_nat (length w))))
        else Some (budget,s)
   | _,_=>Some (budget,s)
   end
 end.

Definition paired_countdown t : option (option gap_tape) :=
 p <- spops 2 (right t) ;;
 if wb (fst p) [0;3]%nat then
 p <- take_fours 4096 (snd p) (ac 0) ;; let '(budget,s):=p in
 ok <- agt budget (ac 0) ;;
 if ok then
  Some (Some (GT (sappend [bl [2;1]%nat budget]
      (sprepend [bl [0;1]%nat budget] (left t)))
      (sprepend [one [0;3]%nat] s) (countdowns t)))
 else Some None else Some None.

Definition paired_pivot t near : option (option gap_tape) :=
 let l:=left t in let r:=right t in
 if sempty r || (Nat.eqb (nth 0 near 0%nat) 0 && Nat.leb 2 (nth 1 near 0%nat)) then
  r <- (if sempty r then Some r else
       p <- spops 2 r ;; Some (sprepend [one [(nth 1 (fst p) 0 - 2)%nat]] (snd p))) ;;
  let l:=sprepend [] l in
  let l:=sappend [one [2;1]%nat] l in
  Some (Some (GT (sprepend [one [0%nat]] l) r (countdowns t)))
 else if wb (firstn 2 near) [0;0]%nat && Nat.ltb 0 (nth 2 near 0%nat) then
  p <- spops 3 r ;;
  Some (Some (GT (sappend [one [2;1]%nat] (sprepend [] l))
       (sprepend [one [0;(nth 2 (fst p) 0 - 1)]%nat] (snd p)) (countdowns t)))
 else Some None.

Fixpoint right_accept w := match w with
 | []=>true | a::b::w=>Nat.ltb 0 a && Nat.eqb b 0 && right_accept w
 | _=>false end.

Fixpoint left_accept w := match w with
 | []=>true | _::a::w=>Nat.leb 1 a && left_accept w
 | _=>false end.

Fixpoint right_cycle w := match w with
 | a::_::w=>right_cycle w ++ [(a-1);1]%nat
 | _=>[] end.

Definition elementary t x y : option gap_tape :=
 p <- spops 2 (right t) ;; let r:=snd p in
 p <- spop (left t) ;; let '(b,l):=p in
 if Nat.ltb 0 x then
  let w:=if Nat.eqb y 0 then [0;x-1;b+1]%nat else [x-1;b+1]%nat in
  Some (GT (sprepend [one w] l)
       (if Nat.eqb y 0 then r else sprepend [one [0;y-1]%nat] r) (countdowns t))
 else p <- spop l ;; let '(a,l):=p in
  Some (GT l (sprepend [one (repeat 0%nat a++[(b+3)%nat]++
                  if Nat.leb 2 y then [0;y-2]%nat else [])] r) (countdowns t)).

Definition powered_pivot t x y : option gap_tape :=
 if Nat.ltb 0 x then
  found <- saligned right_accept (right t) ;;
  match found with
  | None=>elementary t x y
  | Some (w,n,r)=>p <- spop (left t) ;; let '(b,l):=p in
      let cycle:=right_cycle w in
      Some (GT (sprepend [one [0%nat];bl cycle (asub n (ac 1));
               one (firstn (length cycle-1)%nat cycle++[(b+1)%nat])] l) r (countdowns t))
  end
 else if Nat.eqb y 1 then None else
  found <- saligned left_accept (left t) ;;
  match found with
  | None=>elementary t x y
  | Some (w,n,l)=>
    p <- spops 2 (right t) ;; let r:=snd p in
    p <- motif w y ;; let '(fy,first):=p in
    p <- motif w fy ;; let '(cy,cycle):=p in
    if Nat.eqb fy cy then
      Some (GT l (sprepend [one [0;fy]%nat;bl cycle (asub n (ac 1));one first] r) (countdowns t))
    else None
  end.

Definition advance_raw t : option gap_tape :=
 result <- zero_loop t ;;
 match result with Some t=>Some t |None=>
 result <- countdown t ;;
 match result with Some t=>Some t |None=>
 result <- transfer t ;;
 match result with Some t=>Some t |None=>
 p <- spops 3 (right t) ;; let near:=fst p in
 paired <- spaired (left t) ;;
 result <- (if paired then
    result <- paired_countdown t ;;
    match result with Some _=>Some result |None=>paired_pivot t near end
   else Some None) ;;
 match result with Some t=>Some t |None=>
 powered_pivot t (nth 0 near 0%nat) (nth 1 near 0%nat)
 end end end end.

Definition advance t := t <- advance_raw t ;; Some (tnormalize t).

Definition prefix m c : word := match m with
 | M202=>[2;0;2]%nat | M0002=>[0;0;0;2]%nat | M122=>[1;2;2]%nat
 | MH=>[1%nat]++repeat 3%nat (N.to_nat c)++[2%nat] end.

Definition prefix_runs m c := map (fun d=>(Some d,ac 1)) (prefix m c).

Fixpoint derive_final_loop fuel t : option (affine*affine) :=
 match fuel with
 | O=>None
 | S fuel=>t <- advance t ;; match k_shape t with
    | Some r=>Some r |None=>derive_final_loop fuel t end
 end.

Definition derive_final m c zeros residue :=
 derive_final_loop 30000
  (tape_of_runs (prefix_runs m c++[(Some 0%nat,ac (Z.of_N zeros));
          (Some 3%nat,ac 1);(Some 2%nat,Aff 24 (Z.of_N residue))]) true).

Fixpoint constant_prefix rs acc : word * runs :=
 match rs with
 | (Some d,n)::rs'=>match anat n with
     | Some k=>constant_prefix rs' (acc++repeat d k)
     |None=>(acc,rs) end
 | _=>(acc,rs)
 end.

Definition prefix_shape w : option (mode*N) :=
 if wb w [2;0;2]%nat then Some (M202,0%N) else
 if wb w [0;0;0;2]%nat then Some (M0002,0%N) else
 if wb w [1;2;2]%nat then Some (M122,0%N) else
 match w with
 | 1%nat::xs=>if Nat.leb 2 (length xs) && Nat.eqb (last xs 0%nat) 2 &&
                forallb (Nat.eqb 3) (firstn (length xs-1)%nat xs)
              then Some (MH,N.of_nat (length xs-1)%nat) else None
 | _=>None end.

Definition middle_shape t : option (mode*N*N*N) :=
 if sempty (right t) then
 rs <- sruns (left t) ;; let '(before,rs):=constant_prefix rs [] in
 target <- prefix_shape before ;;
 match rs with
 | (Some 0%nat,n)::(None,one_n)::(Some 2%nat,growth)::[]=>
    loss <- ae_N (asub (Aff 1 0) n) ;; growth <- ae_N growth ;;
    if aone one_n && negb (N.eqb growth 0) then Some (fst target,snd target,loss,growth) else None
 | _=>None end else None.

Fixpoint derive_middle_loop fuel t : option (mode*N*N*N) :=
 match fuel with
 | O=>None
 | S fuel=>t <- advance t ;; match middle_shape t with
    | Some r=>Some r |None=>derive_middle_loop fuel t end
 end.

Definition derive_middle m c zeros :=
 derive_middle_loop 30000
  (tape_of_runs (prefix_runs m c++[(Some 0%nat,ac (Z.of_N zeros));
    (Some 2%nat,ac 1);(Some 3%nat,ac 1);(Some 0%nat,Aff 1 0);(None,ac 1)]) false).

Definition evaluate x n : option N :=
 let z:=eval_affine x n in if 0 <=? z then Some (Z.to_N z) else None.

Definition final_shapes : list (mode*N*N) :=
 flat_map (fun m=>map (fun z=>(m,0%N,N.of_nat z)) (seq 0 3)) [M0002;M122] ++
 map (fun i=>(MH,N.of_nat (2+2*i)%nat,0%N)) (seq 0 7) ++
 map (fun i=>(MH,N.of_nat (2+2*i)%nat,1%N)) (seq 0 8).

Definition final_regions : list (mode*N*N*N) :=
 flat_map (fun '(m,c,z)=>map (fun r=>(m,c,z,N.of_nat r)) (seq 0 24)) final_shapes.

Definition middle_regions : list (mode*N*N) :=
 map (fun z=>(M202,0%N,N.of_nat z)) (seq 0 4) ++
 flat_map (fun m=>map (fun z=>(m,0%N,N.of_nat z)) (seq 0 3)) [M0002;M122] ++
 flat_map (fun c=>map (fun z=>(MH,N.of_nat c,N.of_nat z)) (seq 0 2)) (seq 1 9).

Definition derive_final_region '(m,c,z,r) := derive_final m c z r.

Definition derive_middle_region '(m,c,z) := derive_middle m c z.

Definition generated_final := map derive_final_region final_regions.

Definition generated_middle := map derive_middle_region middle_regions.

Definition final_table : list (option (affine*affine)).
Proof. let rows := eval vm_compute in generated_final in exact rows. Defined.

Definition middle_table : list (option (mode*N*N*N)).
Proof. let rows := eval vm_compute in generated_middle in exact rows. Defined.

Definition mode_eq m n := match m,n with
 | M202,M202|M0002,M0002|M122,M122|MH,MH=>true|_,_=>false end.

Definition final_key_eq '(m,c,z,r) '(m',c',z',r') :=
 mode_eq m m' && N.eqb c c' && N.eqb z z' && N.eqb r r'.

Definition middle_key_eq '(m,c,z) '(m',c',z') :=
 mode_eq m m' && N.eqb c c' && N.eqb z z'.

Fixpoint table_lookup {K V} (eq:K->K->bool) (k:K) (keys:list K) (values:list (option V)) : option V :=
 match keys,values with
 | key::keys,v::values=>if eq k key then v else table_lookup eq k keys values
 | _,_=>None end.

Definition lookup_final m c z r := table_lookup final_key_eq (m,c,z,r) final_regions final_table.

Definition lookup_middle m c z := table_lookup middle_key_eq (m,c,z) middle_regions middle_table.
