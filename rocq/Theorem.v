From MinimalSim Require Import Machine Simulator Reflection.
From Coq Require Import NArith List Lia.
Import ListNotations.

Open Scope N_scope.

Lemma return_map_returned_sound b B : 42<=b -> return_map b=Returned B ->
 K2 b -->+ K2 B.
Proof.
 intro Hb. unfold return_map.
 destruct (2<=?b); [|discriminate].
 destruct (entry b) as [s|e] eqn:HE; [|discriminate].
 destruct (8*(b/2)<=?nf_tail s); [|discriminate].
 destruct (finish s) as [B'|c t|e|x] eqn:HF; try discriminate.
 destruct (4*b-4<=?B'); [|discriminate]. intro HR; inversion HR; subst B'.
 eapply progress_evstep_trans; [eapply entry_sound; eauto|].
 apply finish_returned_sound; [eapply entry_output_shape; exact HE|exact HF].
Qed.

Lemma return_map_halted_sound b c t : 42<=b -> return_map b=Halted c t ->
 halts tm (K2 b).
Proof.
 intro Hb. unfold return_map.
 destruct (2<=?b); [|discriminate].
 destruct (entry b) as [s|e] eqn:HE; [|discriminate].
 destruct (8*(b/2)<=?nf_tail s); [|discriminate].
 destruct (finish s) as [B|c' t'|e|x] eqn:HF; try discriminate.
 - destruct (4*b-4<=?B); discriminate.
 - intro HR; inversion HR; subst c' t'.
   eapply halts_evstep.
   + eapply finish_halted_sound; [eapply entry_output_shape; exact HE|exact HF].
   + apply progress_evstep. eapply entry_sound; eauto.
Qed.

Theorem return_contract_proved : return_contract.
Proof.
 intros b Hb. pose proof (step_total_growth b Hb) as HT.
 assert (Hmin : (minimum<=?b)=true) by now apply N.leb_le.
 assert (H42 : 42<=b) by (unfold minimum in Hb; lia).
 destruct HT as [[B [HS [HG HB]]]|[c [t HS]]]; rewrite HS.
 - split; [|exact HB]. unfold Simulator.step in HS. rewrite Hmin in HS.
   eapply return_map_returned_sound; eauto.
 - unfold Simulator.step in HS. rewrite Hmin in HS.
   eapply return_map_halted_sound; eauto.
Qed.

Theorem simulator_halts_iff b : minimum<=b ->
 ((exists fuel c t, Simulator.run fuel b=Halted c t) <-> halts tm (K2 b)).
Proof. apply equivalence_from_contract. exact return_contract_proved. Qed.

Theorem blank_simulator_halts_iff :
 ((exists fuel c t, run_from_blank fuel=Halted c t) <-> halts tm c0).
Proof.
 apply (blank_equivalence_from_prefix 7090140).
 - exact derived_blank_seed.
 - unfold minimum. lia.
 - exact blank_prefix.
 - exact return_contract_proved.
Qed.
