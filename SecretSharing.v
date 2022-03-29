(*
  This formalises Theorem 3.6 from "The Joy of Cryptography" (p. 51).
  It is a simple 2-out-of-2 secret-sharing scheme with perfect security,
  based on XOR.

  It is fairly simple to understand. The hardest part is probably the definition
  of [plus] (XOR), which is not really necessary to understand the proof.

  The final statement ([unconditional_secrecy]) is equivalent to that of the
  books: The scheme achieves perfect secerery with up to two shares
  (non-inclusive).
*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From extructures Require Import ord fset fmap.

Import SPropNotations.

Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Section SecretSharing_example.

Variable (n: nat).

Definition Words_N: nat := 2^n.
Definition Words: choice_type := chFin (mkpos Words_N).

(*
  The first bit is a formalisation of [plus] (XOR).
  It is similar to the definitions in OTP.v and PRF.v, but it has been split
  into lemmas to hopefully be easier to read.
  It is still somewhat unwieldy though.
*)

(* Lemmas for the [plus] obligation. *)
Lemma pow2_inj m:
  (2 ^ m)%nat = BinNat.N.to_nat (BinNat.N.pow (BinNums.Npos (BinNums.xO 1%AC)) (BinNat.N.of_nat m)).
Proof.
  elim m => [ // | m' IHm ].
  rewrite expnSr.
  rewrite Nnat.Nat2N.inj_succ.
  rewrite BinNat.N.pow_succ_r'.
  rewrite Nnat.N2Nat.inj_mul.
  rewrite PeanoNat.Nat.mul_comm.
  by apply f_equal2.
Qed.

Lemma log2_lt_pow2 w m:
  (w.+1 < 2^m)%nat ->
  BinNat.N.lt (BinNat.N.log2 (BinNat.N.of_nat w.+1)) (BinNat.N.of_nat m).
Proof.
  move => H.
  rewrite -BinNat.N.log2_lt_pow2.
  2:{
    rewrite Nnat.Nat2N.inj_succ.
    by apply BinNat.N.lt_0_succ.
  }
  unfold BinNat.N.lt.
  rewrite Nnat.N2Nat.inj_compare.
  rewrite PeanoNat.Nat.compare_lt_iff.
  rewrite -pow2_inj.
  rewrite Nnat.Nat2N.id.
  by apply /ltP.
Qed.

#[program] Definition plus: Words -> Words -> Words :=
fun w k =>
  @Ordinal _ (BinNat.N.to_nat (BinNat.N.lxor
      (BinNat.N.of_nat (nat_of_ord w))
      (BinNat.N.of_nat (nat_of_ord k)))) _.
Next Obligation.
  destruct w as [w Hw], k as [k Hk].
  destruct w as [|w'], k as [|k'].
  1,2,3: by simpl; rewrite ?Pnat.SuccNat2Pos.id_succ.
  move: (log2_lt_pow2 _ _ Hw) => H1.
  move: (log2_lt_pow2 _ _ Hk) => H2.
  move: (BinNat.N.max_lub_lt _ _ _ H1 H2) => Hm.
  case: (BinNat.N.eq_dec (BinNat.N.lxor (BinNat.N.of_nat w'.+1) (BinNat.N.of_nat k'.+1)) BinNat.N0) => H0.
  1: by rewrite H0 expn_gt0.
  move: (BinNat.N.log2_lxor (BinNat.N.of_nat w'.+1) (BinNat.N.of_nat k'.+1)) => Hbound.
  move: (BinNat.N.le_lt_trans _ _ _ Hbound Hm).
  rewrite -BinNat.N.log2_lt_pow2.
  2: by apply BinNat.N.neq_0_lt_0.
  unfold BinNat.N.lt.
  rewrite Nnat.N2Nat.inj_compare.
  rewrite PeanoNat.Nat.compare_lt_iff.
  rewrite -pow2_inj.
  move /ltP.
  apply.
Qed.

Notation "m ⊕ k" := (plus m k) (at level 70).

(* Some lemmas for [plus] itself. *)
Lemma plus_comm m k:
  (m ⊕ k) = (k ⊕ m).
Proof.
  apply ord_inj.
  case: m => m ? /=.
  by rewrite BinNat.N.lxor_comm.
Qed.

Lemma plus_assoc m l k:
  ((m ⊕ l) ⊕ k) = (m ⊕ (l ⊕ k)).
Proof.
  apply ord_inj.
  case: m => m ? /=.
  rewrite !Nnat.N2Nat.id.
  by rewrite BinNat.N.lxor_assoc.
Qed.

Lemma plus_involutive m k:
  (m ⊕ k) ⊕ k = m.
Proof.
  rewrite plus_assoc.
  apply ord_inj.
  case: m => m ? /=.
  rewrite Nnat.N2Nat.id.
  rewrite BinNat.N.lxor_nilpotent.
  rewrite BinNat.N.lxor_0_r.
  by rewrite Nnat.Nat2N.id.
Qed.

#[local] Open Scope package_scope.

Notation " 'word " := ('fin (2^n)%N) (in custom pack_type at level 2).
Notation " 'word " := ('fin (2^n)%N) (at level 2): package_scope.

(*
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition share (m: Words):
  code fset0
    [interface]
    (chMap 'nat 'word) :=
  {code
    s0 <$ uniform Words_N ;;
    let s1 := s0 ⊕ m in
    ret [fmap (0, s0) ; (1, s0 ⊕ m)]
  }.

Definition reconstruct (s0 s1: Words) :
  code fset0
    [interface]
    'fin (2^n) :=
  {code
    ret (s0 ⊕ s1)
  }.

Definition share_lr: nat := 0.

(* Some convenience functions to compute a submap. *)
Fixpoint subm_seq {K: ordType} {V} (m: {fmap K -> V}) (u: seq K): seq (K * V) :=
  match u with
  | k :: u' =>
    match m k with
    | Some v => (k, v) :: subm_seq m u'
    | None => subm_seq m u'
    end
  | [::] => [::]
  end.

Definition subm {K: ordType} {V} (m: {fmap K -> V}) (u: seq K): {fmap K -> V} :=
  mkfmap (subm_seq m u).

Definition TSSS_pkg_tt :
  package fset0 [interface]
    [interface #val #[share_lr]: 'word × 'word × 'set 'nat → {map 'nat → 'word} ] :=
  [package
    #def #[share_lr] ('(ml, (mr, u)): 'word × 'word × 'set 'nat): {map 'nat → 'word} {
      if size (domm u) >= 2 then ret emptym
      else
      s ← share mr ;;
      ret (subm s (domm u))
    }
  ].

Definition TSSS_HYB_pkg_tt :
  package fset0 [interface]
    [interface #val #[share_lr]: 'word × 'word × 'set 'nat → {map 'nat → 'word} ] :=
  [package
    #def #[share_lr] ('(ml, (mr, u)): 'word × 'word × 'set 'nat): {map 'nat → 'word} {
      match FSet.fsval (domm u) with
      | [:: 0] =>
        s0 <$ uniform Words_N ;;
        ret [fmap (0, s0)]
      | [:: 1] =>
        s0 <$ uniform Words_N ;;
        s1 ← ret (s0 ⊕ mr) ;;
        ret [fmap (1, s1)]
      | _ => ret emptym
      end
    }
  ].

Definition TSSS_HYB_pkg_ff :
  package fset0 [interface]
    [interface #val #[share_lr]: 'word × 'word × 'set 'nat → {map 'nat → 'word} ] :=
  [package
    #def #[share_lr] ('(ml, (mr, u)): 'word × 'word × 'set 'nat): {map 'nat → 'word} {
      match FSet.fsval (domm u) with
      | [:: 0] =>
        s0 <$ uniform Words_N ;;
        ret [fmap (0, s0)]
      | [:: 1] =>
        s0 <$ uniform Words_N ;;
        s1 ← ret (s0 ⊕ ml) ;;
        ret [fmap (1, s1)]
      | _ => ret emptym
      end
    }
  ].

Definition TSSS_pkg_ff :
  package fset0 [interface]
    [interface #val #[share_lr]: 'word × 'word × 'set 'nat → {map 'nat → 'word} ] :=
  [package
    #def #[share_lr] ('(ml, (mr, u)): 'word × 'word × 'set 'nat): {map 'nat → 'word} {
      if size (domm u) >= 2 then ret emptym
      else
      s ← share ml ;;
      ret (subm s (domm u))
    }
  ].

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

Definition TSSS := mkpair TSSS_pkg_tt TSSS_pkg_ff.
Definition TSSS_HYB := mkpair TSSS_HYB_pkg_tt TSSS_HYB_pkg_ff.

Lemma TSSS_HYB_equiv_tt:
  TSSS true ≈₀ TSSS_HYB true.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq.
  2: intros [] [] Heq; by case: Heq.
  case m => ml [mr u].
  set u' := _ (domm u).
  case: u' => [|a u'].
  1: {
    cbn.
    apply: r_const_sample_L => ?.
    by apply: rreflexivity_rule.
  }
  case: u' => [|? ?].
  2: {
    simpl.
    case: a => [|[|?]].
    all: by apply: rreflexivity_rule.
  }
  case: a => [|[|?]].
  1,2: by apply: rreflexivity_rule.
  apply: r_const_sample_L => ?.
  by apply: rreflexivity_rule.
Qed.

Lemma TSSS_HYB_equiv:
  TSSS_HYB true ≈₀ TSSS_HYB false.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq.
  2: intros [] [] Heq; by case: Heq.
  case m => ml [mr u].
  set u' := _ (domm u).
  case: u' => [|a u'].
  1: by apply: rreflexivity_rule.
  case: u' => [|? u'].
  2: by apply: rreflexivity_rule.
  case: a => [|[|?]].
  1,3: by apply: rreflexivity_rule.
  pose (f := fun (m: Words) => m ⊕ (ml ⊕ mr)).
  assert (bij_f: bijective f).
  {
    subst f.
    by exists (fun x => (x ⊕ (ml ⊕ mr))) => x;
      apply plus_involutive.
  }
  apply r_uniform_bij with (1:=bij_f) => x.
  unfold f.
  rewrite plus_assoc.
  rewrite (plus_comm ml).
  rewrite plus_involutive.
  by apply: rreflexivity_rule.
Qed.

Lemma TSSS_HYB_equiv_ff:
  TSSS_HYB false ≈₀ TSSS false.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq.
  2: intros [] [] Heq; by case: Heq.
  case m => ml [mr u].
  set u' := _ (domm u).
  case: u' => [|a u'].
  1: {
    cbn.
    apply: r_const_sample_R => ?.
    by apply: rreflexivity_rule.
  }
  case: u' => [|? ?].
  2: {
    simpl.
    case: a => [|[|?]].
    all: by apply: rreflexivity_rule.
  }
  case: a => [|[|?]].
  1,2: by apply: rreflexivity_rule.
  apply: r_const_sample_R => ?.
  by apply: rreflexivity_rule.
Qed.

Theorem unconditional_secrecy LA A:
  ValidPackage LA
    [interface #val #[share_lr] : 'word × 'word × 'set 'nat → {map 'nat → 'word} ] A_export A ->
  Advantage TSSS A = 0%R.
Proof.
  intros vA.
  rewrite Advantage_E.
  rewrite Advantage_sym.
  ssprove triangle (TSSS true) [::
    pack (TSSS_HYB true)  ;
    pack (TSSS_HYB false)
  ] (TSSS false) A as ineq.
  rewrite TSSS_HYB_equiv_tt ?GRing.add0r ?fdisjoints0 // in ineq.
  rewrite TSSS_HYB_equiv    ?GRing.addr0 ?fdisjoints0 // in ineq.
  rewrite TSSS_HYB_equiv_ff ?GRing.addr0 ?fdisjoints0 // in ineq.
  by apply AdvantageE_le_0.
Qed.

End SecretSharing_example.
