(**
  Really simply proof of Claim 5.5 from "The Joy of Cryptography" (p. 94).

  It is simple and easy to follow.
*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

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

Section StretchPRG_example.

Definition tt := Datatypes.tt.

Variable (n: nat).

Definition Word_N: nat := 2^n.
Definition Word: choice_type := 'fin Word_N.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Context (PRG: Word -> Word * Word).

Definition query: nat := 0.

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

Definition PRG1_pkg_tt:
  package fset0
    [interface]
    [interface #val #[query]: 'unit → 'word × 'word ] :=
  [package
      #def #[query] (_: 'unit): 'word × 'word {
        s <$ uniform Word_N ;;
        ret (PRG s)
      }
  ].

Definition PRG1_pkg_ff:
  package fset0
    [interface]
    [interface #val #[query]: 'unit → 'word × 'word ] :=
  [package
      #def #[query] (_: 'unit): 'word × 'word {
        r1 <$ uniform Word_N ;;
        r2 <$ uniform Word_N ;;
        ret (r1, r2)
      }
  ].

Definition PRG1 := mkpair PRG1_pkg_tt PRG1_pkg_ff.

Definition PRG2_pkg_tt:
  package fset0
    [interface]
    [interface #val #[query]: 'unit → 'word × 'word × 'word ] :=
  [package
      #def #[query] (_: 'unit): 'word × 'word × 'word {
        s <$ uniform Word_N ;;
        let '(x, y) := PRG s in
        ret (x, PRG y)
      }
  ].

Definition PRG2_pkg_ff:
  package fset0
    [interface]
    [interface #val #[query]: 'unit → 'word × 'word × 'word ] :=
  [package
      #def #[query] (_: 'unit): 'word × 'word × 'word {
        x <$ uniform Word_N ;;
        u <$ uniform Word_N ;;
        v <$ uniform Word_N ;;
        ret (x, (u, v))
      }
  ].

Definition PRG2 := mkpair PRG2_pkg_tt PRG2_pkg_ff.

Definition PRG2_HYB_pkg_1:
  package fset0
    [interface #val #[query]: 'unit → 'word × 'word ]
    [interface #val #[query]: 'unit → 'word × 'word × 'word ] :=
  [package
      #def #[query] (_: 'unit): 'word × 'word × 'word {
        #import {sig #[query]: 'unit → 'word × 'word } as query ;;
        xy ← query tt ;;
        let '(x, y) := xy in
        ret (x, PRG y)
      }
  ].

Definition PRG2_HYB_pkg_2:
  package fset0
    [interface #val #[query]: 'unit → 'word × 'word ]
    [interface #val #[query]: 'unit → 'word × 'word × 'word ] :=
  [package
      #def #[query] (_: 'unit): 'word × 'word × 'word {
        #import {sig #[query]: 'unit → 'word × 'word } as query ;;
        x <$ uniform Word_N ;;
        uv ← query tt ;;
        ret (x, uv)
      }
  ].

Lemma PRG_equiv_true:
  PRG2 true ≈₀ PRG2_HYB_pkg_1 ∘ PRG1 true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq.
  2: by move=> [? ?] [? ?] [].
  simplify_linking.
  ssprove_code_simpl.
  by apply: rreflexivity_rule.
Qed.

Lemma PRG_HYB_equiv:
  PRG2_HYB_pkg_1 ∘ PRG1 false ≈₀ PRG2_HYB_pkg_2 ∘ PRG1 true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq.
  2: by move=> [? ?] [? ?] [].
  simplify_linking.
  by apply: rreflexivity_rule.
Qed.

Lemma PRG_equiv_false:
  PRG2_HYB_pkg_2 ∘ PRG1 false ≈₀ PRG2 false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq.
  2: by move=> [? ?] [? ?] [].
  simplify_linking.
  by apply: rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the PRG, i.e. the chance by
  which an adversary can distinguish the PRG from truly random numbers.
  Negligible by assumption.
*)
Definition prg_epsilon := Advantage PRG1.

Theorem security_based_on_prf LA A:
  ValidPackage LA
    [interface #val #[query]: 'unit → 'word × 'word × 'word ]
      A_export A ->
  Advantage PRG2 A <=
  prg_epsilon (A ∘ PRG2_HYB_pkg_1) +
  prg_epsilon (A ∘ PRG2_HYB_pkg_2).
Proof.
  move=> vA.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (PRG2 true) [::
    PRG2_HYB_pkg_1 ∘ PRG1 true ;
    PRG2_HYB_pkg_1 ∘ PRG1 false ;
    PRG2_HYB_pkg_2 ∘ PRG1 true ;
    PRG2_HYB_pkg_2 ∘ PRG1 false
  ] (PRG2 false) A
  as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite PRG_equiv_true ?fdisjointUr ?fdisjoints0 // GRing.add0r.
  rewrite PRG_HYB_equiv ?fdisjointUr ?fdisjoints0 // GRing.addr0.
  rewrite PRG_equiv_false ?fdisjointUr ?fdisjoints0 // GRing.addr0.
  by rewrite /prg_epsilon !Advantage_E -!Advantage_link !(Advantage_sym (PRG1 true)).
Qed.

End StretchPRG_example.
