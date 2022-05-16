(**
  This formalises Claim 10.4 from "The Joy of Cryptography" (p. 188).
  Most of it is fairly straight forward, the longest part being
  [TAG_GUESS_equiv_2].

  It would also be nice to formalise Claim 10.3 (p. 186), but its argument
  depends on the adversary only having polynomial time, and how to formulate
  that is unclear.

  The final statement ([security_based_on_prf]) is similar to that of PRF.v,
  stating that the advantage is bounded by a [prf_epsilon] and a
  [statistical_gap]. It would be particularly nice to simply state that it is
  negligible in [n].
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

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Section PRFMAC_example.

Variable (n: nat).

Definition Words_N: nat := 2^n.
Definition Words: choice_type := chFin (mkpos Words_N).

Definition Key_N: nat := 2^n.
Definition Key: choice_type := chFin (mkpos Key_N).

Notation " 'word " := (Words) (in custom pack_type at level 2).
Notation " 'word " := (Words) (at level 2): package_scope.

Notation " 'key " := (Key) (in custom pack_type at level 2).
Notation " 'key " := (Key) (at level 2): package_scope.

#[local] Open Scope package_scope.

Definition key_location: Location := ('option 'key ; 0).
Definition table_location: Location := (chMap 'word 'key ; 1).
Definition mac_table_location: Location := ('set ('word × 'key) ; 2).
Definition lookup: nat := 3.
Definition encrypt: nat := 4.
Definition gettag: nat := 5.
Definition checktag: nat := 6.
Definition guess: nat := 7.

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

Context (PRF: Words -> Key -> Key).

Definition EVAL_locs_tt := fset [:: key_location].
Definition EVAL_locs_ff := fset [:: table_location].

Definition kgen {L} (_: key_location \in L): code L [interface] 'key :=
  {code
    k_init ← get key_location ;;
    match k_init with
    | None =>
        k <$ uniform Key_N ;;
        #put key_location := Some k ;;
        ret k
    | Some k =>
        ret k
    end
  }.

Lemma EVAL_locs_tt_key:
  key_location \in EVAL_locs_tt.
Proof.
  auto_in_fset.
Qed.

Definition EVAL_pkg_tt:
  package EVAL_locs_tt
    [interface]
    [interface #val #[lookup]: 'word → 'key ] :=
  [package
    #def #[lookup] (m: 'word): 'key {
      k ← kgen EVAL_locs_tt_key ;;
      ret (PRF m k)
    }
  ].

Definition EVAL_pkg_ff:
  package EVAL_locs_ff
    [interface]
    [interface #val #[lookup]: 'word → 'key ] :=
  [package
    #def #[lookup] (m: 'word): 'key {
      T ← get table_location ;;
      match getm T m with
      | None =>
          t <$ uniform Key_N ;;
          #put table_location := (setm T m t) ;;
          ret t
      | Some t =>
          ret t
      end
    }
  ].

Definition EVAL := mkpair EVAL_pkg_tt EVAL_pkg_ff.

Definition GUESS_locs := fset [:: table_location].

Definition GUESS_pkg_tt:
  package GUESS_locs
    [interface]
    [interface
      #val #[lookup]: 'word → 'key ;
      #val #[guess]: 'word × 'key → 'bool ] :=
  [package
    #def #[lookup] (m: 'word): 'key {
      T ← get table_location ;;
      match getm T m with
      | None =>
          t <$ uniform Key_N ;;
          #put table_location := (setm T m t) ;;
          ret t
      | Some t =>
          ret t
      end
    } ;
    #def #[guess] ('(m, t): 'word × 'key): 'bool {
      T ← get table_location ;;
      r ← match getm T m with
      | None =>
          r <$ uniform Key_N ;;
          #put table_location := (setm T m r) ;;
          ret r
      | Some r =>
          ret r
      end ;;
      ret (r == t)
    }
  ].

Definition GUESS_pkg_ff:
  package GUESS_locs
    [interface]
    [interface
      #val #[lookup]: 'word → 'key ;
      #val #[guess]: 'word × 'key → 'bool ] :=
  [package
    #def #[lookup] (m: 'word): 'key {
      T ← get table_location ;;
      match getm T m with
      | None =>
          t <$ uniform Key_N ;;
          #put table_location := (setm T m t) ;;
          ret t
      | Some t =>
          ret t
      end
    } ;
    #def #[guess] ('(m, t): 'word × 'key): 'bool {
      T ← get table_location ;;
      ret (getm T m == Some t)
    }
  ].

Definition GUESS := mkpair GUESS_pkg_tt GUESS_pkg_ff.

Definition TAG_locs_tt := fset [:: key_location].
Definition TAG_locs_ff := fset [:: key_location; mac_table_location].

Lemma TAG_locs_tt_key:
  key_location \in TAG_locs_tt.
Proof.
  auto_in_fset.
Qed.

Definition TAG_pkg_tt:
  package TAG_locs_tt
    [interface]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      k ← kgen TAG_locs_tt_key ;;
      ret (PRF m k)
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      k ← kgen TAG_locs_tt_key ;;
      ret ((PRF m k) == t)
    }
  ].

Lemma TAG_locs_ff_key:
  key_location \in TAG_locs_ff.
Proof.
  auto_in_fset.
Qed.

Definition TAG_pkg_ff:
  package TAG_locs_ff
    [interface]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      T ← get mac_table_location ;;
      k ← kgen TAG_locs_ff_key ;;
      let t := PRF m k in
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      T ← get mac_table_location ;;
      ret ((m, t) \in domm T)
    }
  ].

Definition TAG := mkpair TAG_pkg_tt TAG_pkg_ff.

Definition EVAL_TAG_locs_ff := fset [:: mac_table_location].

Definition EVAL_TAG_pkg_tt:
  package fset0
    [interface #val #[lookup]: 'word → 'key ]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      #import {sig #[lookup]: 'word → 'key } as lookup ;;
      t ← lookup m ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      #import {sig #[lookup]: 'word → 'key } as lookup ;;
      r ← lookup m ;;
      ret (r == t)
    }
  ].

Definition EVAL_TAG_pkg_ff:
  package EVAL_TAG_locs_ff
    [interface #val #[lookup]: 'word → 'key]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      #import {sig #[lookup]: 'word → 'key } as lookup ;;
      T ← get mac_table_location ;;
      t ← lookup m ;;
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      T ← get mac_table_location ;;
      ret ((m, t) \in domm T)
    }
  ].

Definition TAG_GUESS_locs := fset [:: mac_table_location ].

Definition TAG_GUESS_pkg_0:
  package fset0
    [interface
      #val #[lookup]: 'word → 'key ;
      #val #[guess]: 'word × 'key → 'bool ]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      #import {sig #[lookup]: 'word → 'key } as lookup ;;
      t ← lookup m ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      #import {sig #[guess]: 'word × 'key → 'bool } as guess ;;
      r ← guess (m, t) ;;
      ret r
    }
  ].

Definition TAG_GUESS_pkg_1:
  package TAG_GUESS_locs
    [interface
      #val #[lookup]: 'word → 'key ;
      #val #[guess]: 'word × 'key → 'bool ]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      #import {sig #[lookup]: 'word → 'key } as lookup ;;
      T ← get mac_table_location ;;
      t ← lookup m ;;
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      #import {sig #[guess]: 'word × 'key → 'bool } as guess ;;
      r ← guess (m, t) ;;
      ret r
    }
  ].

Definition TAG_GUESS_pkg_2:
  package TAG_GUESS_locs
    [interface
      #val #[lookup]: 'word → 'key ;
      #val #[guess]: 'word × 'key → 'bool ]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      #import {sig #[lookup]: 'word → 'key } as lookup ;;
      T ← get mac_table_location ;;
      t ← lookup m ;;
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      T ← get mac_table_location ;;
      ret ((m, t) \in domm T)
    }
  ].

Lemma TAG_equiv_true:
  TAG true ≈₀ EVAL_TAG_pkg_tt ∘ EVAL true.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
    2: case: m => [m t].
    all: simplify_linking.
    all: simplify_linking.
    all: ssprove_sync_eq.
    all: case => [k|].
    all: by apply: rreflexivity_rule.
Qed.

Lemma TAG_GUESS_equiv_0:
  EVAL_TAG_pkg_tt ∘ EVAL false ≈₀ TAG_GUESS_pkg_0 ∘ GUESS true.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  all: simplify_linking.
  2: ssprove_code_simpl.
  all: by apply rreflexivity_rule.
Qed.

Lemma TAG_GUESS_equiv_1:
  TAG_GUESS_pkg_0 ∘ GUESS false ≈₀ TAG_GUESS_pkg_1 ∘ GUESS false.
Proof.
  apply eq_rel_perf_ind_ignore with TAG_GUESS_locs.
  1: {
    apply: fsubset_trans.
    - by apply fsubsetUl.
    - by apply fsubsetUr.
  }
  simplify_eq_rel m.
  2: case: m => [m t].
  all: simplify_linking.
  - apply: r_get_remember_rhs => T2.
    ssprove_sync => T1.
    case: (getm T1 m) => [k|].
    all: simpl.
    2: ssprove_sync => t.
    2: ssprove_sync.
    all: apply: r_put_rhs.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: by ssprove_invariant.
  - simplify_linking.
    ssprove_sync => T1.
    case: (getm T1 m) => [k|].
    all: by apply: r_ret.
Qed.

(**
  The first function ([gettag]) is exactly the same in both packages.
  It turns out, however, to be pretty complicated since we need to prove the
  invariant holds.
*)
Lemma TAG_GUESS_equiv_2:
  TAG_GUESS_pkg_1 ∘ GUESS false ≈₀ TAG_GUESS_pkg_2 ∘ GUESS false.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_rhs table_location mac_table_location
      (fun T1 T2 => forall m t,
        ((m, t) \in domm T2) = (getm T1 m == Some t))
  ).
  1: {
    ssprove_invariant.
    1,2: by rewrite /= /GUESS_locs /TAG_GUESS_locs !fset_cons !in_fsetU !in_fset1 eq_refl Bool.orb_true_r.
    move=> m t.
    by rewrite domm0 in_fset0 get_empty_heap emptymE.
  }
  simplify_eq_rel m.
  2: case: m => [m t].
  all: simpl.
  all: simplify_linking.
  - apply: r_get_vs_get_remember => T2.
    apply: r_get_vs_get_remember => T1.
    destruct (getm T1 m) as [t|] eqn:Heqt.
    all: rewrite Heqt /=.
    + apply: r_put_vs_put.
      ssprove_restore_mem;
        last by apply: r_ret.
      ssprove_invariant=> s0 s1 [[[[Hinv _] H1] _] H2] m' t'.
      rewrite get_set_heap_eq get_set_heap_neq // domm_set in_fsetU in_fset1.
      case: (eq_dec (m', t') (m, t)) => Heq.
      * case: Heq => [-> ->].
        by rewrite H2 Heqt /= !eq_refl.
      * move /eqP /negPf in Heq.
        by rewrite Heq -H1 Hinv.
    + ssprove_sync=> k.
      apply: (r_rem_couple_rhs table_location mac_table_location) => Hinv.
      apply: r_put_vs_put.
      apply: r_put_vs_put.
      ssprove_restore_mem;
        last by apply: r_ret.
      ssprove_invariant=> m' k'.
      rewrite domm_set in_fsetU in_fset1 setmE.
      case: (eq_dec (m', k') (m, k)) => Heq.
      1: {
        case: Heq => [-> ->].
        by rewrite !eq_refl /= eq_refl.
      }
      move /eqP /negPf in Heq.
      rewrite Heq /=.
      rewrite xpair_eqE in Heq.
      case: (eq_dec m' m) => Heqm.
      * rewrite Heqm eq_refl /= in Heq*.
        rewrite eq_sym in Heq.
        by rewrite Heq Hinv Heqt.
      * move /eqP /negPf in Heqm.
        by rewrite Heqm Hinv.
  - ssprove_code_simpl.
    ssprove_code_simpl_more.
    apply: r_get_remember_lhs => T1.
    apply: r_get_remember_rhs => T2.
    apply: (r_rem_couple_rhs table_location mac_table_location) => [|Hinv].
    1: by apply: (Remembers_rhs_from_tracked_lhs _).
    case: (eq_dec (getm T1 m == Some t) true) => /eqP Heq.
    + rewrite Heq eq_refl.
      move /eqP in Heq.
      shelve.
    + rewrite eqb_id in Heq.
      move /negPf in Heq.
      rewrite Heq.
      shelve.
    Unshelve.
    all: rewrite -Hinv in Heq.
    all: rewrite Heq.
    all: apply: r_ret.
    all: split=> //.
    all: by case: H => [[]].
Qed.

Lemma TAG_GUESS_equiv:
  TAG_GUESS_pkg_2 ∘ GUESS false ≈₀ EVAL_TAG_pkg_ff ∘ EVAL false.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: by apply: rreflexivity_rule.
Qed.

Lemma TAG_equiv_false:
  EVAL_TAG_pkg_ff ∘ EVAL true ≈₀ TAG false.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  2: case: m => [m t].
  all: simplify_linking.
  all: ssprove_sync_eq=> T.
  1: ssprove_sync_eq.
  1: case => [k|].
  all: by apply: rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the PRF, i.e. the chance by
  which an adversary can distinguish the PRF from a truly random function.
  Negligible by assumption.
*)
Definition prf_epsilon := Advantage EVAL.

(**
  The advantage an adversary can gain in the [GUESS] game.
  This is negligible, but not yet provable in SSProve.
*)
Definition statistical_gap :=
  AdvantageE (TAG_GUESS_pkg_0 ∘ GUESS true) (TAG_GUESS_pkg_0 ∘ GUESS false).

Lemma cat1s' {A} (x y: A) s:
  [:: x] ++ y :: s = x :: y :: s.
Proof.
  by [].
Qed.

Theorem security_based_on_prf LA A:
    ValidPackage LA
      [interface
        #val #[gettag]: 'word → 'key ;
        #val #[checktag]: 'word × 'key → 'bool
      ] A_export A ->
    fdisjoint LA (
      EVAL_locs_tt :|: EVAL_locs_ff :|: GUESS_locs :|:
      TAG_locs_tt :|: TAG_locs_ff :|:
      EVAL_TAG_locs_ff :|: TAG_GUESS_locs
    ) ->
    Advantage TAG A <=
    prf_epsilon (A ∘ EVAL_TAG_pkg_tt) +
    statistical_gap A +
    prf_epsilon (A ∘ EVAL_TAG_pkg_ff).
Proof.
  move=> vA H.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (TAG true) [::
    EVAL_TAG_pkg_tt ∘ EVAL true   ;
    EVAL_TAG_pkg_tt ∘ EVAL false  ;
    TAG_GUESS_pkg_0 ∘ GUESS true  ;
    TAG_GUESS_pkg_0 ∘ GUESS false ;
    TAG_GUESS_pkg_1 ∘ GUESS false ;
    TAG_GUESS_pkg_2 ∘ GUESS false ;
    EVAL_TAG_pkg_ff ∘ EVAL false  ;
    EVAL_TAG_pkg_ff ∘ EVAL true
  ] (TAG false) A
  as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite !fdisjointUr in H.
  move: H => /andP [/andP [/andP [/andP [/andP [/andP [H1 H2] H3] H4] H5] H6] H7].
  move: {ineq H1 H2 H3 H4 H5 H6 H7} (H1, H2, H3, H4, H5, H6, H7, fdisjoints0) => H.
  rewrite TAG_equiv_true ?fdisjointUr ?H // GRing.add0r.
  rewrite TAG_GUESS_equiv_0 ?fdisjointUr ?H // GRing.addr0.
  rewrite TAG_GUESS_equiv_1 ?fdisjointUr ?H // GRing.addr0.
  rewrite TAG_GUESS_equiv_2 ?fdisjointUr ?H // GRing.addr0.
  rewrite TAG_GUESS_equiv ?fdisjointUr ?H // GRing.addr0.
  rewrite TAG_equiv_false ?fdisjointUr ?H // GRing.addr0.
  rewrite Advantage_sym.
  by rewrite /prf_epsilon /statistical_gap !Advantage_E !Advantage_link.
Qed.

End PRFMAC_example.
