(*
  This formalises Claim 10.4 from "The Joy of Cryptography" (p. 188).
  Most of it is fairly straight forward, but [GUESS_TAG_equiv_2] is (currently)
  quite nasty.

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

Section PRFMAC_example.

Context (n: nat).

Definition Words_N: nat := 2^n.
Definition Words: choice_type := chFin (mkpos Words_N).

Definition Key_N: nat := 2^n.
Definition Key: choice_type := chFin (mkpos Key_N).

Notation " 'word " := (Words) (in custom pack_type at level 2).
Notation " 'key " := (Key) (in custom pack_type at level 2).

Notation " 'word " := (Words) (at level 2): package_scope.
Notation " 'key " := (Key) (at level 2): package_scope.

#[local] Open Scope package_scope.

Definition key_location: Location := ('option Key ; 0).
Definition table_location: Location := (chMap 'word 'key ; 1).
Definition mac_table_location: Location := (chMap ('word × 'word) ('unit) ; 2).
Definition lookup: nat := 3.
Definition encrypt: nat := 4.
Definition gettag: nat := 5.
Definition checktag: nat := 6.
Definition guess: nat := 7.

Context (PRF: Words -> Key -> Key).

Definition kgen {L: { fset Location }}: code L [interface] 'key :=
  {code
    k <$ uniform Key_N ;;
    ret k
  }.

Definition EVAL_location_tt := (fset [:: key_location]).
Definition EVAL_location_ff := (fset [:: table_location]).

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

Definition EVAL_pkg_tt:
  package EVAL_location_tt
    [interface]
    [interface #val #[lookup]: 'word → 'key ] :=
  [package
    #def #[lookup] (m: 'word): 'key {
      k_init ← get key_location ;;
      k ← match k_init with
      | None =>
          k ← kgen ;;
          #put key_location := Some k ;;
          ret k
      | Some k =>
          ret k
      end ;;
      ret (PRF m k)
    }
  ].

Definition EVAL_pkg_ff:
  package EVAL_location_ff
    [interface]
    [interface #val #[lookup]: 'word → 'key ] :=
  [package
    #def #[lookup] (m: 'word): 'key {
      T ← get table_location ;;
      match getm T m with
      | None =>
          t ← kgen ;;
          #put table_location := (setm T m t) ;;
          ret t
      | Some t =>
          ret t
      end
    }
  ].

Definition EVAL := mkpair EVAL_pkg_tt EVAL_pkg_ff.

Definition GUESS_location := (fset [:: table_location]).

Definition GUESS_pkg_tt:
  package GUESS_location
    [interface]
    [interface
      #val #[lookup]: 'word → 'key ;
      #val #[guess]: 'word × 'key → 'bool ] :=
  [package
    #def #[lookup] (m: 'word): 'key {
      T ← get table_location ;;
      match getm T m with
      | None =>
          t ← kgen ;;
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
          r ← kgen ;;
          #put table_location := (setm T m r) ;;
          ret r
      | Some r =>
          ret r
      end ;;
      ret (r == t)
    }
  ].

Definition GUESS_pkg_ff:
  package GUESS_location
    [interface]
    [interface
      #val #[lookup]: 'word → 'key ;
      #val #[guess]: 'word × 'key → 'bool ] :=
  [package
    #def #[lookup] (r: 'word): 'key {
      T ← get table_location ;;
      match getm T r with
      | None =>
          t ← kgen ;;
          #put table_location := (setm T r t) ;;
          ret t
      | Some t =>
          ret t
      end
    } ;
    #def #[guess] ('(m, t): 'word × 'key): 'bool {
      T ← get table_location ;;
      match getm T m with
      | None   => ret false
      | Some r => ret (r == t)
      end
    }
  ].

Definition GUESS := mkpair GUESS_pkg_tt GUESS_pkg_ff.

Definition TAG_location_tt: {fset Location} := fset [:: key_location].
Definition TAG_location_ff: {fset Location} := fset [:: key_location; mac_table_location].

(*
     TAG true
  ≈₀ EVAL_TAG_pkg_tt ∘ EVAL true
  ≈  EVAL_TAG_pkg_tt ∘ EVAL false
  ≈₀ GUESS_TAG_pkg_0 ∘ GUESS true
  ≈  GUESS_TAG_pkg_0 ∘ GUESS false
  ≈₀ GUESS_TAG_pkg_1 ∘ GUESS false
  ≈₀ GUESS_TAG_pkg_2 ∘ GUESS false
  ≈₀ EVAL_TAG_pkg_ff ∘ EVAL false
  ≈  EVAL_TAG_pkg_ff ∘ EVAL true
  ≈₀ TAG false *)


Definition TAG_pkg_tt:
  package TAG_location_tt
    [interface]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      k ← get key_location ;;
      match k with
      | None =>
        k ← kgen ;;
        #put key_location := Some k ;;
        ret (PRF m k)
      | Some k =>
        ret (PRF m k)
      end
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      k ← get key_location ;;
      match k with
      | None =>
        k ← kgen ;;
        #put key_location := Some k ;;
        ret ((PRF m k) == t)
      | Some k =>
        ret ((PRF m k) == t)
      end
    }
  ].

Definition tt := Datatypes.tt.

Definition TAG_pkg_ff:
  package TAG_location_ff
    [interface]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      k_init ← get key_location ;;
      k ← match k_init with
      | None =>
        k ← kgen ;;
        #put key_location := Some k ;;
        ret k
      | Some k =>
        ret k
      end ;;
      t ← ret (PRF m k) ;;
      T ← get mac_table_location ;;
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      T ← get mac_table_location ;;
      match getm T (m, t) with
      | None   => ret false
      | Some _ => ret true
      end
    }
  ].

Definition TAG := mkpair TAG_pkg_tt TAG_pkg_ff.

Definition EVAL_TAG_location_tt: {fset Location} := fset0.
Definition EVAL_TAG_location_ff: {fset Location} := fset [:: mac_table_location].

Definition EVAL_TAG_pkg_tt:
  package EVAL_TAG_location_tt
    [interface #val #[lookup]: 'word → 'key]
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
  package EVAL_TAG_location_ff
    [interface #val #[lookup]: 'word → 'key]
    [interface
      #val #[gettag]: 'word → 'key ;
      #val #[checktag]: 'word × 'key → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'key {
      #import {sig #[lookup]: 'word → 'key } as lookup ;;
      t ← lookup m ;;
      T ← get mac_table_location ;;
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      T ← get mac_table_location ;;
      match getm T (m, t) with
      | None   => ret false
      | Some _ => ret true
      end
    }
  ].

Definition GUESS_TAG_location_0: {fset Location} := fset0.
Definition GUESS_TAG_location_1: {fset Location} := fset [:: mac_table_location ].
Definition GUESS_TAG_location_2: {fset Location} := fset [:: mac_table_location ].

Definition GUESS_TAG_pkg_0:
  package GUESS_TAG_location_0
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

Definition GUESS_TAG_pkg_1:
  package GUESS_TAG_location_1
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
      T ← get mac_table_location ;;
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      #import {sig #[guess]: 'word × 'key → 'bool } as guess ;;
      r ← guess (m, t) ;;
      ret r
    }
  ].

Definition GUESS_TAG_pkg_2:
  package GUESS_TAG_location_2
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
      T ← get mac_table_location ;;
      #put mac_table_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'key): 'bool {
      T ← get mac_table_location ;;
      match getm T (m, t) with
      | None   => ret false
      | Some _ => ret true
      end
    }
  ].

Lemma GUESS_TAG_equiv_0:
  EVAL_TAG_pkg_tt ∘ EVAL false ≈₀ GUESS_TAG_pkg_0 ∘ GUESS true.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m;
    apply rpost_weaken_rule with eq;
    try by intros [] [] e; case: e.
  - simplify_linking.
    apply rreflexivity_rule.
  - simpl.
    ssprove_code_simpl.
    simplify_linking.
    destruct m.
    simpl.
    simplify_linking.
    ssprove_sync_eq => a.
    elim (a _) => [k|];
      apply rreflexivity_rule.
Qed.

Lemma GUESS_TAG_equiv_1:
  GUESS_TAG_pkg_0 ∘ GUESS false ≈₀ GUESS_TAG_pkg_1 ∘ GUESS false.
Proof.
  apply eq_rel_perf_ind with (heap_ignore GUESS_TAG_location_1).
  1: {
    ssprove_invariant.
    eapply fsubset_trans.
    - eapply fsubsetUl.
    - eapply fsubsetUr.
  }
  simplify_eq_rel m;
    simplify_linking.
  - ssprove_sync => a.
    elim (a _) => [k|];
      cbn.
    2: ssprove_sync => ?.
    2: ssprove_sync.
    all: apply r_get_remember_rhs => x.
    all: apply r_put_rhs.
    all: ssprove_restore_mem;
      ssprove_invariant.
    all: apply r_ret.
    all: exact.
  - destruct m.
    simpl.
    simplify_linking.
    ssprove_sync => a.
    elim (a _) => [k|]; cbn.
    all: apply r_ret.
    all: exact.
Qed.

Lemma reflect_iff {P1 P2}:
    reflect P1 P2 ->
    P1 <-> P2.
Proof.
  split => H1;
    destruct H;
    auto;
    discriminate.
Qed.

Ltac ssprove_swap n :=
  ssprove_swap_lhs n;
  ssprove_swap_rhs n.

Ltac ssprove_swap_seq l :=
  ssprove_swap_seq_lhs l;
  ssprove_swap_seq_rhs l.

Lemma GUESS_TAG_equiv_2:
  GUESS_TAG_pkg_1 ∘ GUESS false ≈₀ GUESS_TAG_pkg_2 ∘ GUESS false.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_rhs table_location mac_table_location
      (fun T1 T2 => forall m t,
        getm T2 (m, t) = Some tt <-> getm T1 m = Some t)
  ).
  1: {
    ssprove_invariant;
      try rewrite !in_fsetU !in_fset -!(reflect_iff orP);
      auto.
    split;
      discriminate.
  }
  simplify_eq_rel m;
    simplify_linking.
  (*
    The first function ([gettag]) is exactly the same in both packages.
    It turns out, however, to be pretty complicated since we need to prove the
    invariant holds.
  *)
  - apply r_get_vs_get_remember;
      ssprove_invariant.
    intros T1.
    set o := T1 _.
    destruct o as [k|] eqn:Heq;
      simpl;
      subst o.
    + apply r_get_vs_get_remember;
        ssprove_invariant.
      intros T2.
      apply r_put_vs_put.
      ssprove_restore_mem.
      1: {
        (*
          TODO: This part is weird. [ssprove_invariant] is not able to simplify
          the proof because the precondition is missing a [set_*] pair for
          [table_location] to match the [get_*] pair.
          There is probably a way to simplify this.
        *)
        ssprove_invariant.
        intros s0 s1 Hinv m0 t.
        repeat case: Hinv => Hinv ?.
        rewrite get_set_heap_eq.
        rewrite get_set_heap_neq;
          auto.
        simpl in *.
        subst.
        rewrite setmE.
        destruct (_ == _) eqn:Heqk;
          auto.
        simpl in *.
        move /eqP in Heqk.
        case: Heqk => ? ?.
        subst.
        exact.
      }
      apply r_ret.
      exact.
    + ssprove_sync => a.
      ssprove_swap 0%N.
      apply r_get_vs_get_remember;
        ssprove_invariant.
      intros T2.
      eapply (r_rem_couple_rhs table_location mac_table_location);
        try exact _;
        simpl;
        intros Hinv.
      apply r_put_vs_put.
      apply r_put_vs_put.
      ssprove_restore_mem.
      1: {
        ssprove_invariant => m0 t.
        rewrite !setmE.
        rewrite xpair_eqE.
        destruct (m0 == m) eqn:Heqm;
          rewrite Heqm.
        2: apply Hinv.
        destruct (t == a) eqn:Heqt;
          rewrite Heqt;
          move /eqP in Heqm;
          move /eqP in Heqt;
          subst.
        1: exact.
        rewrite Hinv Heq.
        split.
        1: discriminate.
        case => ?.
        subst.
        by case: Heqt.
      }
      apply r_ret.
      exact.
  - case: m => m t.
    simpl.
    simplify_linking.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    apply r_get_remember_lhs => T1.
    apply r_get_remember_rhs => T2.
    eapply (r_rem_couple_rhs table_location mac_table_location);
      try exact _.
    1: eapply Remembers_rhs_from_tracked_lhs; exact _.
    intros Hinv.
    simpl in Hinv.
    set o1 := T1 _.
    set o2 := T2 _.
    destruct o2 as [[]|] eqn:Heq2.
    2: destruct o1 as [k|] eqn:Heq1.
    all: subst o1 o2.
    + rewrite Hinv in Heq2.
      rewrite Heq2.
      rewrite eq_refl.
      shelve.
    + rewrite -Hinv in Heq1.
      destruct (_ == _) eqn:Heq.
      1: {
        move /eqP in Heq.
        subst.
        rewrite Heq2 in Heq1.
        discriminate.
      }
      shelve.
    + Unshelve.
      all: apply r_ret.
      all: split; auto.
      all: case: H => H ?.
      all: case: H => H ?.
      all: case: H => ? H.
      all: split; auto.
Qed.

Lemma GUESS_TAG_equiv:
  GUESS_TAG_pkg_2 ∘ GUESS false ≈₀ EVAL_TAG_pkg_ff ∘ EVAL false.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m;
    apply rpost_weaken_rule with eq;
    try by intros [] [] e; case: e.
  - simplify_linking.
    apply rreflexivity_rule.
  - ssprove_code_simpl.
    apply rreflexivity_rule.
Qed.

Lemma TAG_equiv_false:
  EVAL_TAG_pkg_ff ∘ EVAL true ≈₀ TAG false.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m;
    apply rpost_weaken_rule with eq;
    try by intros [] [] e; case: e.
  - simplify_linking.
    ssprove_sync_eq.
    elim => [k|];
      apply rreflexivity_rule.
  - destruct m.
    simpl.
    ssprove_sync_eq => a.
    elim (a _) => [k|];
      apply rreflexivity_rule.
Qed.

Lemma TAG_equiv_true:
  TAG true ≈₀ EVAL_TAG_pkg_tt ∘ EVAL true.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m;
    apply rpost_weaken_rule with eq;
    (* TODO: This can be improved right? *)
    try by intros [] [] e; case: e.
    - simplify_linking.
      ssprove_sync_eq.
      elim => [k|];
        apply rreflexivity_rule.
    - destruct m.
      simpl.
      simplify_linking.
      ssprove_sync_eq.
      elim => [k|];
        apply rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(*
  The advantage an adversary can gain over the PRF, i.e. the chance by
  which an adversary can distinguish the PRF from a truly random function.
  Negligible by assumption.
*)
Definition prf_epsilon := Advantage EVAL.

(*
  The advantage an adversary can gain in the GUESS game.
  This is negligible, but we haven't formalised it yet.
*)
Definition statistical_gap :=
  AdvantageE (GUESS_TAG_pkg_0 ∘ GUESS true) (GUESS_TAG_pkg_0 ∘ GUESS false).

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
    fdisjoint LA (fset [:: key_location; table_location; mac_table_location]) ->
    Advantage TAG A <=
    prf_epsilon (A ∘ EVAL_TAG_pkg_tt) +
    statistical_gap A +
    prf_epsilon (A ∘ EVAL_TAG_pkg_ff).
Proof.
  intros vA H.
  unfold prf_epsilon, statistical_gap.
  rewrite !Advantage_E.
  rewrite Advantage_sym.
  ssprove triangle (TAG true) [::
    EVAL_TAG_pkg_tt ∘ EVAL true   ;
    EVAL_TAG_pkg_tt ∘ EVAL false  ;
    GUESS_TAG_pkg_0 ∘ GUESS true  ;
    GUESS_TAG_pkg_0 ∘ GUESS false ;
    GUESS_TAG_pkg_1 ∘ GUESS false ;
    GUESS_TAG_pkg_2 ∘ GUESS false ;
    EVAL_TAG_pkg_ff ∘ EVAL false  ;
    EVAL_TAG_pkg_ff ∘ EVAL true
  ] (TAG false) A
  as ineq.
  eapply le_trans.
  1: exact ineq.
  clear ineq.
  rewrite !Advantage_link.
  rewrite -!cat1s' !fset_cat !fdisjointUr in H.
  move: H.
  repeat (move /andP; case => ?).
  move => ?.
  rewrite (TAG_equiv_true LA) ?GRing.add0r ?fdisjointUr ?fdisjoints0;
    auto.
  rewrite (GUESS_TAG_equiv_0 LA) ?GRing.addr0 ?fdisjointUr ?fdisjoints0;
    auto.
  rewrite (GUESS_TAG_equiv_1 LA) ?GRing.addr0 ?fdisjointUr ?fdisjoints0;
    auto.
  2: by apply /andP.
  rewrite (GUESS_TAG_equiv_2 LA) ?GRing.addr0 ?fdisjointUr;
    auto.
  2,3: by apply /andP.
  rewrite (TAG_equiv_false LA) ?GRing.addr0.
  3: simpl.
  3: unfold TAG_location_ff.
  3: rewrite -cat1s' fset_cat.
  2,3: by rewrite fdisjointUr; apply /andP.
  rewrite (GUESS_TAG_equiv LA) ?GRing.addr0 ?fdisjointUr.
  2,3: by apply /andP.
  rewrite Advantage_sym.
  by [].
Qed.

End PRFMAC_example.
