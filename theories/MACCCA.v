(**
  This formalises Claim 10.10 from "The Joy of Cryptography" (p. 194).
  It is fairly straight forward, significantly more so than PRPCCA.v, but it
  relies on two, somewhat high-level, cryptographic primitives.

  It shows an alternate way to gain CCA security, by augmenting a CPA-secure
  encryption scheme with a MAC.

  The advantage is at most a sum of the MAC and CPA epsilons, which are
  negligible by assumption, hence the scheme is secure.
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

Section MACCCA_example.

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Variable (n: nat).

Definition Word_N: nat := 2^n.
Definition Word: choice_type := chFin (mkpos Word_N).

Context (mac: Word -> Word -> Word).
Context (enc: Word -> Word -> Word).
Context (dec: Word -> Word -> Word).

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Definition mac_key_location: Location := ('option 'word ; 0).
Definition mac_set_location: Location := ('set ('word × 'word) ; 1).
Definition enc_key_location: Location := ('option 'word ; 2).
Definition cca_set_location: Location := ('set ('word × 'word) ; 3).
Definition gettag: nat := 4.
Definition checktag: nat := 5.
Definition eavesdrop: nat := 6.
Definition decrypt: nat := 7.

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

Definition TAG_locs_tt := fset [:: mac_key_location].
Definition TAG_locs_ff := fset [:: mac_key_location; mac_set_location].

Definition kgen {L I l} (_: ('option 'word ; l) \in L): code L I 'word :=
  {code
    k_init ← get ('option 'word ; l) ;;
    match k_init with
    | None =>
        k <$ uniform Word_N ;;
        #put ('option 'word ; l) := Some k ;;
        ret k
    | Some k =>
        ret k
    end
  }.

Lemma TAG_locs_tt_key:
  mac_key_location \in TAG_locs_tt.
Proof.
  auto_in_fset.
Qed.

Definition TAG_pkg_tt:
  package TAG_locs_tt
    [interface]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'word {
      k ← kgen TAG_locs_tt_key ;;
      ret (mac k m)
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      k ← kgen TAG_locs_tt_key ;;
      ret (t == (mac k m))
    }
  ].

Lemma TAG_locs_ff_key:
  mac_key_location \in TAG_locs_ff.
Proof.
  auto_in_fset.
Qed.

Definition TAG_pkg_ff:
  package TAG_locs_ff
    [interface]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package
    #def #[gettag] (m: 'word): 'word {
      T ← get mac_set_location ;;
      k ← kgen TAG_locs_ff_key ;;
      let t := mac k m in
      #put mac_set_location := (setm T (m, t) tt) ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      T ← get mac_set_location ;;
      ret ((m, t) \in domm T)
    }
  ].

Definition TAG := mkpair TAG_pkg_tt TAG_pkg_ff.

Definition CPA_EVAL_locs := fset [:: enc_key_location].

Lemma CPA_EVAL_locs_key:
  enc_key_location \in CPA_EVAL_locs.
Proof.
  auto_in_fset.
Qed.

Definition CPA_EVAL_pkg_tt:
  package CPA_EVAL_locs [interface]
    [interface #val #[eavesdrop]: 'word × 'word → 'word ] :=
  [package
    #def #[eavesdrop] ('(ml, mr): 'word × 'word): 'word {
      k ← kgen CPA_EVAL_locs_key ;;
      ret (enc k ml)
    }
  ].

Definition CPA_EVAL_pkg_ff:
  package CPA_EVAL_locs [interface]
    [interface #val #[eavesdrop]: 'word × 'word → 'word ] :=
  [package
    #def #[eavesdrop] ('(ml, mr): 'word × 'word): 'word {
      k ← kgen CPA_EVAL_locs_key ;;
      ret (enc k mr)
    }
  ].

Definition CPA_EVAL := mkpair CPA_EVAL_pkg_tt CPA_EVAL_pkg_ff.

Definition CCA_EVAL_locs := fset [:: mac_key_location; enc_key_location; cca_set_location].

Lemma CCA_EVAL_locs_mac_key:
  mac_key_location \in CCA_EVAL_locs.
Proof.
  auto_in_fset.
Qed.

Lemma CCA_EVAL_locs_enc_key:
  enc_key_location \in CCA_EVAL_locs.
Proof.
  auto_in_fset.
Qed.

Definition CCA_EVAL_pkg_tt:
  package CCA_EVAL_locs [interface]
    [interface
      #val #[eavesdrop]: 'word × 'word → 'word × 'word ;
      #val #[decrypt]: 'word × 'word → 'option 'word ] :=
  [package
    #def #[eavesdrop] ('(ml, mr): 'word × 'word): 'word × 'word {
      S ← get cca_set_location ;;
      ke ← kgen CCA_EVAL_locs_enc_key ;;
      km ← kgen CCA_EVAL_locs_mac_key ;;
      let c := enc ke ml in
      let t := mac km c in
      #put cca_set_location := (setm S (c, t) tt) ;;
      ret (c, t)
    } ;
    #def #[decrypt] ('(c, t): 'word × 'word): 'option 'word {
      S ← get cca_set_location ;;
      if ((c, t) \in domm S) then ret None else
      km ← kgen CCA_EVAL_locs_mac_key ;;
      if (t != mac km c) then ret None else
      ke ← kgen CCA_EVAL_locs_enc_key ;;
      ret (Some (dec ke c))
    }
  ].

Definition CCA_EVAL_pkg_ff:
  package CCA_EVAL_locs [interface]
    [interface
      #val #[eavesdrop]: 'word × 'word → 'word × 'word ;
      #val #[decrypt]: 'word × 'word → 'option 'word ] :=
  [package
    #def #[eavesdrop] ('(ml, mr): 'word × 'word): 'word × 'word {
      S ← get cca_set_location ;;
      ke ← kgen CCA_EVAL_locs_enc_key ;;
      km ← kgen CCA_EVAL_locs_mac_key ;;
      let c := enc ke mr in
      let t := mac km c in
      #put cca_set_location := (setm S (c, t) tt) ;;
      ret (c, t)
    } ;
    #def #[decrypt] ('(c, t): 'word × 'word): 'option 'word {
      S ← get cca_set_location ;;
      if ((c, t) \in domm S) then ret None else
      km ← kgen CCA_EVAL_locs_mac_key ;;
      if (t != mac km c) then ret None else
      ke ← kgen CCA_EVAL_locs_enc_key ;;
      ret (Some (dec ke c))
    }
  ].

Definition CCA_EVAL := mkpair CCA_EVAL_pkg_tt CCA_EVAL_pkg_ff.

Definition CCA_EVAL_TAG_locs := fset [:: enc_key_location; cca_set_location].

Lemma CCA_EVAL_TAG_locs_enc_key:
  enc_key_location \in CCA_EVAL_TAG_locs.
Proof.
  auto_in_fset.
Qed.

Definition CCA_EVAL_TAG_pkg_tt:
  package CCA_EVAL_TAG_locs
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ]
    [interface
      #val #[eavesdrop]: 'word × 'word → 'word × 'word ;
      #val #[decrypt]: 'word × 'word → 'option 'word ] :=
  [package
    #def #[eavesdrop] ('(ml, mr): 'word × 'word): 'word × 'word {
      #import {sig #[gettag]: 'word → 'word } as gettag ;;
      S ← get cca_set_location ;;
      ke ← kgen CCA_EVAL_TAG_locs_enc_key ;;
      let c := enc ke ml in
      t ← gettag c ;;
      #put cca_set_location := (setm S (c, t) tt) ;;
      ret (c, t)
    } ;
    #def #[decrypt] ('(c, t): 'word × 'word): 'option 'word {
      #import {sig #[checktag]: 'word × 'word → 'bool } as checktag ;;
      S ← get cca_set_location ;;
      if ((c, t) \in domm S) then ret None else
      r ← checktag (c, t) ;;
      if (~~ r) then ret None else
      ke ← kgen CCA_EVAL_TAG_locs_enc_key ;;
      ret (Some (dec ke c))
    }
  ].

Definition CCA_EVAL_TAG_pkg_ff:
  package CCA_EVAL_TAG_locs
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ]
    [interface
      #val #[eavesdrop]: 'word × 'word → 'word × 'word ;
      #val #[decrypt]: 'word × 'word → 'option 'word ] :=
  [package
    #def #[eavesdrop] ('(ml, mr): 'word × 'word): 'word × 'word {
      #import {sig #[gettag]: 'word → 'word } as gettag ;;
      S ← get cca_set_location ;;
      ke ← kgen CCA_EVAL_TAG_locs_enc_key ;;
      let c := enc ke mr in
      t ← gettag c ;;
      #put cca_set_location := (setm S (c, t) tt) ;;
      ret (c, t)
    } ;
    #def #[decrypt] ('(c, t): 'word × 'word): 'option 'word {
      #import {sig #[checktag]: 'word × 'word → 'bool } as checktag ;;
      S ← get cca_set_location ;;
      if ((c, t) \in domm S) then ret None else
      r ← checktag (c, t) ;;
      if (~~ r) then ret None else
      ke ← kgen CCA_EVAL_TAG_locs_enc_key ;;
      ret (Some (dec ke c))
    }
  ].

Definition CCA_EVAL_HYB_locs := fset [:: mac_key_location; mac_set_location; cca_set_location].

Lemma CCA_EVAL_HYB_locs_mac_key:
  mac_key_location \in CCA_EVAL_HYB_locs.
Proof.
  auto_in_fset.
Qed.

Definition CCA_EVAL_HYB_pkg:
  package CCA_EVAL_HYB_locs
    [interface #val #[eavesdrop]: 'word × 'word → 'word ]
    [interface
      #val #[eavesdrop]: 'word × 'word → 'word × 'word ;
      #val #[decrypt]: 'word × 'word → 'option 'word ] :=
  [package
    #def #[eavesdrop] ('(ml, mr): 'word × 'word): 'word × 'word {
      #import {sig #[eavesdrop]: 'word × 'word → 'word } as eavesdrop ;;
      S ← get cca_set_location ;;
      c ← eavesdrop (ml, mr) ;;
      T ← get mac_set_location ;;
      km ← kgen CCA_EVAL_HYB_locs_mac_key ;;
      let t := mac km c in
      #put mac_set_location := (setm T (c, t) tt) ;;
      #put cca_set_location := (setm S (c, t) tt) ;;
      ret (c, t)
    } ;
    #def #[decrypt] ('(c, t): 'word × 'word): 'option 'word {
      ret None
    }
  ].

Lemma CCA_EVAL_equiv_true:
  CCA_EVAL true ≈₀ CCA_EVAL_TAG_pkg_tt ∘ TAG true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  all: by apply: rreflexivity_rule.
Qed.

Lemma CCA_EVAL_HYB_equiv_true:
  CCA_EVAL_TAG_pkg_tt ∘ TAG false ≈₀ CCA_EVAL_HYB_pkg ∘ CPA_EVAL true.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_lhs cca_set_location mac_set_location
      (fun S T => S = T)
  ).
  1: {
    ssprove_invariant=> //=.
    all: by rewrite /CCA_EVAL_TAG_locs /TAG_locs_ff !fset_cons !in_fsetU !in_fset1 eq_refl Bool.orb_true_r.
  }
  simplify_eq_rel m.
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  - case: m => [ml mr].
    apply: r_get_vs_get_remember => S.
    ssprove_sync=> [|[ke|]];
      first by move=> ? ? ->.
    2: ssprove_sync=> ke;
      ssprove_sync;
      first by move=> ? ? ->.
    all: apply: r_get_vs_get_remember => T.
    all: ssprove_sync=> [|[km|]];
      first by move=> ? ? ->.
    2,4: ssprove_sync=> km;
      ssprove_sync;
      first by move=> ? ? ->.
    all: apply: (r_rem_couple_lhs cca_set_location mac_set_location) => Hinv.
    all: apply: r_put_vs_put.
    all: apply: r_put_vs_put.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
    all: by rewrite Hinv.
  - case: m => [c t].
    apply: r_get_remember_lhs => S.
    destruct ((c, t) \in domm S) eqn:Heq.
    all: rewrite Heq.
    1: by apply: r_ret => ? ? [].
    apply: r_get_remember_lhs => T.
    apply: (r_rem_couple_lhs cca_set_location mac_set_location) => Hinv.
    rewrite -Hinv Heq /=.
    by apply: r_ret => ? ? [] [].
Qed.

Lemma CCA_EVAL_HYB_equiv_false:
  CCA_EVAL_HYB_pkg ∘ CPA_EVAL false ≈₀ CCA_EVAL_TAG_pkg_ff ∘ TAG false.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_rhs cca_set_location mac_set_location
      (fun S T => S = T)
  ).
  1: {
    ssprove_invariant=> //=.
    all: by rewrite /CCA_EVAL_TAG_locs /TAG_locs_ff !fset_cons !in_fsetU !in_fset1 eq_refl !Bool.orb_true_r.
  }
  simplify_eq_rel m.
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  - case: m => [ml mr].
    apply: r_get_vs_get_remember => S.
    ssprove_sync=> [|[ke|]];
      first by move=> ? ? ->.
    2: ssprove_sync=> ke;
      ssprove_sync;
      first by move=> ? ? ->.
    all: apply: r_get_vs_get_remember => T.
    all: ssprove_sync=> [|[km|]];
      first by move=> ? ? ->.
    2,4: ssprove_sync=> km;
      ssprove_sync;
      first by move=> ? ? ->.
    all: apply: (r_rem_couple_rhs cca_set_location mac_set_location) => Hinv.
    all: apply: r_put_vs_put.
    all: apply: r_put_vs_put.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
    all: by rewrite Hinv.
  - case: m => [c t].
    apply: r_get_remember_rhs => S.
    destruct ((c, t) \in domm S) eqn:Heq.
    all: rewrite Heq.
    1: by apply: r_ret => ? ? [].
    apply: r_get_remember_rhs => T.
    apply: (r_rem_couple_rhs cca_set_location mac_set_location) => Hinv.
    rewrite -Hinv Heq /=.
    by apply: r_ret => ? ? [] [].
Qed.

Lemma CCA_EVAL_equiv_false:
  CCA_EVAL_TAG_pkg_ff ∘ TAG true ≈₀ CCA_EVAL false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  all: by apply: rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the MAC, i.e. the chance by
  which an adversary can construct a forge a MAC.
  Negligible by assumption.
*)
Definition mac_epsilon := Advantage TAG.

(**
  The advantage an adversary can gain over the CPA-secure encryption, i.e. the
  chance by which an adversary can distinguish which message a ciphertext
  belongs to.
  Negligible by assumption.
*)
Definition cpa_epsilon := Advantage CPA_EVAL.

Theorem security_based_on_mac LA A:
  ValidPackage LA
    [interface
      #val #[eavesdrop]: 'word × 'word → 'word × 'word ;
      #val #[decrypt]: 'word × 'word → 'option 'word ]
    A_export A ->
  fdisjoint LA (
    TAG_locs_tt :|: TAG_locs_ff :|: CPA_EVAL_locs :|:
    CCA_EVAL_locs :|: CCA_EVAL_TAG_locs :|: CCA_EVAL_HYB_locs
    ) ->
  Advantage CCA_EVAL A <=
  mac_epsilon (A ∘ CCA_EVAL_TAG_pkg_tt) +
  cpa_epsilon (A ∘ CCA_EVAL_HYB_pkg) +
  mac_epsilon (A ∘ CCA_EVAL_TAG_pkg_ff).
Proof.
  move=> vA H.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (CCA_EVAL true) [::
    CCA_EVAL_TAG_pkg_tt ∘ TAG true ;
    CCA_EVAL_TAG_pkg_tt ∘ TAG false ;
    CCA_EVAL_HYB_pkg ∘ CPA_EVAL true ;
    CCA_EVAL_HYB_pkg ∘ CPA_EVAL false ;
    CCA_EVAL_TAG_pkg_ff ∘ TAG false ;
    CCA_EVAL_TAG_pkg_ff ∘ TAG true
  ] (CCA_EVAL false) A as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite !fdisjointUr in H.
  move: H => /andP [/andP [/andP [/andP [/andP [H1 H2] H3] H4] H5] H6].
  move: {ineq H1 H2 H3 H4 H5 H6} (H1, H2, H3, H4, H5, H6) => H.
  rewrite CCA_EVAL_equiv_true ?fdisjointUr ?H // GRing.add0r.
  rewrite CCA_EVAL_HYB_equiv_true ?fdisjointUr ?H // GRing.addr0.
  rewrite CCA_EVAL_HYB_equiv_false ?fdisjointUr ?H // GRing.addr0.
  rewrite CCA_EVAL_equiv_false ?fdisjointUr ?H // GRing.addr0.
  rewrite /mac_epsilon /cpa_epsilon !Advantage_E -!Advantage_link.
  by rewrite (Advantage_sym (TAG true)) (Advantage_sym (CPA_EVAL true)).
Qed.

End MACCCA_example.
