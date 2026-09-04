/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A self-contained deterministic graph-container lemma and the elementary
binomial-tail estimate used in the proof of Erdős Problem 748.

This module deliberately imports only Mathlib.  Keeping these two generic
ingredients here makes the proof of Problem 748 independent of unrelated
Erdős-problem developments.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Common
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos748.GraphContainer

attribute [local instance] Classical.propDecidable

open Finset
open Nat
open Real

def degree_in {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
  (v : V) :
    ℕ :=
  (A.filter (G.Adj v ·)).card

def container_algorithm {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (S : Finset V) (A : Finset V) : Finset V :=
  if h : (A.filter (fun v => degree_in G A v ≥ Δ)).Nonempty then
    let v := (A.filter (fun v => degree_in G A v ≥ Δ)).min' h
    if v ∈ S then
      container_algorithm G Δ S (A \ (insert v (Finset.univ.filter (G.Adj v ·))))
    else
      container_algorithm G Δ S (A.erase v)
  else
    A
termination_by A.card
decreasing_by
  · refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ?_)
    refine ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hvA : v ∈ A := Finset.mem_filter.mp (Finset.min'_mem _ h) |>.1
    have hvSub : v ∈ A \ insert v (Finset.univ.filter (G.Adj v ·)) := by
      rw [heq]
      exact hvA
    exact (Finset.mem_sdiff.mp hvSub).2 (Finset.mem_insert_self _ _)
  · exact Finset.card_erase_lt_of_mem ( Finset.mem_filter.mp ( Finset.min'_mem _ h ) |>.1 )

/-
Definition of the process that generates S and A from an independent set I.
generate_S_and_A runs the algorithm:
If v ∈ I, add v to S and remove v and neighbors from A.
If v ∉ I, remove v from A.
get_S extracts the final set S.
-/
def generate_S_and_A {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) : Finset V × Finset V :=
  if h : (A.filter (fun v => degree_in G A v ≥ Δ)).Nonempty then
    let v := (A.filter (fun v => degree_in G A v ≥ Δ)).min' h
    if v ∈ I then
      generate_S_and_A G Δ I (insert v S_acc) (A \ (insert v (Finset.univ.filter (G.Adj v ·))))
    else
      generate_S_and_A G Δ I S_acc (A.erase v)
  else
    (S_acc, A)
termination_by A.card
decreasing_by
  · refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ?_)
    refine ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hvA : v ∈ A := Finset.mem_filter.mp (Finset.min'_mem _ h) |>.1
    have hvSub : v ∈ A \ insert v (Finset.univ.filter (G.Adj v ·)) := by
      rw [heq]
      exact hvA
    exact (Finset.mem_sdiff.mp hvSub).2 (Finset.mem_insert_self _ _)
  · exact Finset.card_erase_lt_of_mem ( Finset.mem_filter.mp ( Finset.min'_mem _ h ) |>.1 )

def get_S {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) : Finset V :=
  (generate_S_and_A G Δ I ∅ Finset.univ).1

/-
The set S returned by the container algorithm is a subset of the input independent set I.
-/
lemma get_S_subset_I {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) :
    get_S G Δ I ⊆ I := by
      -- By induction on the recursive calls of `generate_S_and_A`, we can show that the first
      -- component is always a subset of `I`.
      have h_ind : ∀ (S_acc : Finset V) (A :
          Finset V), S_acc ⊆ I → (generate_S_and_A G Δ I S_acc A).1 ⊆ I := by
        intro S_acc A hS_acc
        induction hcard : A.card using Nat.strong_induction_on generalizing S_acc A with
        | h n ih =>
            unfold generate_S_and_A;
            field_simp;
            split_ifs <;> simp_all +decide only [ge_iff_le];
            · convert ih _ _ _ _ _ rfl using 1;
              · rw [ ← hcard, Finset.card_sdiff ];
                refine Nat.sub_lt ?_ ?_;
                · exact Finset.card_pos.mpr ( by
                  obtain ⟨ v, hv ⟩ := ‹ { v ∈ A | Δ ≤ degree_in G A v }.Nonempty ›;
                  exact ⟨ v, Finset.mem_filter.mp hv |>.1 ⟩ );
                · refine Finset.card_pos.mpr
                    ⟨ Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) ‹_›,
                      Finset.mem_inter.mpr ⟨ Finset.mem_insert_self _ _, ?_ ⟩ ⟩;
                  exact Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1;
              · grind;
            · exact ih _ ( by
              rw [
                Finset.card_erase_of_mem
                  ( Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ) ];
              exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _,
                Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ⟩ ) zero_lt_one
                |> LT.lt.trans_le
                <| by linarith ) _ _ hS_acc rfl;
      exact h_ind ∅ _ ( Finset.empty_subset _ )

/-
The quantity (Δ+1)|S| + |A| is non-increasing during the algorithm.
-/
lemma generate_S_and_A_size_bound {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) :
    let res := generate_S_and_A G Δ I S_acc A
    (Δ + 1) * res.1.card + res.2.card ≤ (Δ + 1) * S_acc.card + A.card := by
      induction hcard : Finset.card A using Nat.strong_induction_on generalizing S_acc A with
      | h k ih =>
          unfold generate_S_and_A;
          by_cases h : Finset.Nonempty ( Finset.filter ( fun v => degree_in G A v ≥ Δ ) A )<;>
            simp_all +decide only [ge_iff_le];
          · split_ifs <;> try contradiction
            · let v := Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) ‹_›
              refine le_trans
                (ih (Finset.card (A \ insert v (Finset.univ.filter (G.Adj v ·)))) ?_
                  (insert v S_acc) (A \ insert v (Finset.univ.filter (G.Adj v ·))) rfl) ?_;
              · refine lt_of_lt_of_le
                  ( Finset.card_lt_card (t := A) ( Finset.ssubset_iff_subset_ne.mpr ?_ ) ) ?_;
                · constructor
                  · intro y hy
                    exact Finset.mem_sdiff.mp hy |>.1
                  · intro h_eq
                    have hvA : v ∈ A :=
                      Finset.mem_filter.mp (Finset.min'_mem _ h) |>.1
                    have hv_not : v ∉ A \ insert v (Finset.univ.filter (G.Adj v ·)) := by
                      simp
                    exact hv_not (h_eq.symm ▸ hvA)
                · exact le_of_eq hcard;
              · rw [ Finset.card_sdiff ];
                have h_removed :
                    Δ + 1 ≤
                      (insert (Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) h)
                        (Finset.univ.filter (G.Adj (Finset.min' (Finset.filter (fun v =>
                          degree_in G A v ≥ Δ) A) h) ·)) ∩ A).card := by
                  let v := Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) h
                  have hv := Finset.min'_mem (Finset.filter (fun v => degree_in G A v ≥ Δ) A) h
                  have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
                  have hdeg : Δ ≤ degree_in G A v := (Finset.mem_filter.mp hv).2
                  have hsub :
                      insert v (A.filter (G.Adj v ·)) ⊆
                        insert v (Finset.univ.filter (G.Adj v ·)) ∩ A := by
                    intro x hx
                    rw [Finset.mem_inter]
                    rw [Finset.mem_insert] at hx ⊢
                    rcases hx with rfl | hx
                    · exact ⟨Or.inl rfl, hvA⟩
                    · exact ⟨Or.inr (by simpa using (Finset.mem_filter.mp hx).2),
                        (Finset.mem_filter.mp hx).1⟩
                  have hsmall :
                      degree_in G A v + 1 ≤
                        (insert v (Finset.univ.filter (G.Adj v ·)) ∩ A).card := by
                    change (A.filter (G.Adj v ·)).card + 1 ≤
                      (insert v (Finset.univ.filter (G.Adj v ·)) ∩ A).card
                    rw [← Finset.card_insert_of_notMem (s := A.filter (G.Adj v ·))]
                    · exact Finset.card_le_card hsub
                    · simp
                  exact (Nat.succ_le_succ hdeg).trans hsmall
                refine le_trans
                  ( add_le_add_right ( Nat.sub_le_sub_left h_removed A.card )
                    ((Δ + 1) * (insert v S_acc).card) ) ?_;
                · have h_delta_le_card : Δ + 1 ≤ k := by
                    let v := Finset.min' ( Finset.filter ( fun v =>
                      degree_in G A v ≥ Δ ) A ) ‹_›
                    have h_deg_ge : degree_in G A v ≥ Δ := by
                      exact Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.2;
                    have h_deg_lt : degree_in G A v < Finset.card A := by
                      refine lt_of_lt_of_le
                        ( Finset.card_lt_card ( Finset.filter_ssubset.mpr ?_ ) ) ?_;
                      · exact ⟨ _, Finset.min'_mem _ ‹_›
                          |> Finset.mem_filter.mp |>.1, G.loopless.1 v ⟩;
                      · rfl;
                    linarith;
                  by_cases hvS : v ∈ S_acc
                  · simp [hvS]
                    omega
                  · simp [hvS, Nat.mul_succ, Nat.add_assoc, Nat.add_comm]
                    omega
            · have :=
              ih ( Finset.card ( A.erase ( Finset.min' ( Finset.filter ( fun v =>
                Δ ≤ degree_in G A v ) A ) h ) ) ) ?_ S_acc
                ( A.erase ( Finset.min' ( Finset.filter ( fun v =>
                  Δ ≤ degree_in G A v ) A ) h ) ) ?_;
              · exact this.trans ( add_le_add_right ( by
                  have hAcard : A.card = k := by assumption
                  exact ( Finset.card_le_card ( Finset.erase_subset _ _ ) ).trans
                    ( le_of_eq hAcard ) )
                    _ );
              · exact lt_of_lt_of_le ( Finset.card_erase_lt_of_mem ( Finset.mem_filter.mp (
                Finset.min'_mem _ h ) |>.1 ) ) ( by linarith );
              · rfl;
          · grind

/-
The generated S set is contained in the union of the accumulator and the independent set I.
-/
lemma generate_S_subset_union {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) :
    (generate_S_and_A G Δ I S_acc A).1 ⊆ S_acc ∪ I := by
      induction A using Finset.strongInduction generalizing S_acc with
      | _ A ih =>
          unfold generate_S_and_A;
          norm_num +zetaDelta at *;
          split_ifs;
          · let v := Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) ‹_›
            refine Finset.Subset.trans
              (ih (A \ insert v (Finset.univ.filter (G.Adj v ·))) ?_ (insert v S_acc)) ?_;
            · simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
              exact ⟨ fun x hx hx' hx'' =>
                hx, _, Finset.min'_mem _ ‹_› |> Finset.mem_filter.mp |>.1, fun _ => by tauto ⟩;
            · grind;
          · exact ih _ ( Finset.erase_ssubset
            <| Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ) _;
          · exact Finset.subset_union_left

/-
The accumulator set is a subset of the generated S set.
-/
lemma S_acc_subset_generate_S {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) :
    S_acc ⊆ (generate_S_and_A G Δ I S_acc A).1 := by
      induction hcard : A.card using Nat.strong_induction_on generalizing S_acc A with
      | h k ih =>
          unfold generate_S_and_A;
          field_simp;
          split_ifs <;> simp_all +decide only [ge_iff_le];
          · intro x hx;
            convert ih _ _ _ _ rfl ( Finset.mem_insert_of_mem hx ) using 1;
            refine lt_of_lt_of_le
              ( Finset.card_lt_card (t := A) ( Finset.ssubset_iff_subset_ne.mpr ?_ ) ) ?_;
            · constructor
              · intro y hy
                exact Finset.mem_sdiff.mp hy |>.1
              · intro h_eq
                let v := Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) ‹_›
                have hvA : v ∈ A :=
                  Finset.mem_filter.mp (Finset.min'_mem _ ‹_›) |>.1
                have hv_not : v ∉ A \ insert v (Finset.univ.filter (G.Adj v ·)) := by
                  simp
                exact hv_not (h_eq.symm ▸ hvA)
            · exact le_of_eq hcard;
          · exact ih _ ( by
            rw [ Finset.card_erase_of_mem ( Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ) ];
            exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _,
              Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ⟩ ) zero_lt_one
              |> LT.lt.trans_le
              <| by simp +decide [ hcard ] ) _ _ rfl
          · exact fun _ hx ↦ hx

/-
The independent set I restricted to A is covered by the new elements in S and the final set A,
assuming S_acc and A are disjoint.
-/
lemma generate_S_and_A_invariant {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V)
    (hI : G.IsIndepSet (I : Set V)) (h_disjoint : Disjoint S_acc A) :
    let res := generate_S_and_A G Δ I S_acc A
    I ∩ A ⊆ (res.1 \ S_acc) ∪ res.2 := by
  induction hcard : A.card using Nat.strong_induction_on generalizing S_acc A with
  | h n ih =>
      unfold generate_S_and_A
      split_ifs <;> simp_all only [ge_iff_le]
      split_ifs
      · let v := Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) ‹_›
        let A' := A \ insert v (Finset.univ.filter (G.Adj v ·))
        let S' := insert v S_acc
        change I ∩ A ⊆
          (generate_S_and_A G Δ I S' A').1 \ S_acc ∪
            (generate_S_and_A G Δ I S' A').2
        have hvA : v ∈ A := by
          exact Finset.mem_filter.mp (Finset.min'_mem _ ‹_›) |>.1
        have hvI : v ∈ I := by
          simpa [v] using ‹Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) _ ∈ I›
        have hcard' : A'.card < n := by
          refine lt_of_lt_of_le (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ?_))
            (le_of_eq hcard)
          refine ⟨Finset.sdiff_subset, ?_⟩
          intro heq
          have : v ∈ A' := heq.symm ▸ hvA
          exact (Finset.mem_sdiff.mp this).2 (Finset.mem_insert_self _ _)
        have hdisjoint' : Disjoint S' A' := by
          rw [Finset.disjoint_left]
          intro y hyS hyA'
          rcases Finset.mem_insert.mp hyS with rfl | hyS
          · exact (Finset.mem_sdiff.mp hyA').2 (Finset.mem_insert_self _ _)
          · exact (Finset.disjoint_left.mp h_disjoint hyS) (Finset.mem_sdiff.mp hyA').1
        intro x hx
        have hxI : x ∈ I := (Finset.mem_inter.mp hx).1
        have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
        by_cases hxv : x = v
        · subst x
          refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
          · exact S_acc_subset_generate_S G Δ I S' A' (Finset.mem_insert_self _ _)
          · exact fun hvS => Finset.disjoint_left.mp h_disjoint hvS hvA
        · have hxA' : x ∈ A' := by
            refine Finset.mem_sdiff.mpr ⟨hxA, ?_⟩
            intro hxremoved
            rcases Finset.mem_insert.mp hxremoved with hx | hx
            · exact hxv hx
            · have hadj : G.Adj v x := (Finset.mem_filter.mp hx).2
              exact (hI hxI hvI hxv) (G.adj_symm hadj)
          have hxrec := ih A'.card hcard' S' A' hdisjoint' rfl
            (Finset.mem_inter.mpr ⟨hxI, hxA'⟩)
          rcases Finset.mem_union.mp hxrec with hxleft | hxright
          · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxleft).1, ?_⟩)
            exact fun hxS => (Finset.mem_sdiff.mp hxleft).2 (Finset.mem_insert_of_mem hxS)
          · exact Finset.mem_union_right _ hxright
      · let v := Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) ‹_›
        let A' := A.erase v
        change I ∩ A ⊆
          (generate_S_and_A G Δ I S_acc A').1 \ S_acc ∪
            (generate_S_and_A G Δ I S_acc A').2
        have hvA : v ∈ A := by
          exact Finset.mem_filter.mp (Finset.min'_mem _ ‹_›) |>.1
        have hvI : v ∉ I := by
          simpa [v] using ‹Finset.min' (Finset.filter (fun v => Δ ≤ degree_in G A v) A) _ ∉ I›
        have hcard' : A'.card < n := by
          exact (Finset.card_erase_lt_of_mem hvA).trans_le (le_of_eq hcard)
        have hdisjoint' : Disjoint S_acc A' :=
          h_disjoint.mono_right (Finset.erase_subset _ _)
        intro x hx
        have hxI : x ∈ I := (Finset.mem_inter.mp hx).1
        have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
        have hxA' : x ∈ A' := Finset.mem_erase.mpr ⟨fun hxv => hvI (hxv ▸ hxI), hxA⟩
        exact ih A'.card hcard' S_acc A' hdisjoint' rfl
          (Finset.mem_inter.mpr ⟨hxI, hxA'⟩)
      · intro x hx
        exact Finset.mem_union_right _ (Finset.mem_inter.mp hx).2

/-
The container algorithm produces the same set A as the generation process, given consistent inputs.
-/
lemma container_algorithm_eq_generate_A_correct {V : Type*} [Fintype V]
  [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V)
    (h_disjoint : Disjoint S_acc A) (h_S_acc_sub : S_acc ⊆ I) :
    let res := generate_S_and_A G Δ I S_acc A
    container_algorithm G Δ res.1 A = res.2 := by
  induction A using Finset.strongInduction generalizing S_acc I Δ G with
  | _ A ih =>
      rw [generate_S_and_A]
      split_ifs <;> simp only
      split_ifs
      · let v := Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) ‹_›
        let A' := A \ insert v (Finset.univ.filter (G.Adj v ·))
        let S' := insert v S_acc
        change container_algorithm G Δ (generate_S_and_A G Δ I S' A').1 A =
          (generate_S_and_A G Δ I S' A').2
        have hvA : v ∈ A := by
          exact Finset.mem_filter.mp (Finset.min'_mem _ ‹_›) |>.1
        have hvI : v ∈ I := by
          simpa [v] using ‹Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) _ ∈ I›
        have hssub : A' ⊂ A := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
          intro heq
          have : v ∈ A' := heq.symm ▸ hvA
          exact (Finset.mem_sdiff.mp this).2 (Finset.mem_insert_self _ _)
        have hdisjoint' : Disjoint S' A' := by
          rw [Finset.disjoint_left]
          intro x hxS hxA'
          rcases Finset.mem_insert.mp hxS with rfl | hxS
          · exact (Finset.mem_sdiff.mp hxA').2 (Finset.mem_insert_self _ _)
          · exact (Finset.disjoint_left.mp h_disjoint hxS) (Finset.mem_sdiff.mp hxA').1
        have hS'sub : S' ⊆ I := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hvI
          · exact h_S_acc_sub hx
        have hvFinal : v ∈ (generate_S_and_A G Δ I S' A').1 :=
          S_acc_subset_generate_S G Δ I S' A' (Finset.mem_insert_self _ _)
        rw [container_algorithm]
        simp only [‹(Finset.filter (fun v => degree_in G A v ≥ Δ) A).Nonempty›,
          dite_true]
        change (if v ∈ (generate_S_and_A G Δ I S' A').1 then
            container_algorithm G Δ (generate_S_and_A G Δ I S' A').1 A'
          else container_algorithm G Δ (generate_S_and_A G Δ I S' A').1 (A.erase v)) =
          (generate_S_and_A G Δ I S' A').2
        rw [if_pos hvFinal]
        exact ih A' hssub G Δ I S' hdisjoint' hS'sub
      · let v := Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) ‹_›
        let A' := A.erase v
        change container_algorithm G Δ (generate_S_and_A G Δ I S_acc A').1 A =
          (generate_S_and_A G Δ I S_acc A').2
        have hvA : v ∈ A := by
          exact Finset.mem_filter.mp (Finset.min'_mem _ ‹_›) |>.1
        have hvI : v ∉ I := by
          simpa [v] using ‹Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) _ ∉ I›
        have hvS : v ∉ S_acc := fun hv => Finset.disjoint_left.mp h_disjoint hv hvA
        have hvFinal : v ∉ (generate_S_and_A G Δ I S_acc A').1 := by
          intro hv
          rcases Finset.mem_union.mp (generate_S_subset_union G Δ I S_acc A' hv) with hv | hv
          · exact hvS hv
          · exact hvI hv
        rw [container_algorithm]
        simp only [‹(Finset.filter (fun v => degree_in G A v ≥ Δ) A).Nonempty›,
          dite_true]
        change (if v ∈ (generate_S_and_A G Δ I S_acc A').1 then
            container_algorithm G Δ (generate_S_and_A G Δ I S_acc A').1
              (A \ insert v (Finset.univ.filter (G.Adj v ·)))
          else container_algorithm G Δ (generate_S_and_A G Δ I S_acc A').1 A') =
          (generate_S_and_A G Δ I S_acc A').2
        rw [if_neg hvFinal]
        exact ih A' (Finset.erase_ssubset hvA) G Δ I S_acc
          (h_disjoint.mono_right (Finset.erase_subset _ _)) h_S_acc_sub
      · rw [container_algorithm]
        simp only [‹¬(Finset.filter (fun v => degree_in G A v ≥ Δ) A).Nonempty›,
          dite_false]

/-
The container algorithm always returns a set where every vertex has degree strictly less than Δ in
the induced subgraph.
-/
def is_low_degree {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (A :
  Finset V) :
    Prop :=
  ∀ v ∈ A, degree_in G A v < Δ

lemma container_algorithm_returns_low_degree {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (S : Finset V) (A : Finset V) :
    is_low_degree G Δ (container_algorithm G Δ S A) := by
      induction A using Finset.strongInductionOn generalizing S with
      | _ A ih =>
          unfold container_algorithm
          split
          · rename_i hhigh
            let v := (Finset.filter (fun v => degree_in G A v ≥ Δ) A).min' hhigh
            change is_low_degree G Δ
              (if v ∈ S then
                container_algorithm G Δ S (A \ insert v (Finset.univ.filter (G.Adj v ·)))
              else
                container_algorithm G Δ S (A.erase v))
            by_cases hvS : v ∈ S
            · simp [hvS]
              exact ih (A \ insert v (Finset.univ.filter (G.Adj v ·))) (by
                refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
                intro h_eq
                have hvA : v ∈ A := (Finset.mem_filter.mp (Finset.min'_mem _ hhigh)).1
                have hv_not : v ∉ A \ insert v (Finset.univ.filter (G.Adj v ·)) := by
                  simp [v]
                exact hv_not (by simpa [h_eq] using hvA)) S
            · simp [hvS]
              exact ih (A.erase v) (Finset.erase_ssubset
                ((Finset.mem_filter.mp (Finset.min'_mem _ hhigh)).1)) S
          · intro v hv
            have hv_not : ¬ degree_in G A v ≥ Δ := by
              intro hv_degree
              exact ‹¬(Finset.filter (fun v => degree_in G A v ≥ Δ) A).Nonempty›
                ⟨v, Finset.mem_filter.mpr ⟨hv, hv_degree⟩⟩
            omega

/-
The container algorithm returns a set inducing a subgraph with maximum degree strictly less than Δ.
-/
lemma container_algorithm_max_degree {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : Δ ≥ 1) (S : Finset V) (A : Finset V) :
    (G.induce (container_algorithm G Δ S A)).maxDegree < Δ := by
      let C := container_algorithm G Δ S A
      have hlow : is_low_degree G Δ C := container_algorithm_returns_low_degree G Δ S A
      have hdeg : ∀ v : (C : Set V), (G.induce (C : Set V)).degree v = degree_in G C v := by
        intro v
        unfold SimpleGraph.degree degree_in
        refine Finset.card_bij (fun x hx => (x : V)) ?_ ?_ ?_
        · intro x hx
          simp only [mem_filter, SetLike.coe_mem, true_and] at hx ⊢
          simpa [SimpleGraph.mem_neighborFinset] using hx
        · intro x hx y hy hxy
          exact Subtype.ext hxy
        · intro y hy
          refine ⟨⟨y, (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩
          simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hy).2
      refine lt_of_le_of_lt ((G.induce (C : Set V)).maxDegree_le_of_forall_degree_le (Δ - 1) ?_) ?_
      · intro v
        rw [hdeg v]
        exact Nat.le_pred_of_lt (hlow v v.2)
      · omega

/-
The Graph Container Lemma: For every independent set I, there is a small subset S such that I is
contained in S ∪ f(S) and f(S) induces a graph with small maximum degree.
-/
theorem graph_container_lemma {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : Δ ≥ 1) :
    ∃ f : Finset V → Finset V,
      ∀ I : Finset V, G.IsIndepSet (I : Set V) →
        ∃ S, S ⊆ I ∧
             S.card ≤ Fintype.card V / (Δ + 1) ∧
             I ⊆ S ∪ f S ∧
             (G.induce (f S)).maxDegree < Δ := by
               refine ⟨ ?_, fun I hI => ?_ ⟩;
               focus
                 exact fun S => container_algorithm G Δ S Finset.univ;
               refine ⟨ get_S G Δ I, get_S_subset_I G Δ I, ?_, ?_, ?_ ⟩;
               · have := generate_S_and_A_size_bound G Δ I ∅ Finset.univ;
                 rw [ Nat.le_div_iff_mul_le ] <;> norm_num at * ; linarith!;
               · -- By definition of `get_S`, we know that `get_S G Δ I` is the first component of
                 -- the result of `generate_S_and_A G Δ I ∅ Finset.univ`.
                 have h_generate :
                     let res := generate_S_and_A G Δ I ∅ Finset.univ;
                       get_S G Δ I = res.1
                         ∧ container_algorithm G Δ (get_S G Δ I) Finset.univ = res.2 := by
                   exact
                     ⟨ rfl,
                       container_algorithm_eq_generate_A_correct G Δ I ∅ Finset.univ
                         ( by simp +decide ) ( by simp +decide ) ⟩;
                 have := generate_S_and_A_invariant G Δ I ∅ Finset.univ hI; aesop;
               · exact container_algorithm_max_degree G Δ hΔ (get_S G Δ I) univ

/-
For integers $M\ge 1$ and $1\le t\le M/2$,
\[
\sum_{i=0}^{t}\binom{M}{i}\le \left(\frac{eM}{t}\right)^t.
\]
-/
lemma binom_tail_bound (M : ℕ) (t : ℕ) (hM : M ≥ 1) (ht1 : 1 ≤ t) (ht2 : t ≤ M / 2) :
    (∑ i ∈ range (t + 1), (M.choose i : ℝ)) ≤ (Real.exp 1 * M / t) ^ t := by
      -- The RHS is bounded by $(M/t)^t \sum_{i=0}^M \binom{M}{i} (t/M)^i = (M/t)^t (1 + t/M)^M$.
      have h_rhs_bound : (∑ i ∈ Finset.range (t + 1), (M.choose i : ℝ)) ≤ (M / t :
          ℝ) ^ t * (1 + t / M) ^ M := by
        -- We have $\sum_{i=0}^t \binom{M}{i} \le (M/t)^t \sum_{i=0}^t \binom{M}{i} (t/M)^i$.
        have h_sum_bound : (∑ i ∈ Finset.range (t + 1), (M.choose i : ℝ))
          ≤ (M / t : ℝ) ^ t * (∑ i ∈ Finset.range (t + 1), (M.choose i :
            ℝ) * (t / M) ^ i) := by
          rw [ Finset.mul_sum _ _ _ ];
          -- For each term in the sum, we have $\left(\frac{M}{t}\right)^t
          -- \left(\frac{t}{M}\right)^i \geq 1$ because $t \leq M/2$.
          have h_term : ∀ i ∈ Finset.range (t + 1), (M / t : ℝ) ^ t * (t / M : ℝ) ^ i ≥ 1 := by
            -- Since $t \leq M/2$, we have $t/M \leq 1/2$. Therefore, $(t/M)^i \leq (t/M)^t$ for $i
            -- \leq t$.
            have h_term_bound : ∀ i ∈ Finset.range (t + 1), (t / M : ℝ) ^ i ≥ (t / M : ℝ) ^ t := by
              exact fun i hi =>
                pow_le_pow_of_le_one ( by positivity )
                  ( div_le_one_of_le₀
                    ( by
                      norm_cast
                      linarith [ Nat.div_mul_le_self M 2 ] )
                    ( by positivity ) )
                  ( by linarith [ Finset.mem_range.mp hi ] );
            exact fun i hi => le_trans ( by
              ring_nf;
              norm_num [ show M ≠ 0 by linarith, show t ≠ 0 by linarith ] ) (
                mul_le_mul_of_nonneg_left ( h_term_bound i hi ) ( by positivity ) ) ;
          exact Finset.sum_le_sum fun i hi =>
            by nlinarith only [ h_term i hi, show ( M.choose i : ℝ ) ≥ 0 by positivity ] ;
        refine le_trans h_sum_bound ?_;
        rw [ add_comm 1 _, add_pow ] ; norm_num [ mul_comm ];
        exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono
          ( by linarith [ Nat.div_mul_le_self M 2 ] ) ) fun _ _ _ =>
          mul_nonneg ( pow_nonneg ( by positivity ) _ ) ( Nat.cast_nonneg _ ) ) ( by positivity );
      -- Using $1+u \le e^u$, we have $(1+t/M)^M \le (e^{t/M})^M = e^t$.
      have h_exp_bound : (1 + t / M : ℝ) ^ M ≤ Real.exp t := by
        rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
        exact Real.exp_le_exp.mpr ( by
          nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + t / M : ℝ ) ),
            show ( t : ℝ ) / M ≥ 0 by positivity,
            mul_div_cancel₀ ( t : ℝ ) ( by positivity : ( M : ℝ ) ≠ 0 ) ] );
      calc
        (∑ i ∈ range (t + 1), (M.choose i : ℝ)) ≤ (M / t : ℝ) ^ t * Real.exp t :=
          h_rhs_bound.trans (mul_le_mul_of_nonneg_left h_exp_bound <| by positivity)
        _ = (Real.exp 1 * M / t) ^ t := by
          rw [mul_div_assoc, mul_pow, Real.exp_one_pow]
          ring


end Erdos748.GraphContainer
