/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Pairing bounded integer coefficients

A bounded integer population with large centered variance contains many
vertex-disjoint pairs of unequal coefficients.  The quantitative conclusion
is stated without division:

`eta * |S| ≤ 8 * B² * |M|`.

Every pair in `M` has coefficient difference between `1` and `2 * B`.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos636.Pairing

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The graph joining two indices in `S` exactly when their coefficients are
different. -/
def coefficientGraph (S : Finset I) (a : I → ℤ) : SimpleGraph I where
  Adj i j := i ∈ S ∧ j ∈ S ∧ a i ≠ a j
  symm := by
    constructor
    intro i j hij
    exact ⟨hij.2.1, hij.1, hij.2.2.symm⟩
  loopless := by
    constructor
    intro i hii
    exact hii.2.2 rfl

noncomputable instance coefficientGraph.instDecidableRel
    (S : Finset I) (a : I → ℤ) : DecidableRel (coefficientGraph S a).Adj :=
  Classical.decRel _

@[simp] lemma coefficientGraph_adj {S : Finset I} {a : I → ℤ} {i j : I} :
    (coefficientGraph S a).Adj i j ↔ i ∈ S ∧ j ∈ S ∧ a i ≠ a j :=
  Iff.rfl

/-- A finite set of pairwise vertex-disjoint edges. -/
def EdgeMatching (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I)) : Prop :=
  M ⊆ G.edgeFinset ∧
    (M : Set (Sym2 I)).Pairwise fun e f ↦ Disjoint (e : Set I) (f : Set I)

/-- A maximum-cardinality matching is inclusion-maximal. -/
private lemma exists_maximal_edgeMatching
    (G : SimpleGraph I) [DecidableRel G.Adj] :
    ∃ M : Finset (Sym2 I), EdgeMatching G M ∧
      ∀ e ∈ G.edgeFinset, e ∉ M →
        ∃ m ∈ M, ¬ Disjoint (e : Set I) (m : Set I) := by
  classical
  let good := G.edgeFinset.powerset.filter fun (M : Finset (Sym2 I)) ↦
    (M : Set (Sym2 I)).Pairwise fun e f ↦ Disjoint (e : Set I) (f : Set I)
  have hgood : good.Nonempty := ⟨∅, by simp [good]⟩
  obtain ⟨M, hMgood, hMmax⟩ := good.exists_max_image Finset.card hgood
  have hMsub : M ⊆ G.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMgood).1
  have hMpair : (M : Set (Sym2 I)).Pairwise
      (fun e f ↦ Disjoint (e : Set I) (f : Set I)) :=
    (Finset.mem_filter.mp hMgood).2
  refine ⟨M, ⟨hMsub, hMpair⟩, ?_⟩
  intro e heG heM
  by_contra hdisj
  push Not at hdisj
  have hpairInsert : ((insert e M : Finset (Sym2 I)) : Set (Sym2 I)).Pairwise
      (fun p q ↦ Disjoint (p : Set I) (q : Set I)) := by
    rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hMpair, ?_⟩
    intro m hm hem
    exact ⟨hdisj m hm, (hdisj m hm).symm⟩
  have hinsGood : insert e M ∈ good := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, hpairInsert⟩
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heG
    · exact hMsub hf
  have hle := hMmax (insert e M) hinsGood
  rw [Finset.card_insert_of_notMem heM] at hle
  omega

/-- The vertices incident with at least one edge of a finite matching. -/
def matchingVertices (M : Finset (Sym2 I)) : Finset I :=
  M.biUnion Sym2.toFinset

/-- The endpoint set of an inclusion-maximal matching covers every edge. -/
private lemma matchingVertices_cover_of_maximal
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I))
    (hmax : ∀ e ∈ G.edgeFinset, e ∉ M →
      ∃ m ∈ M, ¬ Disjoint (e : Set I) (m : Set I))
    {x y : I} (hxy : G.Adj x y) :
    x ∈ matchingVertices M ∨ y ∈ matchingVertices M := by
  have heG : s(x, y) ∈ G.edgeFinset := by simpa using hxy
  by_cases heM : s(x, y) ∈ M
  · left
    exact Finset.mem_biUnion.mpr ⟨s(x, y), heM, by simp⟩
  · obtain ⟨m, hmM, hem⟩ := hmax s(x, y) heG heM
    obtain ⟨z, hze, hzm⟩ := Set.not_disjoint_iff.mp hem
    have hz : z ∈ matchingVertices M :=
      Finset.mem_biUnion.mpr ⟨m, hmM, Sym2.mem_toFinset.mpr hzm⟩
    change z ∈ s(x, y) at hze
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz

/-- A matching has exactly two endpoints per edge. -/
private lemma card_matchingVertices_eq_two_mul
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I)) (hM : EdgeMatching G M) :
    (matchingVertices M).card = 2 * M.card := by
  have hpair : (M : Set (Sym2 I)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro x hxe hxf
    have hd := hM.2 he hf hef
    exact Set.disjoint_left.mp hd (Sym2.mem_toFinset.mp hxe)
      (Sym2.mem_toFinset.mp hxf)
  rw [matchingVertices, Finset.card_biUnion hpair]
  calc
    ∑ e ∈ M, e.toFinset.card = ∑ _e ∈ M, 2 := by
      apply Finset.sum_congr rfl
      intro e heM
      rw [Sym2.card_toFinset_of_not_isDiag e]
      exact G.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp (hM.1 heM))
    _ = 2 * M.card := by simp [Nat.mul_comm]

/-- A maximal matching in the unequal-coefficient graph leaves only one
coefficient value outside its endpoint set. -/
private lemma exists_matching_anchor
    (S : Finset I) (a : I → ℤ) (B : ℕ)
    (hbounded : ∀ i ∈ S, |a i| ≤ (B : ℤ)) :
    ∃ M : Finset (Sym2 I),
      EdgeMatching (coefficientGraph S a) M ∧
      (∀ {i j : I}, i ∈ S → j ∈ S →
        i ∉ matchingVertices M →
        j ∉ matchingVertices M → a i = a j) ∧
      ∃ c : ℤ, |c| ≤ (B : ℤ) ∧
        ∀ i ∈ S, i ∉ matchingVertices M → a i = c := by
  classical
  let H := coefficientGraph S a
  obtain ⟨M, hM, hmax⟩ := exists_maximal_edgeMatching H
  let C := matchingVertices M
  have hconstant : ∀ {i j : I}, i ∈ S → j ∈ S → i ∉ C → j ∉ C → a i = a j := by
    intro i j hi hj hiC hjC
    by_contra hij
    have hcover := matchingVertices_cover_of_maximal
      H M hmax (show H.Adj i j from ⟨hi, hj, hij⟩)
    exact hcover.elim hiC hjC
  refine ⟨M, hM, ?_, ?_⟩
  · intro i j hi hj hiM hjM
    exact hconstant hi hj (by simpa [C] using hiM) (by simpa [C] using hjM)
  · by_cases hU : ∃ i ∈ S, i ∉ C
    · obtain ⟨r, hrS, hrC⟩ := hU
      refine ⟨a r, hbounded r hrS, ?_⟩
      intro i hiS hiC
      exact hconstant hiS hrS (by simpa [C] using hiC) hrC
    · refine ⟨0, by simp, ?_⟩
      intro i hiS hiC
      exfalso
      exact hU ⟨i, hiS, by simpa [C] using hiC⟩

/-- A centered bounded integer population with variance at least `eta * |S|`
has a disjoint unequal-coefficient matching of linear size.  The centering
hypothesis permits any explicitly supplied population mean `mu`; avoiding a
division by `|S|` also makes the statement valid for the empty population.
-/
theorem exists_many_disjoint_coefficient_pairs
    (S : Finset I) (a : I → ℤ) (B : ℕ) (eta mu : ℝ)
    (hbounded : ∀ i ∈ S, |a i| ≤ (B : ℤ))
    (hcentered : ∑ i ∈ S, ((a i : ℝ) - mu) = 0)
    (hvariance : eta * (S.card : ℝ) ≤
      ∑ i ∈ S, ((a i : ℝ) - mu) ^ 2) :
    ∃ M : Finset (Sym2 I),
      EdgeMatching (coefficientGraph S a) M ∧
      (∀ e ∈ M, ∀ i ∈ (e : Set I), ∀ j ∈ (e : Set I), i ≠ j →
        (1 : ℤ) ≤ |a i - a j| ∧ |a i - a j| ≤ 2 * (B : ℤ)) ∧
      eta * (S.card : ℝ) ≤
        8 * (B : ℝ) ^ 2 * (M.card : ℝ) := by
  classical
  obtain ⟨M, hM, hunmatched, c, hcB, hc⟩ :=
    exists_matching_anchor S a B hbounded
  let C := matchingVertices M
  have hpairs : ∀ e ∈ M, ∀ i ∈ (e : Set I), ∀ j ∈ (e : Set I), i ≠ j →
      (1 : ℤ) ≤ |a i - a j| ∧ |a i - a j| ≤ 2 * (B : ℤ) := by
    intro e heM i hie j hje hij
    have heEdge : e ∈ (coefficientGraph S a).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp (hM.1 heM)
    have heq : e = s(i, j) :=
      (Sym2.mem_and_mem_iff hij).mp ⟨hie, hje⟩
    have hadj : (coefficientGraph S a).Adj i j := by
      rw [← (coefficientGraph S a).mem_edgeSet, ← heq]
      exact heEdge
    have hpos : 0 < |a i - a j| := abs_pos.mpr (sub_ne_zero.mpr hadj.2.2)
    refine ⟨by omega, ?_⟩
    calc
      |a i - a j| ≤ |a i| + |a j| := abs_sub (a i) (a j)
      _ ≤ (B : ℤ) + (B : ℤ) :=
        add_le_add (hbounded i hadj.1) (hbounded j hadj.2.1)
      _ = 2 * (B : ℤ) := by ring
  have hdeviation :
      (∑ i ∈ S, ((a i : ℝ) - mu) ^ 2) ≤
        ∑ i ∈ S, ((a i : ℝ) - (c : ℝ)) ^ 2 := by
    have hid :
        (∑ i ∈ S, ((a i : ℝ) - (c : ℝ)) ^ 2) =
          (∑ i ∈ S, ((a i : ℝ) - mu) ^ 2) +
            (S.card : ℝ) * (mu - (c : ℝ)) ^ 2 := by
      calc
        (∑ i ∈ S, ((a i : ℝ) - (c : ℝ)) ^ 2) =
            ∑ i ∈ S,
              (((a i : ℝ) - mu) ^ 2 +
                (2 * (mu - (c : ℝ)) * ((a i : ℝ) - mu) +
                  (mu - (c : ℝ)) ^ 2)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
        _ = (∑ i ∈ S, ((a i : ℝ) - mu) ^ 2) +
            (S.card : ℝ) * (mu - (c : ℝ)) ^ 2 := by
              rw [Finset.sum_add_distrib]
              congr 1
              rw [Finset.sum_add_distrib]
              have hcross :
                  (∑ i ∈ S,
                    2 * (mu - (c : ℝ)) * ((a i : ℝ) - mu)) = 0 := by
                rw [← Finset.mul_sum]
                simp [hcentered]
              rw [hcross, zero_add]
              simp [nsmul_eq_mul]
    rw [hid]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hterm : ∀ i ∈ S,
      ((a i : ℝ) - (c : ℝ)) ^ 2 ≤
        if i ∈ C then 4 * (B : ℝ) ^ 2 else 0 := by
    intro i hiS
    by_cases hiC : i ∈ C
    · rw [if_pos hiC]
      have hdiffZ : |a i - c| ≤ 2 * (B : ℤ) := by
        calc
          |a i - c| ≤ |a i| + |c| := abs_sub (a i) c
          _ ≤ (B : ℤ) + (B : ℤ) := add_le_add (hbounded i hiS) hcB
          _ = 2 * (B : ℤ) := by ring
      have hdiffR : |(a i : ℝ) - (c : ℝ)| ≤ 2 * (B : ℝ) := by
        exact_mod_cast hdiffZ
      rw [← sq_abs]
      have hBnonneg : (0 : ℝ) ≤ (B : ℝ) := by positivity
      nlinarith [abs_nonneg ((a i : ℝ) - (c : ℝ))]
    · rw [if_neg hiC, hc i hiS (by simpa [C] using hiC)]
      simp
  have hsumBound :
      (∑ i ∈ S, ((a i : ℝ) - (c : ℝ)) ^ 2) ≤
        (C.card : ℝ) * (4 * (B : ℝ) ^ 2) := by
    calc
      (∑ i ∈ S, ((a i : ℝ) - (c : ℝ)) ^ 2) ≤
          ∑ i ∈ S, if i ∈ C then 4 * (B : ℝ) ^ 2 else 0 := by
            exact Finset.sum_le_sum fun i hi ↦ hterm i hi
      _ = ((S.filter fun i ↦ i ∈ C).card : ℝ) * (4 * (B : ℝ) ^ 2) := by
            rw [← Finset.sum_filter]
            simp
      _ ≤ (C.card : ℝ) * (4 * (B : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast Finset.card_le_card (show
                S.filter (fun i ↦ i ∈ C) ⊆ C from fun i hi ↦
                  (Finset.mem_filter.mp hi).2)
            · positivity
  have hCcard : C.card = 2 * M.card := by
    simpa [C] using card_matchingVertices_eq_two_mul (coefficientGraph S a) M hM
  refine ⟨M, hM, hpairs, ?_⟩
  calc
    eta * (S.card : ℝ) ≤ ∑ i ∈ S, ((a i : ℝ) - mu) ^ 2 := hvariance
    _ ≤ ∑ i ∈ S, ((a i : ℝ) - (c : ℝ)) ^ 2 := hdeviation
    _ ≤ (C.card : ℝ) * (4 * (B : ℝ) ^ 2) := hsumBound
    _ = 8 * (B : ℝ) ^ 2 * (M.card : ℝ) := by
      rw [hCcard, Nat.cast_mul, Nat.cast_ofNat]
      ring

end

end Erdos636.Pairing
