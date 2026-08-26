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
import ErdosProblems.Erdos76.Fractional
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Tactic

/-!
# Fractional triangle decompositions of almost-complete graphs

This file develops the companion theorem used in the proof of Erdős 76.
Gruslys and Letzter prove that a graph on `n ≥ 7` vertices with at most
`n - 4` missing edges has a fractional triangle decomposition.  Their
induction proves the stronger statement `AlmostCompleteStrong` below.

The definitions use the triangle-load convention from `Fractional.lean`.
In particular, the uncovered weight is a sum over *present* graph edges.
The weighted definitions formalize Section 3 of the companion paper and use
capacity zero away from the graph.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The number of unordered pairs which are not edges of `G`. -/
def missingEdgeCount (G : SimpleGraph A) : ℕ :=
  Gᶜ.edgeFinset.card

/-- A fractional triangle packing which covers every present edge exactly
once. -/
def IsFractionalDecomposition (G : SimpleGraph A) (w : Finset A → ℝ) : Prop :=
  IsFractionalPacking G w ∧
    ∀ e ∈ G.edgeFinset, fractionalEdgeLoad G w e = 1

/-- The total weight of present edges left uncovered by a packing. -/
def fractionalUncoveredWeight (G : SimpleGraph A) (w : Finset A → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, (1 - fractionalEdgeLoad G w e)

/-- The bound on triangle weights used by the induction in the companion
paper. -/
def IsHalfBounded (G : SimpleGraph A) (w : Finset A → ℝ) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, w t ≤ 1 / 2

/-- The strong induction conclusion of Gruslys--Letzter, Theorem 2.1. -/
def HasStrongFractionalPacking (G : SimpleGraph A) (a : ℝ) : Prop :=
  ∃ w : Finset A → ℝ,
    IsFractionalPacking G w ∧ fractionalUncoveredWeight G w ≤ a ∧
      IsHalfBounded G w

/-- Exact finite formulation of Gruslys--Letzter, Theorem 2.1. -/
def AlmostCompleteStrong : Prop :=
  ∀ n a : ℕ, 11 ≤ n → a ≤ 4 → ∀ G : SimpleGraph (Fin n),
    missingEdgeCount G ≤ n - 4 + a → HasStrongFractionalPacking G a

/-- Exact finite formulation of the almost-complete decomposition theorem,
Gruslys--Letzter, Theorem 1.1. -/
def AlmostCompleteFractionalDecomposition : Prop :=
  ∀ n : ℕ, 7 ≤ n → ∀ G : SimpleGraph (Fin n),
    missingEdgeCount G ≤ n - 4 →
      ∃ w : Finset (Fin n) → ℝ, IsFractionalDecomposition G w

/-- The two finite certificate families in Gruslys--Letzter Lemma 2.2.
This proposition is the semantic target for `CertificateBridge`: the first
family supplies the strong induction bases at orders `11,12,13`; the second
supplies exact decompositions at orders `7,...,10`. -/
def AlmostCompleteCertificateBases : Prop :=
  (∀ n a : ℕ, 11 ≤ n → n ≤ 13 → a ≤ 4 →
    ∀ G : SimpleGraph (Fin n),
      missingEdgeCount G = n - 4 + a →
        HasStrongFractionalPacking G (a : ℝ)) ∧
  (∀ n : ℕ, 7 ≤ n → n ≤ 10 →
    ∀ G : SimpleGraph (Fin n),
      missingEdgeCount G = n - 4 →
        ∃ w : Finset (Fin n) → ℝ, IsFractionalDecomposition G w)

lemma IsFractionalDecomposition.isPacking {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalDecomposition G w) : IsFractionalPacking G w :=
  hw.1

lemma IsFractionalDecomposition.edgeLoad_eq_one
    {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalDecomposition G w) {e : Sym2 A} (he : e ∈ G.edgeFinset) :
    fractionalEdgeLoad G w e = 1 :=
  hw.2 e he

lemma fractionalUncoveredWeight_nonneg {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalPacking G w) : 0 ≤ fractionalUncoveredWeight G w := by
  apply sum_nonneg
  intro e he
  exact sub_nonneg.mpr (hw.edgeLoad_le_one he)

lemma fractionalUncoveredWeight_eq_zero
    {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalDecomposition G w) : fractionalUncoveredWeight G w = 0 := by
  unfold fractionalUncoveredWeight
  apply sum_eq_zero
  intro e he
  rw [hw.edgeLoad_eq_one he]
  norm_num

lemma isFractionalDecomposition_iff
    {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalPacking G w) :
    IsFractionalDecomposition G w ↔ fractionalUncoveredWeight G w = 0 := by
  constructor
  · exact fractionalUncoveredWeight_eq_zero
  · intro hzero
    refine ⟨hw, ?_⟩
    have hz : ∀ e ∈ G.edgeFinset, 1 - fractionalEdgeLoad G w e = 0 := by
      have hall := (sum_eq_zero_iff_of_nonneg fun e he ↦
        sub_nonneg.mpr (hw.edgeLoad_le_one he)).mp hzero
      exact fun e he ↦ hall e he
    intro e he
    linarith [hz e he]

/-! ## Weighted graphs (companion paper, Section 3) -/

/-- An edge capacity is supported on `G` and takes values in `[0,1]` on its
edges. -/
def IsEdgeCapacity (G : SimpleGraph A) (c : Sym2 A → ℝ) : Prop :=
  (∀ e ∈ G.edgeFinset, 0 ≤ c e ∧ c e ≤ 1) ∧
    ∀ e, e ∉ G.edgeFinset → c e = 0

/-- The missing weight of a weighted graph, with absent graph edges counted
at capacity zero. -/
def capacityMissingWeight (c : Sym2 A → ℝ) : ℝ :=
  ∑ e ∈ (⊤ : SimpleGraph A).edgeFinset, (1 - c e)

/-- A triangle weighting whose edge loads do not exceed the prescribed
capacities. -/
def IsCapacityPacking (G : SimpleGraph A) (c : Sym2 A → ℝ)
    (w : Finset A → ℝ) : Prop :=
  (∀ t ∈ G.cliqueFinset 3, 0 ≤ w t) ∧
    ∀ e ∈ G.edgeFinset, fractionalEdgeLoad G w e ≤ c e

/-- Uncovered present-edge capacity. -/
def capacityUncoveredWeight (G : SimpleGraph A) (c : Sym2 A → ℝ)
    (w : Finset A → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, (c e - fractionalEdgeLoad G w e)

/-- A weighted fractional decomposition realizes every capacity exactly. -/
def IsCapacityDecomposition (G : SimpleGraph A) (c : Sym2 A → ℝ)
    (w : Finset A → ℝ) : Prop :=
  IsCapacityPacking G c w ∧
    ∀ e ∈ G.edgeFinset, fractionalEdgeLoad G w e = c e

lemma IsEdgeCapacity.nonneg {G : SimpleGraph A} {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity G c) {e : Sym2 A} (he : e ∈ G.edgeFinset) : 0 ≤ c e :=
  (hc.1 e he).1

lemma IsEdgeCapacity.le_one {G : SimpleGraph A} {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity G c) {e : Sym2 A} (he : e ∈ G.edgeFinset) : c e ≤ 1 :=
  (hc.1 e he).2

lemma IsCapacityPacking.toFractionalPacking
    {G : SimpleGraph A} {c : Sym2 A → ℝ} {w : Finset A → ℝ}
    (hc : IsEdgeCapacity G c) (hw : IsCapacityPacking G c w) :
    IsFractionalPacking G w := by
  refine ⟨hw.1, ?_⟩
  intro e he
  exact (hw.2 e he).trans (hc.le_one he)

lemma capacityUncoveredWeight_nonneg
    {G : SimpleGraph A} {c : Sym2 A → ℝ} {w : Finset A → ℝ}
    (hw : IsCapacityPacking G c w) : 0 ≤ capacityUncoveredWeight G c w := by
  apply sum_nonneg
  intro e he
  exact sub_nonneg.mpr (hw.2 e he)

lemma capacityUncoveredWeight_eq_zero
    {G : SimpleGraph A} {c : Sym2 A → ℝ} {w : Finset A → ℝ}
    (hw : IsCapacityDecomposition G c w) : capacityUncoveredWeight G c w = 0 := by
  unfold capacityUncoveredWeight
  apply sum_eq_zero
  intro e he
  rw [hw.2 e he]
  norm_num

/-! ## Finite averaging identities

These are the algebraic part of the weighted reduction (Lemma 2.4).  The
remaining combinatorial part is Claim 3.1 of the paper: distribute rational
edge deficits among equally many simple graphs and average their packings.
-/

lemma fractionalEdgeLoad_smul (G : SimpleGraph A) (r : ℝ)
    (w : Finset A → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (fun t ↦ r * w t) e = r * fractionalEdgeLoad G w e := by
  simp [fractionalEdgeLoad, mul_sum]

lemma fractionalEdgeLoad_add (G : SimpleGraph A)
    (w₁ w₂ : Finset A → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (fun t ↦ w₁ t + w₂ t) e =
      fractionalEdgeLoad G w₁ e + fractionalEdgeLoad G w₂ e := by
  simp [fractionalEdgeLoad, sum_add_distrib]

lemma fractionalEdgeLoad_sum {I : Type*} [Fintype I]
    (G : SimpleGraph A) (w : I → Finset A → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (fun t ↦ ∑ i, w i t) e =
      ∑ i, fractionalEdgeLoad G (w i) e := by
  simp only [fractionalEdgeLoad]
  rw [sum_comm]

/-- Pointwise arithmetic mean of finitely many triangle weightings. -/
def averageTriangleWeight {I : Type*} [Fintype I]
    (w : I → Finset A → ℝ) : Finset A → ℝ :=
  fun t ↦ (Fintype.card I : ℝ)⁻¹ * ∑ i, w i t

lemma fractionalEdgeLoad_average {I : Type*} [Fintype I]
    (G : SimpleGraph A) (w : I → Finset A → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (averageTriangleWeight w) e =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, fractionalEdgeLoad G (w i) e := by
  change fractionalEdgeLoad G
      (fun t ↦ (Fintype.card I : ℝ)⁻¹ * ∑ i, w i t) e = _
  rw [fractionalEdgeLoad_smul, fractionalEdgeLoad_sum]

lemma averageTriangleWeight_nonneg {I : Type*} [Fintype I]
    {G : SimpleGraph A} {w : I → Finset A → ℝ}
    (hw : ∀ i t, t ∈ G.cliqueFinset 3 → 0 ≤ w i t) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ averageTriangleWeight w t := by
  intro t ht
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (sum_nonneg fun i _ ↦ hw i t ht)

lemma average_le_of_forall_le {I : Type*} [Fintype I] [Nonempty I]
    {f : I → ℝ} {b : ℝ} (hf : ∀ i, f i ≤ b) :
    (Fintype.card I : ℝ)⁻¹ * ∑ i, f i ≤ b := by
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc
    (Fintype.card I : ℝ)⁻¹ * ∑ i, f i
        ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _i : I, b := by
          gcongr with i
          exact hf i
    _ = b := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      field_simp

lemma averageTriangleWeight_le_half {I : Type*} [Fintype I] [Nonempty I]
    {G : SimpleGraph A} {w : I → Finset A → ℝ}
    (hw : ∀ i, IsHalfBounded G (w i)) : IsHalfBounded G (averageTriangleWeight w) := by
  intro t ht
  exact average_le_of_forall_le fun i ↦ hw i t ht

/-! ## The integral distribution lemma (Claim 3.1) -/

section DeficitDistribution

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Extend a prescribed finite set `h` inside `p` either up to size `m`, or
all the way to `p` if `p` itself is smaller.  This is the selection step in
the inductive proof of Claim 3.1. -/
lemma exists_intermediate_finset {h p : Finset I} {m : ℕ}
    (hhp : h ⊆ p) (hhm : h.card ≤ m) :
    ∃ s : Finset I,
      h ⊆ s ∧ s ⊆ p ∧ s.card ≤ m ∧ (s.card = m ∨ s = p) := by
  by_cases hpm : p.card ≤ m
  · exact ⟨p, hhp, Subset.rfl, hpm, Or.inr rfl⟩
  · have hmp : m < p.card := Nat.lt_of_not_ge hpm
    have htake : m - h.card ≤ (p \ h).card := by
      rw [card_sdiff_of_subset hhp]
      omega
    obtain ⟨t, htp, htcard⟩ := exists_subset_card_eq htake
    refine ⟨h ∪ t, subset_union_left, ?_, ?_, Or.inl ?_⟩
    · exact union_subset hhp (htp.trans sdiff_subset)
    · rw [card_union_of_disjoint]
      · omega
      · exact disjoint_of_subset_right htp Finset.disjoint_sdiff
    · rw [card_union_of_disjoint]
      · omega
      · exact disjoint_of_subset_right htp Finset.disjoint_sdiff

/-- The number of selected rows containing an index. -/
def rowMultiplicity {r : ℕ} (S : Fin r → Finset I) (i : I) : ℕ :=
  ∑ j, if i ∈ S j then 1 else 0

@[simp] lemma rowMultiplicity_zero (S : Fin 0 → Finset I) (i : I) :
    rowMultiplicity S i = 0 := by
  simp [rowMultiplicity]

@[simp] lemma rowMultiplicity_cons {r : ℕ} (s : Finset I)
    (S : Fin r → Finset I) (i : I) :
    rowMultiplicity (Fin.cases s S) i =
      (if i ∈ s then 1 else 0) + rowMultiplicity S i := by
  unfold rowMultiplicity
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rfl

/-- Indices carrying a positive deficit. -/
def positiveDeficitSupport (d : I → ℕ) : Finset I :=
  univ.filter fun i ↦ 0 < d i

/-- Indices whose deficit reaches the current number of rows. -/
def saturatedDeficitSupport (r : ℕ) (d : I → ℕ) : Finset I :=
  univ.filter fun i ↦ d i = r

/-- Decrease by one precisely on the selected positive deficits. -/
def decrementDeficit (s : Finset I) (d : I → ℕ) (i : I) : ℕ :=
  if i ∈ s then d i - 1 else d i

lemma saturatedDeficitSupport_subset_positive {r : ℕ} (hr : 0 < r) (d : I → ℕ) :
    saturatedDeficitSupport r d ⊆ positiveDeficitSupport d := by
  intro i hi
  have hid : d i = r := (mem_filter.mp hi).2
  exact mem_filter.mpr ⟨mem_univ _, hid.symm ▸ hr⟩

lemma decrementDeficit_add_indicator {s : Finset I} {d : I → ℕ}
    (hs : s ⊆ positiveDeficitSupport d) (i : I) :
    decrementDeficit s d i + (if i ∈ s then 1 else 0) = d i := by
  by_cases hi : i ∈ s
  · have hpos : 0 < d i := (mem_filter.mp (hs hi)).2
    simp [decrementDeficit, hi, Nat.sub_add_cancel hpos]
  · simp [decrementDeficit, hi]

lemma sum_decrementDeficit_add_card {s : Finset I} {d : I → ℕ}
    (hs : s ⊆ positiveDeficitSupport d) :
    (∑ i, decrementDeficit s d i) + s.card = ∑ i, d i := by
  have hindicator : (∑ i : I, if i ∈ s then 1 else 0) = s.card := by
    simp
  rw [← hindicator, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ decrementDeficit_add_indicator hs i

lemma decrementDeficit_le_pred {r : ℕ} {s : Finset I} {d : I → ℕ}
    (hdr : ∀ i, d i ≤ r + 1)
    (hsat : saturatedDeficitSupport (r + 1) d ⊆ s) (i : I) :
    decrementDeficit s d i ≤ r := by
  by_cases hi : i ∈ s
  · simp only [decrementDeficit, hi, if_true]
    have hiBound := hdr i
    omega
  · simp only [decrementDeficit, hi, if_false]
    have hiBound := hdr i
    have hne : d i ≠ r + 1 := by
      intro heq
      apply hi
      apply hsat
      exact mem_filter.mpr ⟨mem_univ _, heq⟩
    omega

lemma sum_decrementDeficit_le_of_card_eq {r m : ℕ} {s : Finset I} {d : I → ℕ}
    (hs : s ⊆ positiveDeficitSupport d) (hscard : s.card = m)
    (htotal : ∑ i, d i ≤ (r + 1) * m) :
    ∑ i, decrementDeficit s d i ≤ r * m := by
  have hid := sum_decrementDeficit_add_card hs
  rw [hscard] at hid
  rw [Nat.add_mul, one_mul] at htotal
  omega

lemma sum_decrementDeficit_le_of_all_positive {r m : ℕ} {d : I → ℕ}
    (hdr : ∀ i, d i ≤ r + 1) (hp : (positiveDeficitSupport d).card ≤ m) :
    ∑ i, decrementDeficit (positiveDeficitSupport d) d i ≤ r * m := by
  have hpoint : ∀ i, decrementDeficit (positiveDeficitSupport d) d i ≤
      if i ∈ positiveDeficitSupport d then r else 0 := by
    intro i
    by_cases hi : i ∈ positiveDeficitSupport d
    · simp only [hi, if_true, decrementDeficit]
      have hiBound := hdr i
      omega
    · have hz : d i = 0 := by
        have hnot : ¬ 0 < d i := by
          intro hpos
          exact hi (by simp [positiveDeficitSupport, hpos])
        have := not_lt.mp hnot
        omega
      simp [decrementDeficit, hi, hz]
  calc
    ∑ i, decrementDeficit (positiveDeficitSupport d) d i
        ≤ ∑ i, if i ∈ positiveDeficitSupport d then r else 0 :=
      sum_le_sum fun i _ ↦ hpoint i
    _ = (positiveDeficitSupport d).card * r := by simp
    _ ≤ m * r := Nat.mul_le_mul_right r hp
    _ = r * m := Nat.mul_comm _ _

lemma card_saturatedDeficitSupport_le {r m : ℕ} (hr : 0 < r) (d : I → ℕ)
    (htotal : ∑ i, d i ≤ r * m) :
    (saturatedDeficitSupport r d).card ≤ m := by
  have hprod : r * (saturatedDeficitSupport r d).card ≤ r * m := by
    calc
      r * (saturatedDeficitSupport r d).card
          = (saturatedDeficitSupport r d).card * r := Nat.mul_comm _ _
      _ = ∑ _i ∈ saturatedDeficitSupport r d, r := by simp
      _ = ∑ i ∈ saturatedDeficitSupport r d, d i := by
        apply sum_congr rfl
        intro i hi
        exact (mem_filter.mp hi).2.symm
      _ ≤ ∑ i, d i := by
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ Nat.zero_le _
      _ ≤ r * m := htotal
  exact Nat.le_of_mul_le_mul_left hprod hr

/-- Claim 3.1 of Gruslys--Letzter.  Integer deficits of individual size at
most `r` and total size at most `r * m` can be distributed among `r` sets,
each of cardinality at most `m`, with no index repeated within a set. -/
theorem exists_deficit_distribution (r m : ℕ) (d : I → ℕ)
    (hrange : ∀ i, d i ≤ r) (htotal : ∑ i, d i ≤ r * m) :
    ∃ S : Fin r → Finset I,
      (∀ j, (S j).card ≤ m) ∧ ∀ i, rowMultiplicity S i = d i := by
  induction r generalizing d with
  | zero =>
      have hd : ∀ i, d i = 0 := fun i ↦ Nat.eq_zero_of_le_zero (hrange i)
      refine ⟨fun j ↦ Fin.elim0 j, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · intro i
        simp [hd i]
  | succ r ih =>
      let h := saturatedDeficitSupport (r + 1) d
      let p := positiveDeficitSupport d
      have hhp : h ⊆ p := by
        simpa [h, p] using
          (saturatedDeficitSupport_subset_positive (I := I) (Nat.succ_pos r) d)
      have hhm : h.card ≤ m := by
        simpa [h] using
          (card_saturatedDeficitSupport_le (I := I) (Nat.succ_pos r) d htotal)
      obtain ⟨s, hhs, hsp, hsle, hscard | hsp_eq⟩ :=
        exists_intermediate_finset (I := I) hhp hhm
      · let d' := decrementDeficit s d
        have hd'range : ∀ i, d' i ≤ r := by
          intro i
          simpa [d', h] using
            (decrementDeficit_le_pred (I := I) hrange hhs i)
        have hd'total : ∑ i, d' i ≤ r * m := by
          simpa [d'] using
            (sum_decrementDeficit_le_of_card_eq (I := I)
              (by simpa [p] using hsp) hscard htotal)
        obtain ⟨S, hSCard, hSMult⟩ := ih d' hd'range hd'total
        refine ⟨Fin.cases s S, ?_, ?_⟩
        · intro j
          exact Fin.cases hsle (fun j ↦ hSCard j) j
        · intro i
          rw [rowMultiplicity_cons, hSMult i]
          simpa [d', Nat.add_comm] using
            (decrementDeficit_add_indicator (I := I) (by simpa [p] using hsp) i)
      · subst s
        let d' := decrementDeficit p d
        have hd'range : ∀ i, d' i ≤ r := by
          intro i
          simpa [d', h] using
            (decrementDeficit_le_pred (I := I) hrange hhs i)
        have hd'total : ∑ i, d' i ≤ r * m := by
          simpa [d', p] using
            (sum_decrementDeficit_le_of_all_positive (I := I) hrange hsle)
        obtain ⟨S, hSCard, hSMult⟩ := ih d' hd'range hd'total
        refine ⟨Fin.cases p S, ?_, ?_⟩
        · intro j
          exact Fin.cases hsle (fun j ↦ hSCard j) j
        · intro i
          rw [rowMultiplicity_cons, hSMult i]
          simpa [d', p, Nat.add_comm] using
            (decrementDeficit_add_indicator (I := I) (subset_refl _) i)

end DeficitDistribution

/-! ## Zero-extension and averaging across subgraphs

The simple graphs supplied by Claim 3.1 have different triangle sets.  Their
packings are therefore extended by zero before they are averaged.
-/

/-- Extend a triangle weighting from `H` by zero to all vertex triples. -/
def zeroExtendTriangleWeight (H : SimpleGraph A) (w : Finset A → ℝ) : Finset A → ℝ :=
  fun t ↦ if t ∈ H.cliqueFinset 3 then w t else 0

lemma zeroExtendTriangleWeight_of_mem {H : SimpleGraph A} {w : Finset A → ℝ}
    {t : Finset A} (ht : t ∈ H.cliqueFinset 3) : zeroExtendTriangleWeight H w t = w t := by
  simp [zeroExtendTriangleWeight, ht]

lemma zeroExtendTriangleWeight_of_not_mem {H : SimpleGraph A} {w : Finset A → ℝ}
    {t : Finset A} (ht : t ∉ H.cliqueFinset 3) : zeroExtendTriangleWeight H w t = 0 := by
  simp [zeroExtendTriangleWeight, ht]

lemma fractionalEdgeLoad_zeroExtend {H G : SimpleGraph A} (hHG : H ≤ G)
    (w : Finset A → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (zeroExtendTriangleWeight H w) e =
      fractionalEdgeLoad H w e := by
  let sH := (H.cliqueFinset 3).filter fun t ↦ e ∈ t.sym2
  let sG := (G.cliqueFinset 3).filter fun t ↦ e ∈ t.sym2
  have hsub : sH ⊆ sG := by
    intro t ht
    have ht' := mem_filter.mp ht
    exact mem_filter.mpr ⟨SimpleGraph.cliqueFinset_mono G hHG ht'.1, ht'.2⟩
  unfold fractionalEdgeLoad
  change (∑ t ∈ sG, zeroExtendTriangleWeight H w t) = ∑ t ∈ sH, w t
  calc
    (∑ t ∈ sG, zeroExtendTriangleWeight H w t) =
        ∑ t ∈ sH, zeroExtendTriangleWeight H w t := by
      symm
      apply sum_subset hsub
      intro t htG htH
      exact zeroExtendTriangleWeight_of_not_mem (fun ht ↦ htH (mem_filter.mpr
        ⟨ht, (mem_filter.mp htG).2⟩))
    _ = ∑ t ∈ sH, w t := by
      apply sum_congr rfl
      intro t ht
      exact zeroExtendTriangleWeight_of_mem (mem_filter.mp ht).1

lemma fractionalEdgeLoad_eq_zero_of_not_edge (H : SimpleGraph A)
    (w : Finset A → ℝ) {e : Sym2 A} (heND : ¬ e.IsDiag)
    (heH : e ∉ H.edgeFinset) : fractionalEdgeLoad H w e = 0 := by
  unfold fractionalEdgeLoad
  apply sum_eq_zero
  intro t ht
  have htData := mem_filter.mp ht
  exfalso
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa using heND
      have hmem := Finset.mk_mem_sym2_iff.mp htData.2
      have hadj : H.Adj x y :=
        (SimpleGraph.mem_cliqueFinset_iff.mp htData.1).isClique hmem.1 hmem.2 hxy
      exact heH (by simpa using hadj)

lemma zeroExtendTriangleWeight_nonneg {H G : SimpleGraph A} (hHG : H ≤ G)
    {w : Finset A → ℝ} (hw : IsFractionalPacking H w) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ zeroExtendTriangleWeight H w t := by
  intro t htG
  by_cases htH : t ∈ H.cliqueFinset 3
  · simpa [zeroExtendTriangleWeight, htH] using hw.nonneg_on htH
  · simp [zeroExtendTriangleWeight, htH]

lemma zeroExtendTriangleWeight_le_half {H G : SimpleGraph A} (hHG : H ≤ G)
    {w : Finset A → ℝ} (hw : IsHalfBounded H w) :
    IsHalfBounded G (zeroExtendTriangleWeight H w) := by
  intro t htG
  by_cases htH : t ∈ H.cliqueFinset 3
  · simpa [zeroExtendTriangleWeight, htH] using hw t htH
  · simp [zeroExtendTriangleWeight, htH]

section SubgraphAverage

variable {I : Type*} [Fintype I] [Nonempty I]

/-- Average of the `0`-`1` capacities of a finite family of subgraphs. -/
def averageGraphCapacity (H : I → SimpleGraph A) : Sym2 A → ℝ :=
  fun e ↦ (Fintype.card I : ℝ)⁻¹ * ∑ i, if e ∈ (H i).edgeFinset then 1 else 0

/-- Average after extending every subgraph packing by zero. -/
def averageSubgraphPacking (H : I → SimpleGraph A)
    (w : I → Finset A → ℝ) : Finset A → ℝ :=
  averageTriangleWeight fun i ↦ zeroExtendTriangleWeight (H i) (w i)

lemma averageGraphCapacity_isEdgeCapacity (H : I → SimpleGraph A) :
    IsEdgeCapacity (⊤ : SimpleGraph A) (averageGraphCapacity H) := by
  constructor
  · intro e he
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (sum_nonneg fun i _ ↦ by positivity)
    · exact average_le_of_forall_le fun i ↦ by
        split_ifs <;> norm_num
  · intro e he
    have heDiag : e.IsDiag := by
      contrapose! he
      simpa using he
    have heNo : ∀ i, e ∉ (H i).edgeFinset := fun i hi ↦
      (SimpleGraph.not_isDiag_of_mem_edgeFinset hi) heDiag
    simp [averageGraphCapacity, heNo]

lemma averageSubgraphPacking_isCapacityPacking
    (H : I → SimpleGraph A) (w : I → Finset A → ℝ)
    (hw : ∀ i, IsFractionalPacking (H i) (w i)) :
    IsCapacityPacking (⊤ : SimpleGraph A) (averageGraphCapacity H)
      (averageSubgraphPacking H w) := by
  constructor
  · apply averageTriangleWeight_nonneg
    intro i
    exact zeroExtendTriangleWeight_nonneg le_top (hw i)
  · intro e he
    rw [averageSubgraphPacking, fractionalEdgeLoad_average]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    gcongr with i
    rw [fractionalEdgeLoad_zeroExtend le_top]
    by_cases hei : e ∈ (H i).edgeFinset
    · simpa [hei] using (hw i).edgeLoad_le_one hei
    · have heND : ¬ e.IsDiag :=
        @SimpleGraph.not_isDiag_of_mem_edgeFinset A (⊤ : SimpleGraph A) e
          (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
            (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) he
      have hz : fractionalEdgeLoad (H i) (w i) e = 0 :=
        fractionalEdgeLoad_eq_zero_of_not_edge (H i) (w i)
          heND hei
      simp [hei, hz]

lemma averageSubgraphPacking_isCapacityDecomposition
    (H : I → SimpleGraph A) (w : I → Finset A → ℝ)
    (hw : ∀ i, IsFractionalDecomposition (H i) (w i)) :
    IsCapacityDecomposition (⊤ : SimpleGraph A) (averageGraphCapacity H)
      (averageSubgraphPacking H w) := by
  refine ⟨averageSubgraphPacking_isCapacityPacking H w
    (fun i ↦ (hw i).isPacking), ?_⟩
  intro e he
  rw [averageSubgraphPacking, fractionalEdgeLoad_average, averageGraphCapacity]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [fractionalEdgeLoad_zeroExtend le_top]
  by_cases hei : e ∈ (H i).edgeFinset
  · rw [(hw i).edgeLoad_eq_one hei, if_pos hei]
  · have heND : ¬ e.IsDiag :=
      @SimpleGraph.not_isDiag_of_mem_edgeFinset A (⊤ : SimpleGraph A) e
        (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
          (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) he
    rw [fractionalEdgeLoad_eq_zero_of_not_edge (H i) (w i) heND hei,
      if_neg hei]

lemma averageSubgraphPacking_halfBounded
    (H : I → SimpleGraph A) (w : I → Finset A → ℝ)
    (hw : ∀ i, IsHalfBounded (H i) (w i)) :
    IsHalfBounded (⊤ : SimpleGraph A) (averageSubgraphPacking H w) := by
  apply averageTriangleWeight_le_half
  intro i
  exact zeroExtendTriangleWeight_le_half le_top (hw i)

/-- Extending a packing of `H` by zero, and viewing the indicator of `H` as
an edge capacity on the complete graph, does not change its total uncovered
weight. -/
lemma capacityUncoveredWeight_indicator_zeroExtend
    (H : SimpleGraph A) (w : Finset A → ℝ) :
    capacityUncoveredWeight (⊤ : SimpleGraph A)
        (fun e ↦ if e ∈ H.edgeFinset then 1 else 0)
        (zeroExtendTriangleWeight H w) =
      fractionalUncoveredWeight H w := by
  unfold capacityUncoveredWeight fractionalUncoveredWeight
  simp_rw [fractionalEdgeLoad_zeroExtend le_top]
  have hsub : H.edgeFinset ⊆
      @SimpleGraph.edgeFinset A (⊤ : SimpleGraph A)
        (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
          (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) := by
    intro e he
    have heND : ¬ e.IsDiag := H.not_isDiag_of_mem_edgeFinset he
    induction e using Sym2.inductionOn with
    | hf x y => simpa [SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using heND
  calc
    (∑ e ∈ @SimpleGraph.edgeFinset A (⊤ : SimpleGraph A)
        (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
          (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))),
        ((if e ∈ H.edgeFinset then 1 else 0) - fractionalEdgeLoad H w e)) =
        ∑ e ∈ H.edgeFinset,
          ((if e ∈ H.edgeFinset then 1 else 0) - fractionalEdgeLoad H w e) := by
      symm
      apply sum_subset hsub
      intro e heTop heH
      have heND : ¬ e.IsDiag :=
        @SimpleGraph.not_isDiag_of_mem_edgeFinset A (⊤ : SimpleGraph A) e
          (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
            (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) heTop
      rw [if_neg heH, fractionalEdgeLoad_eq_zero_of_not_edge H w heND heH]
      norm_num
    _ = ∑ e ∈ H.edgeFinset, (1 - fractionalEdgeLoad H w e) := by
      apply sum_congr rfl
      intro e he
      simp [he]

/-- Both edge capacities and triangle loads commute with the finite average;
consequently, so does the total uncovered weight. -/
lemma capacityUncoveredWeight_averageSubgraphPacking
    (H : I → SimpleGraph A) (w : I → Finset A → ℝ) :
    capacityUncoveredWeight (⊤ : SimpleGraph A) (averageGraphCapacity H)
        (averageSubgraphPacking H w) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, fractionalUncoveredWeight (H i) (w i) := by
  unfold capacityUncoveredWeight averageGraphCapacity averageSubgraphPacking
  simp_rw [fractionalEdgeLoad_average]
  simp_rw [← mul_sub, ← sum_sub_distrib]
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simpa only [capacityUncoveredWeight] using
    (capacityUncoveredWeight_indicator_zeroExtend (H i) (w i))

end SubgraphAverage

/-! ## Turning deficit rows into unweighted graphs -/

/-- An unordered pair of distinct vertices, represented independently of any
particular decidability instance for `SimpleGraph.edgeFinset`. -/
abbrev CompleteEdge (A : Type*) := {e : Sym2 A // ¬ e.IsDiag}

/-- Forget the non-diagonal witness on every edge in a row. -/
def deficitRowEdges (s : Finset (CompleteEdge A)) : Finset (Sym2 A) :=
  s.map ⟨Subtype.val, Subtype.val_injective⟩

/-- The spanning graph whose non-edges are exactly the entries of `s`. -/
def graphOfDeficitRow (s : Finset (CompleteEdge A)) : SimpleGraph A :=
  (⊤ : SimpleGraph A).deleteEdges (deficitRowEdges s)

@[simp] lemma mem_deficitRowEdges {s : Finset (CompleteEdge A)} {e : CompleteEdge A} :
    (e : Sym2 A) ∈ deficitRowEdges s ↔ e ∈ s := by
  simp [deficitRowEdges]

@[simp] lemma mem_graphOfDeficitRow_edgeSet
    {s : Finset (CompleteEdge A)} {e : CompleteEdge A} :
    (e : Sym2 A) ∈ (graphOfDeficitRow s).edgeSet ↔ e ∉ s := by
  rw [graphOfDeficitRow, SimpleGraph.edgeSet_deleteEdges]
  simp [e.property]

lemma missingEdgeCount_graphOfDeficitRow (s : Finset (CompleteEdge A)) :
    missingEdgeCount (graphOfDeficitRow s) = s.card := by
  unfold missingEdgeCount
  have hedge : (graphOfDeficitRow s)ᶜ.edgeFinset = deficitRowEdges s := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
        by_cases hxy : x = y
        · subst y
          simp [deficitRowEdges]
        · let e' : CompleteEdge A := ⟨s(x, y), by simpa using hxy⟩
          have hrow : s(x, y) ∈ deficitRowEdges s ↔ e' ∈ s := by
            simpa [e'] using (mem_deficitRowEdges (s := s) (e := e'))
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          change (x ≠ y ∧ ¬ (graphOfDeficitRow s).Adj x y) ↔ _
          rw [hrow]
          simpa [hxy, e', SimpleGraph.mem_edgeSet] using
            (not_congr (mem_graphOfDeficitRow_edgeSet (s := s) (e := e')))
  rw [hedge, deficitRowEdges, card_map]

lemma absentRowMultiplicity_add {r : ℕ} (S : Fin r → Finset (CompleteEdge A))
    (e : CompleteEdge A) :
    (∑ j, if e ∉ S j then 1 else 0) + rowMultiplicity S e = r := by
  rw [rowMultiplicity, ← sum_add_distrib]
  calc
    ∑ j, ((if e ∉ S j then 1 else 0) + if e ∈ S j then 1 else 0) =
        ∑ _j : Fin r, 1 := by
      apply sum_congr rfl
      intro j hj
      by_cases he : e ∈ S j <;> simp [he]
    _ = r := by simp

/-- Claim 3.1 realizes an integral deficit vector as the pointwise average
of the indicator functions of its row graphs. -/
lemma averageGraphCapacity_deficitRows_eq {r : ℕ} (hr : 0 < r)
    (d : CompleteEdge A → ℕ) (S : Fin r → Finset (CompleteEdge A))
    (hmult : ∀ e, rowMultiplicity S e = d e) (c : Sym2 A → ℝ)
    (hcDiag : ∀ e : Sym2 A, e.IsDiag → c e = 0)
    (hcDeficit : ∀ e : CompleteEdge A,
      c e = 1 - (d e : ℝ) / (r : ℝ)) :
    averageGraphCapacity (fun j ↦ graphOfDeficitRow (S j)) = c := by
  funext e
  induction e using Sym2.inductionOn with
  | hf x y =>
      by_cases hxy : x = y
      · subst y
        rw [hcDiag s(x, x) (by simp)]
        simp [averageGraphCapacity]
      · let e' : CompleteEdge A := ⟨s(x, y), by simpa using hxy⟩
        have hedge : ∀ j,
            s(x, y) ∈ (graphOfDeficitRow (S j)).edgeFinset ↔ e' ∉ S j := by
          intro j
          rw [SimpleGraph.mem_edgeFinset]
          simpa [e'] using
            (mem_graphOfDeficitRow_edgeSet (s := S j) (e := e'))
        have hcountNat : (∑ j, if e' ∉ S j then 1 else 0) = r - d e' := by
          have hadd := absentRowMultiplicity_add S e'
          rw [hmult e'] at hadd
          omega
        have hdle : d e' ≤ r := by
          have hadd := absentRowMultiplicity_add S e'
          rw [hmult e'] at hadd
          omega
        have hcountReal : (∑ j, if e' ∉ S j then (1 : ℝ) else 0) =
            (r : ℝ) - (d e' : ℝ) := by
          calc
            (∑ j, if e' ∉ S j then (1 : ℝ) else 0) =
                ((∑ j, if e' ∉ S j then (1 : ℕ) else 0) : ℝ) := by
              apply sum_congr rfl
              intro j hj
              by_cases he : e' ∈ S j <;> simp [he]
            _ = ((r - d e' : ℕ) : ℝ) := by exact_mod_cast hcountNat
            _ = (r : ℝ) - (d e' : ℝ) := by rw [Nat.cast_sub hdle]
        rw [averageGraphCapacity]
        simp_rw [hedge]
        rw [hcountReal, hcDeficit e']
        have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
        simp only [Fintype.card_fin]
        field_simp

/-! ## The rational weighted reduction (Lemma 2.4, finite core) -/

lemma capacityMissingWeight_eq_sum_completeEdges (c : Sym2 A → ℝ) :
    capacityMissingWeight c = ∑ e : CompleteEdge A, (1 - c e) := by
  unfold capacityMissingWeight
  apply Finset.sum_subtype
  intro e
  induction e using Sym2.inductionOn with
  | hf x y => simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

lemma integralDeficits_total_le {r m : ℕ} (hr : 0 < r)
    (c : Sym2 A → ℝ) (d : CompleteEdge A → ℕ)
    (hcDeficit : ∀ e : CompleteEdge A,
      c e = 1 - (d e : ℝ) / (r : ℝ))
    (hmissing : capacityMissingWeight c ≤ (m : ℝ)) :
    ∑ e, d e ≤ r * m := by
  have hsum : capacityMissingWeight c =
      (∑ e, (d e : ℝ)) / (r : ℝ) := by
    rw [capacityMissingWeight_eq_sum_completeEdges]
    simp_rw [hcDeficit]
    simp only [sub_sub_cancel]
    rw [sum_div]
  rw [hsum] at hmissing
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hreal : (∑ e, (d e : ℝ)) ≤ (r : ℝ) * (m : ℝ) :=
    by simpa [mul_comm] using (div_le_iff₀ hrReal).mp hmissing
  exact_mod_cast hreal

lemma IsEdgeCapacity.eq_zero_of_isDiag {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) {e : Sym2 A}
    (heDiag : e.IsDiag) : c e = 0 := by
  apply hc.2 e
  intro he
  have heND : ¬ e.IsDiag :=
    @SimpleGraph.not_isDiag_of_mem_edgeFinset A (⊤ : SimpleGraph A) e
      (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
        (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) he
  exact heND heDiag

/-- If every row graph has the required strong packing, averaging those
packings proves the corresponding weighted statement.  This isolates the
analytic-free final step of Lemma 2.4 from Claim 3.1's construction of the
rows. -/
theorem weightedReduction_of_deficitRows {r m : ℕ} (hr : 0 < r)
    (S : Fin r → Finset (CompleteEdge A))
    (hcard : ∀ j, (S j).card ≤ m) (c : Sym2 A → ℝ)
    (hcapacity : averageGraphCapacity (fun j ↦ graphOfDeficitRow (S j)) = c)
    (a : ℝ)
    (hgraphs : ∀ H : SimpleGraph A, missingEdgeCount H ≤ m →
      HasStrongFractionalPacking H a) :
    ∃ w : Finset A → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph A) c w ∧
        capacityUncoveredWeight (⊤ : SimpleGraph A) c w ≤ a ∧
          IsHalfBounded (⊤ : SimpleGraph A) w := by
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let H : Fin r → SimpleGraph A := fun j ↦ graphOfDeficitRow (S j)
  have hex : ∀ j, ∃ w : Finset A → ℝ,
      IsFractionalPacking (H j) w ∧ fractionalUncoveredWeight (H j) w ≤ a ∧
        IsHalfBounded (H j) w := by
    intro j
    exact hgraphs (H j) (by simpa [H, missingEdgeCount_graphOfDeficitRow] using hcard j)
  choose w hwPacking hwUncovered hwHalf using hex
  refine ⟨averageSubgraphPacking H w, ?_, ?_, ?_⟩
  · rw [← hcapacity]
    exact averageSubgraphPacking_isCapacityPacking H w hwPacking
  · rw [← hcapacity, capacityUncoveredWeight_averageSubgraphPacking]
    exact average_le_of_forall_le hwUncovered
  · exact averageSubgraphPacking_halfBounded H w hwHalf

/-- Exact analogue of the row-averaging step: decompositions of all row
graphs average to a decomposition of their mean capacity. -/
theorem weightedDecomposition_of_deficitRows {r m : ℕ} (hr : 0 < r)
    (S : Fin r → Finset (CompleteEdge A))
    (hcard : ∀ j, (S j).card ≤ m) (c : Sym2 A → ℝ)
    (hcapacity : averageGraphCapacity (fun j ↦ graphOfDeficitRow (S j)) = c)
    (hgraphs : ∀ H : SimpleGraph A, missingEdgeCount H ≤ m →
      ∃ w : Finset A → ℝ, IsFractionalDecomposition H w) :
    ∃ w : Finset A → ℝ,
      IsCapacityDecomposition (⊤ : SimpleGraph A) c w := by
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let H : Fin r → SimpleGraph A := fun j ↦ graphOfDeficitRow (S j)
  have hex : ∀ j, ∃ w : Finset A → ℝ, IsFractionalDecomposition (H j) w := by
    intro j
    exact hgraphs (H j) (by simpa [H, missingEdgeCount_graphOfDeficitRow] using hcard j)
  choose w hw using hex
  refine ⟨averageSubgraphPacking H w, ?_⟩
  rw [← hcapacity]
  exact averageSubgraphPacking_isCapacityDecomposition H w hw

/-- The rational part of Gruslys--Letzter Lemma 2.4, stated with its common
denominator and integral deficit vector exposed.  `Claim 3.1` supplies the
row graphs, and `weightedReduction_of_deficitRows` averages their packings. -/
theorem rationalWeightedReduction_of_integralDeficits {r m : ℕ} (hr : 0 < r)
    (c : Sym2 A → ℝ) (d : CompleteEdge A → ℕ)
    (hrange : ∀ e, d e ≤ r) (htotal : ∑ e, d e ≤ r * m)
    (hcDiag : ∀ e : Sym2 A, e.IsDiag → c e = 0)
    (hcDeficit : ∀ e : CompleteEdge A,
      c e = 1 - (d e : ℝ) / (r : ℝ))
    (a : ℝ)
    (hgraphs : ∀ H : SimpleGraph A, missingEdgeCount H ≤ m →
      HasStrongFractionalPacking H a) :
    ∃ w : Finset A → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph A) c w ∧
        capacityUncoveredWeight (⊤ : SimpleGraph A) c w ≤ a ∧
          IsHalfBounded (⊤ : SimpleGraph A) w := by
  obtain ⟨S, hcard, hmult⟩ := exists_deficit_distribution r m d hrange htotal
  apply weightedReduction_of_deficitRows hr S hcard c
  · exact averageGraphCapacity_deficitRows_eq hr d S hmult c hcDiag hcDeficit
  · exact hgraphs

/-- Gruslys--Letzter Lemma 2.4 for a capacity with a displayed common
denominator.  The missing-weight hypothesis now supplies Claim 3.1's total
integral-deficit bound rather than requiring it as separate input. -/
theorem rationalWeightedReduction {r m : ℕ} (hr : 0 < r)
    (c : Sym2 A → ℝ) (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c)
    (d : CompleteEdge A → ℕ) (hrange : ∀ e, d e ≤ r)
    (hcDeficit : ∀ e : CompleteEdge A,
      c e = 1 - (d e : ℝ) / (r : ℝ))
    (hmissing : capacityMissingWeight c ≤ (m : ℝ))
    (a : ℝ)
    (hgraphs : ∀ H : SimpleGraph A, missingEdgeCount H ≤ m →
      HasStrongFractionalPacking H a) :
    ∃ w : Finset A → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph A) c w ∧
        capacityUncoveredWeight (⊤ : SimpleGraph A) c w ≤ a ∧
          IsHalfBounded (⊤ : SimpleGraph A) w := by
  apply rationalWeightedReduction_of_integralDeficits hr c d hrange
      (integralDeficits_total_le hr c d hcDeficit hmissing)
      (fun e he ↦ hc.eq_zero_of_isDiag he) hcDeficit a hgraphs

/-! ## The triangle correction in Lemma 2.3 -/

/-- Put weight `q` on one specified triangle and zero elsewhere. -/
def singleTriangleWeight (t : Finset A) (q : ℝ) : Finset A → ℝ :=
  fun u ↦ if u = t then q else 0

lemma fractionalEdgeLoad_singleTriangle {G : SimpleGraph A} {t : Finset A}
    (ht : t ∈ G.cliqueFinset 3) (q : ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (singleTriangleWeight t q) e =
      if e ∈ t.sym2 then q else 0 := by
  unfold fractionalEdgeLoad singleTriangleWeight
  by_cases he : e ∈ t.sym2
  · have htFilter : t ∈ (G.cliqueFinset 3).filter fun u ↦ e ∈ u.sym2 :=
      mem_filter.mpr ⟨ht, he⟩
    rw [if_pos he]
    simpa using (Finset.sum_eq_single
      (s := (G.cliqueFinset 3).filter fun u ↦ e ∈ u.sym2)
      (f := fun u ↦ if u = t then q else 0) t
      (fun u hu hut ↦ if_neg hut)
      (fun htNot ↦ (htNot htFilter).elim))
  · rw [if_neg he]
    apply sum_eq_zero
    intro u hu
    rw [if_neg]
    intro hut
    subst u
    exact he (mem_filter.mp hu).2

/-- Add the final weight on the distinguished triangle in the induction step
of Lemma 2.3.  The hypothesis `hfill` records that the capacity decomposition
already covers every other edge fully and covers the three triangle edges to
within `q`. -/
lemma isFractionalDecomposition_add_singleTriangle
    {G : SimpleGraph A} {c : Sym2 A → ℝ} {w : Finset A → ℝ}
    {t : Finset A} (ht : t ∈ G.cliqueFinset 3) {q : ℝ} (hq : 0 ≤ q)
    (hw : IsCapacityDecomposition G c w)
    (hfill : ∀ e ∈ G.edgeFinset,
      c e + (if e ∈ t.sym2 then q else 0) = 1) :
    IsFractionalDecomposition G
      (fun u ↦ w u + singleTriangleWeight t q u) := by
  have hload : ∀ e ∈ G.edgeFinset,
      fractionalEdgeLoad G (fun u ↦ w u + singleTriangleWeight t q u) e = 1 := by
    intro e he
    rw [fractionalEdgeLoad_add, hw.2 e he,
      fractionalEdgeLoad_singleTriangle ht]
    exact hfill e he
  constructor
  · constructor
    · intro u hu
      exact add_nonneg (hw.1.1 u hu) (by
        by_cases hut : u = t <;> simp [singleTriangleWeight, hut, hq])
    · intro e he
      rw [hload e he]
  · exact hload

end

end Erdos76
