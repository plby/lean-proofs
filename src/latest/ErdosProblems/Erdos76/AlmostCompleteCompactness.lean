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
import ErdosProblems.Erdos76.AlmostComplete
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-!
# Compactness in the weighted reduction

This file proves the irrational-capacity part of Gruslys--Letzter Lemma 2.4.
The rational part and its finite deficit distribution are in
`AlmostComplete.lean`.  We approximate every capacity from above by a
rational capacity with a common denominator, apply that theorem, and take a
convergent subsequence in the finite cube of triangle weights.
-/

open Finset Filter Set
open scoped BigOperators Topology

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The upper rational approximation to an edge capacity, with denominator
`k + 1`.  Diagonal pairs retain capacity zero. -/
def upperCapacityApprox (c : Sym2 A → ℝ) (k : ℕ) (e : Sym2 A) : ℝ :=
  if e.IsDiag then 0 else
    (Nat.ceil (((k + 1 : ℕ) : ℝ) * c e) : ℝ) / (k + 1 : ℕ)

/-- The integral deficit of `upperCapacityApprox`. -/
def upperCapacityDeficit (c : Sym2 A → ℝ) (k : ℕ)
    (e : CompleteEdge A) : ℕ :=
  k + 1 - Nat.ceil (((k + 1 : ℕ) : ℝ) * c e)

lemma upperCapacityApprox_eq_zero_of_isDiag (c : Sym2 A → ℝ) (k : ℕ)
    {e : Sym2 A} (he : e.IsDiag) : upperCapacityApprox c k e = 0 := by
  simp [upperCapacityApprox, he]

lemma upperCapacityApprox_nonDiag (c : Sym2 A → ℝ) (k : ℕ)
    (e : CompleteEdge A) :
    upperCapacityApprox c k e =
      (Nat.ceil (((k + 1 : ℕ) : ℝ) * c e) : ℝ) / (k + 1 : ℕ) := by
  simp [upperCapacityApprox, e.2]

lemma upperCapacityDeficit_le (c : Sym2 A → ℝ) (k : ℕ)
    (e : CompleteEdge A) : upperCapacityDeficit c k e ≤ k + 1 := by
  exact Nat.sub_le _ _

lemma ceil_scaled_capacity_le {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) (k : ℕ)
    (e : CompleteEdge A) :
    Nat.ceil (((k + 1 : ℕ) : ℝ) * c e) ≤ k + 1 := by
  apply Nat.ceil_le.mpr
  have he : (e : Sym2 A) ∈
      @SimpleGraph.edgeFinset A (⊤ : SimpleGraph A)
        (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
          (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using e.2
  have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
  simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
    (mul_le_mul_of_nonneg_left (hc.le_one he) hk)

lemma upperCapacityApprox_deficit {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) (k : ℕ)
    (e : CompleteEdge A) :
    upperCapacityApprox c k e =
      1 - (upperCapacityDeficit c k e : ℝ) / (k + 1 : ℕ) := by
  rw [upperCapacityApprox_nonDiag]
  have hceil := ceil_scaled_capacity_le hc k e
  rw [upperCapacityDeficit, Nat.cast_sub hceil]
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  field_simp
  ring

lemma capacity_le_upperCapacityApprox {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) (k : ℕ) (e : Sym2 A) :
    c e ≤ upperCapacityApprox c k e := by
  by_cases he : e.IsDiag
  · rw [upperCapacityApprox_eq_zero_of_isDiag c k he,
      hc.eq_zero_of_isDiag he]
  · rw [upperCapacityApprox, if_neg he]
    have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    apply (le_div_iff₀ hk).mpr
    simpa [mul_comm] using
      (Nat.le_ceil (((k + 1 : ℕ) : ℝ) * c e))

lemma upperCapacityApprox_lt_add_inv {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) (k : ℕ) (e : Sym2 A) :
    upperCapacityApprox c k e < c e + 1 / (k + 1 : ℕ) := by
  by_cases he : e.IsDiag
  · rw [upperCapacityApprox_eq_zero_of_isDiag c k he,
      hc.eq_zero_of_isDiag he]
    positivity
  · rw [upperCapacityApprox, if_neg he]
    have heTop : e ∈
        @SimpleGraph.edgeFinset A (⊤ : SimpleGraph A)
          (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
            (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) := by
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have hc0 : 0 ≤ c e := hc.nonneg heTop
    have hscaled : 0 ≤ ((k + 1 : ℕ) : ℝ) * c e := mul_nonneg (by positivity) hc0
    have hceil := Nat.ceil_lt_add_one hscaled
    have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    apply (div_lt_iff₀ hk).mpr
    calc
      (Nat.ceil (((k + 1 : ℕ) : ℝ) * c e) : ℝ)
          < ((k + 1 : ℕ) : ℝ) * c e + 1 := hceil
      _ = (c e + 1 / (k + 1 : ℕ)) * (k + 1 : ℕ) := by
        field_simp

lemma upperCapacityApprox_isEdgeCapacity {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) (k : ℕ) :
    IsEdgeCapacity (⊤ : SimpleGraph A) (upperCapacityApprox c k) := by
  constructor
  · intro e he
    constructor
    · exact (hc.nonneg he).trans (capacity_le_upperCapacityApprox hc k e)
    · by_cases heDiag : e.IsDiag
      · simp [upperCapacityApprox, heDiag]
      · rw [upperCapacityApprox, if_neg heDiag]
        have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
        apply (div_le_iff₀ hk).mpr
        have hnat := ceil_scaled_capacity_le hc k ⟨e, heDiag⟩
        change Nat.ceil (((k + 1 : ℕ) : ℝ) * c e) ≤ k + 1 at hnat
        norm_num only [one_mul]
        exact_mod_cast hnat
  · intro e he
    have heDiag : e.IsDiag := by
      by_contra hnd
      apply he
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hnd
    exact upperCapacityApprox_eq_zero_of_isDiag c k heDiag

lemma capacityMissingWeight_upperCapacityApprox_le {c : Sym2 A → ℝ}
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) (k : ℕ) :
    capacityMissingWeight (upperCapacityApprox c k) ≤ capacityMissingWeight c := by
  unfold capacityMissingWeight
  gcongr with e he
  exact capacity_le_upperCapacityApprox hc k e

lemma tendsto_upperCapacityApprox (c : Sym2 A → ℝ)
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c) (e : Sym2 A) :
    Tendsto (fun k ↦ upperCapacityApprox c k e) atTop (𝓝 (c e)) := by
  have hupper : Tendsto
      (fun k : ℕ ↦ c e + 1 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (c e)) := by
    have hone : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ ↦ c e) atTop (𝓝 (c e)) :=
      tendsto_const_nhds
    simpa only [Nat.cast_add, Nat.cast_one, add_zero] using hconst.add hone
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · exact fun k ↦ capacity_le_upperCapacityApprox hc k e
  · exact fun k ↦ (upperCapacityApprox_lt_add_inv hc k e).le

lemma zeroExtendTriangleWeight_mem_halfCube (G : SimpleGraph A)
    (w : Finset A → ℝ)
    (hw0 : ∀ t ∈ G.cliqueFinset 3, 0 ≤ w t)
    (hwHalf : IsHalfBounded G w) :
    zeroExtendTriangleWeight G w ∈
      Set.Icc (fun _ ↦ 0) (fun _ ↦ 1 / 2) := by
  constructor
  · intro t
    by_cases ht : t ∈ G.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem ht]
      exact hw0 t ht
    · rw [zeroExtendTriangleWeight_of_not_mem ht]
  · intro t
    by_cases ht : t ∈ G.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem ht]
      exact hwHalf t ht
    · rw [zeroExtendTriangleWeight_of_not_mem ht]
      norm_num

/-- Gruslys--Letzter Lemma 2.4 with no rationality assumption.  The output
is the limit of strong packings of upper rational approximations of `c`. -/
theorem weightedReduction {m : ℕ} (c : Sym2 A → ℝ)
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c)
    (hmissing : capacityMissingWeight c ≤ (m : ℝ)) (a : ℝ)
    (hgraphs : ∀ H : SimpleGraph A, missingEdgeCount H ≤ m →
      HasStrongFractionalPacking H a) :
    ∃ w : Finset A → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph A) c w ∧
        capacityUncoveredWeight (⊤ : SimpleGraph A) c w ≤ a ∧
          IsHalfBounded (⊤ : SimpleGraph A) w := by
  have hex : ∀ k : ℕ, ∃ w : Finset A → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph A) (upperCapacityApprox c k) w ∧
        capacityUncoveredWeight (⊤ : SimpleGraph A)
          (upperCapacityApprox c k) w ≤ a ∧
          IsHalfBounded (⊤ : SimpleGraph A) w := by
    intro k
    apply rationalWeightedReduction (Nat.succ_pos k)
        (upperCapacityApprox c k) (upperCapacityApprox_isEdgeCapacity hc k)
        (upperCapacityDeficit c k) (upperCapacityDeficit_le c k)
        (upperCapacityApprox_deficit hc k)
    · exact (capacityMissingWeight_upperCapacityApprox_le hc k).trans hmissing
    · exact hgraphs
  choose w hwPacking hwUncovered hwHalf using hex
  let v : ℕ → Finset A → ℝ := fun k ↦
    zeroExtendTriangleWeight (⊤ : SimpleGraph A) (w k)
  have hvPacking : ∀ k,
      IsCapacityPacking (⊤ : SimpleGraph A) (upperCapacityApprox c k) (v k) := by
    intro k
    constructor
    · exact zeroExtendTriangleWeight_nonneg le_rfl
        (IsCapacityPacking.toFractionalPacking
          (upperCapacityApprox_isEdgeCapacity hc k) (hwPacking k))
    · intro e he
      rw [fractionalEdgeLoad_zeroExtend le_rfl]
      exact (hwPacking k).2 e he
  have hvUncovered : ∀ k,
      capacityUncoveredWeight (⊤ : SimpleGraph A)
        (upperCapacityApprox c k) (v k) ≤ a := by
    intro k
    simpa only [v, capacityUncoveredWeight,
      fractionalEdgeLoad_zeroExtend le_rfl] using hwUncovered k
  have hvHalf : ∀ k, IsHalfBounded (⊤ : SimpleGraph A) (v k) := by
    intro k
    exact zeroExtendTriangleWeight_le_half le_rfl (hwHalf k)
  let K : Set (Finset A → ℝ) :=
    Set.Icc (fun _ ↦ 0) (fun _ ↦ 1 / 2)
  have hvK : ∀ k, v k ∈ K := by
    intro k
    exact zeroExtendTriangleWeight_mem_halfCube (⊤ : SimpleGraph A) (w k)
      (hwPacking k).1 (hwHalf k)
  obtain ⟨wlim, hwlimK, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact K).tendsto_subseq hvK
  refine ⟨wlim, ?_, ?_, ?_⟩
  · constructor
    · intro t ht
      exact hwlimK.1 t
    · intro e he
      have hload : Tendsto
          (fun n ↦ fractionalEdgeLoad (⊤ : SimpleGraph A) (v (φ n)) e)
          atTop (𝓝 (fractionalEdgeLoad (⊤ : SimpleGraph A) wlim e)) := by
        unfold fractionalEdgeLoad
        apply tendsto_finsetSum
        intro t ht
        simpa only [Function.comp_apply] using tendsto_pi_nhds.mp hlim t
      have hcap := (tendsto_upperCapacityApprox c hc e).comp hφ.tendsto_atTop
      exact le_of_tendsto_of_tendsto' hload hcap fun n ↦
        (hvPacking (φ n)).2 e he
  · have hunc : Tendsto
        (fun n ↦ capacityUncoveredWeight (⊤ : SimpleGraph A)
          (upperCapacityApprox c (φ n)) (v (φ n))) atTop
        (𝓝 (capacityUncoveredWeight (⊤ : SimpleGraph A) c wlim)) := by
      unfold capacityUncoveredWeight
      apply tendsto_finsetSum
      intro e he
      apply ((tendsto_upperCapacityApprox c hc e).comp hφ.tendsto_atTop).sub
      unfold fractionalEdgeLoad
      apply tendsto_finsetSum
      intro t ht
      simpa only [Function.comp_apply] using tendsto_pi_nhds.mp hlim t
    exact le_of_tendsto_of_tendsto' hunc tendsto_const_nhds fun n ↦
      hvUncovered (φ n)
  · intro t ht
    exact hwlimK.2 t

end

end Erdos76
