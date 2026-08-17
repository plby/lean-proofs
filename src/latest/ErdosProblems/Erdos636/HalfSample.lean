/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos636.External.Erdos88.Fourier

/-!
# Symmetry of uniform half-samples

If a finite population has size `2 * s`, complementation is a fixed-point
free involution of the uniform `s`-subsets (apart from the degenerate empty
population).  For arbitrary real coefficients, the sums on complementary
subsets add to the total population sum.  Consequently the distribution of
the subset sum is symmetric about its expectation, and its probability of
being at least its expectation is at least `1 / 2`.

Everything here is an exact finite statement using normalized counting
probability; there are no asymptotic or measurability hypotheses.
-/

open scoped BigOperators

namespace Erdos636
namespace HalfSample

open Erdos88.Fourier

universe u

/-- The finite sample space of subsets of `I` having cardinality `s`. -/
abbrev Slice (I : Type u) [Fintype I] (s : ℕ) :=
  {S : Finset I // S.card = s}

/-- A half-slice is nonempty when the population cardinality is `2 * s`. -/
theorem sliceNonempty {I : Type u} [Fintype I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) : Nonempty (Slice I s) := by
  classical
  have hs : s ≤ (Finset.univ : Finset I).card := by
    simp only [Finset.card_univ, hcard]
    omega
  obtain ⟨S, _hS, hScard⟩ := Finset.exists_subset_card_eq hs
  exact ⟨⟨S, hScard⟩⟩

/-- Complementation, restricted to the slice of half-size subsets. -/
noncomputable def sliceComplement {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) : Slice I s ≃ Slice I s where
  toFun S := ⟨S.1ᶜ, by rw [Finset.card_compl, S.2, hcard]; omega⟩
  invFun S := ⟨S.1ᶜ, by rw [Finset.card_compl, S.2, hcard]; omega⟩
  left_inv S := by ext i; simp
  right_inv S := by ext i; simp

@[simp] lemma sliceComplement_val {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (S : Slice I s) :
    (sliceComplement hcard S).1 = S.1ᶜ := rfl

@[simp] lemma sliceComplement_apply_apply {I : Type u} [Fintype I]
    [DecidableEq I] {s : ℕ} (hcard : Fintype.card I = 2 * s)
    (S : Slice I s) :
    sliceComplement hcard (sliceComplement hcard S) = S := by
  exact (sliceComplement hcard).symm_apply_apply S

/-- Sum of a real coefficient population on one slice point. -/
noncomputable def sliceSum {I : Type u} [Fintype I] {s : ℕ}
    (a : I → ℝ) (S : Slice I s) : ℝ :=
  by classical exact ∑ i ∈ S.1, a i

/-- Exact complement identity for coefficient sums. -/
lemma sliceSum_complement_add {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (a : I → ℝ)
    (S : Slice I s) :
    sliceSum a (sliceComplement hcard S) + sliceSum a S = ∑ i, a i := by
  exact Finset.sum_compl_add_sum S.1 a

/-- Exact symmetry of a half-slice coefficient sum about half the total. -/
lemma sliceSum_complement {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (a : I → ℝ)
    (S : Slice I s) :
    sliceSum a (sliceComplement hcard S) = (∑ i, a i) - sliceSum a S := by
  linarith [sliceSum_complement_add hcard a S]

/-- Uniform expectation of the coefficient sum on a half-slice. -/
noncomputable def sliceExpectation {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (a : I → ℝ) : ℝ := by
  let _ := sliceNonempty hcard
  exact finExpectation (Slice I s) (sliceSum a)

/-- Uniform probability of an event on a half-slice. -/
noncomputable def sliceProbability {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s)
    (P : Slice I s → Prop) : ℝ := by
  let _ := sliceNonempty hcard
  exact finProbability (Slice I s) P

/-- The mean of an arbitrary real coefficient sum on a uniform half-slice
is exactly half of the total population sum. -/
theorem sliceExpectation_eq_half_total {I : Type u} [Fintype I]
    [DecidableEq I] {s : ℕ} (hcard : Fintype.card I = 2 * s)
    (a : I → ℝ) :
    sliceExpectation hcard a = (∑ i, a i) / 2 := by
  classical
  let _ := sliceNonempty hcard
  let e : Slice I s ≃ Slice I s := sliceComplement hcard
  let X : Slice I s → ℝ := sliceSum a
  have hperm : (∑ S, X (e S)) = ∑ S, X S := e.sum_comp X
  have hpoint : ∀ S, X (e S) = (∑ i, a i) - X S := by
    intro S
    exact sliceSum_complement hcard a S
  simp_rw [hpoint] at hperm
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hperm
  have hN : (Fintype.card (Slice I s) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [sliceExpectation, finExpectation]
  change (∑ S, X S) / (Fintype.card (Slice I s) : ℝ) = _
  apply (div_eq_iff hN).2
  linarith

/-- Distributional complement symmetry: the probability that a half-sample
sum is at least `r` equals the probability that it is at most the reflected
threshold `total - r`. -/
theorem sliceProbability_ge_eq_le_reflection {I : Type u} [Fintype I]
    [DecidableEq I] {s : ℕ} (hcard : Fintype.card I = 2 * s)
    (a : I → ℝ) (r : ℝ) :
    sliceProbability hcard (fun S ↦ r ≤ sliceSum a S) =
      sliceProbability hcard (fun S ↦
        sliceSum a S ≤ (∑ i, a i) - r) := by
  classical
  let _ := sliceNonempty hcard
  let e : Slice I s ≃ Slice I s := sliceComplement hcard
  let P : Slice I s → Prop := fun S ↦ r ≤ sliceSum a S
  let Q : Slice I s → Prop := fun S ↦
    sliceSum a S ≤ (∑ i, a i) - r
  have hreflect : ∀ S, P S ↔ Q (e S) := by
    intro S
    change r ≤ sliceSum a S ↔
      sliceSum a (sliceComplement hcard S) ≤ (∑ i, a i) - r
    rw [sliceSum_complement]
    constructor <;> intro h <;> linarith
  have hfiltered :
      (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
    rw [← Fintype.card_subtype P, ← Fintype.card_subtype Q]
    exact Fintype.card_congr (Equiv.subtypeEquiv e hreflect)
  rw [sliceProbability, sliceProbability, finProbability, finProbability]
  exact congrArg (fun m : ℕ ↦ (m : ℝ) / Fintype.card (Slice I s)) hfiltered

/-- On a uniform half-slice, an arbitrary real coefficient sum lies above
half the total population sum with probability at least `1 / 2`. -/
theorem one_half_le_sliceProbability_ge_half_total {I : Type u}
    [Fintype I] [DecidableEq I] {s : ℕ}
    (hcard : Fintype.card I = 2 * s) (a : I → ℝ) :
    (1 : ℝ) / 2 ≤ sliceProbability hcard (fun S ↦
      (∑ i, a i) / 2 ≤ sliceSum a S) := by
  classical
  let _ := sliceNonempty hcard
  let total : ℝ := ∑ i, a i
  let X : Slice I s → ℝ := sliceSum a
  let P : Slice I s → Prop := fun S ↦ total / 2 ≤ X S
  let Q : Slice I s → Prop := fun S ↦ X S ≤ total / 2
  let A : Finset (Slice I s) := Finset.univ.filter P
  let B : Finset (Slice I s) := Finset.univ.filter Q
  let e : Slice I s ≃ Slice I s := sliceComplement hcard
  have hreflect : ∀ S, P S ↔ Q (e S) := by
    intro S
    change total / 2 ≤ sliceSum a S ↔
      sliceSum a (sliceComplement hcard S) ≤ total / 2
    rw [sliceSum_complement]
    change total / 2 ≤ sliceSum a S ↔
      total - sliceSum a S ≤ total / 2
    constructor <;> intro h <;> linarith
  have hAB : A.card = B.card := by
    change (Finset.univ.filter P).card = (Finset.univ.filter Q).card
    rw [← Fintype.card_subtype P, ← Fintype.card_subtype Q]
    exact Fintype.card_congr (Equiv.subtypeEquiv e hreflect)
  have hcover : A ∪ B = Finset.univ := by
    ext S
    simp only [A, B, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact le_total (total / 2) (X S)
  have hcount : Fintype.card (Slice I s) ≤ 2 * A.card := by
    calc
      Fintype.card (Slice I s) = (A ∪ B).card := by rw [hcover, Finset.card_univ]
      _ ≤ A.card + B.card := Finset.card_union_le A B
      _ = 2 * A.card := by omega
  have hNpos : (0 : ℝ) < Fintype.card (Slice I s) := by
    exact_mod_cast Fintype.card_pos
  rw [sliceProbability, finProbability]
  change (1 : ℝ) / 2 ≤ (A.card : ℝ) / Fintype.card (Slice I s)
  rw [le_div_iff₀ hNpos]
  have hcountR : (Fintype.card (Slice I s) : ℝ) ≤ 2 * A.card := by
    exact_mod_cast hcount
  linarith

/-- The same half-probability statement, expressed directly relative to the
uniform expectation. -/
theorem one_half_le_sliceProbability_ge_expectation {I : Type u}
    [Fintype I] [DecidableEq I] {s : ℕ}
    (hcard : Fintype.card I = 2 * s) (a : I → ℝ) :
    (1 : ℝ) / 2 ≤ sliceProbability hcard (fun S ↦
      sliceExpectation hcard a ≤ sliceSum a S) := by
  rw [sliceExpectation_eq_half_total]
  exact one_half_le_sliceProbability_ge_half_total hcard a

end HalfSample
end Erdos636
