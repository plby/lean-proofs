/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology symmDiff

namespace Erdos1123

/-- A sequence of nonnegative, finitely supported weights. -/
structure WeightSequence (α : Type*) where
  support : ℕ → Finset α
  weight : ℕ → α → ℝ
  nonneg : ∀ n x, 0 ≤ weight n x

namespace WeightSequence

variable {α : Type*} (W : WeightSequence α)

/-- The weighted mass of a set at one coordinate. -/
noncomputable def mass (A : Set α) (n : ℕ) : ℝ := by
  classical
  exact ∑ x ∈ W.support n, if x ∈ A then W.weight n x else 0

theorem mass_empty (n : ℕ) : W.mass ∅ n = 0 := by
  classical
  simp [mass]

theorem mass_nonneg (A : Set α) (n : ℕ) : 0 ≤ W.mass A n := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact W.nonneg n x
  · exact le_rfl

theorem mass_mono {A B : Set α} (h : A ⊆ B) (n : ℕ) :
    W.mass A n ≤ W.mass B n := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hA : x ∈ A
  · simp [hA, h hA]
  · simp only [hA, ↓reduceIte]
    split_ifs
    · exact W.nonneg n x
    · exact le_rfl

theorem mass_union_le (A B : Set α) (n : ℕ) :
    W.mass (A ∪ B) n ≤ W.mass A n + W.mass B n := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
    simp [ha, hb, W.nonneg n x]

/-- Null sets have weighted masses tending to zero. -/
def IsNull (A : Set α) : Prop := Tendsto (W.mass A) atTop (𝓝 0)

theorem isNull_empty : W.IsNull ∅ := by
  unfold IsNull
  have h : W.mass ∅ = fun _ => 0 := funext W.mass_empty
  rw [h]
  exact tendsto_const_nhds

theorem IsNull.mono {A B : Set α} (hB : W.IsNull B) (hAB : A ⊆ B) :
    W.IsNull A :=
  squeeze_zero (W.mass_nonneg A) (W.mass_mono hAB) hB

theorem IsNull.union {A B : Set α} (hA : W.IsNull A) (hB : W.IsNull B) :
    W.IsNull (A ∪ B) := by
  apply squeeze_zero (W.mass_nonneg _) (W.mass_union_le A B)
  simpa using hA.add hB

theorem IsNull.symmDiff {A B : Set α} (hA : W.IsNull A) (hB : W.IsNull B) :
    W.IsNull (A ∆ B) :=
  IsNull.mono W (IsNull.union W hA hB) Set.symmDiff_subset_union

/-- The ideal of sets with vanishing weighted mass. -/
noncomputable def nullIdeal : Ideal (AsBoolRing (Set α)) where
  carrier := {A | W.IsNull (ofBoolRing A)}
  zero_mem' := W.isNull_empty
  add_mem' := fun hA hB => IsNull.symmDiff W hA hB
  smul_mem' := fun _ _ hA => IsNull.mono W hA Set.inter_subset_right

noncomputable instance quotientBooleanRing :
    BooleanRing (AsBoolRing (Set α) ⧸ W.nullIdeal) :=
  { (inferInstance : Ring (AsBoolRing (Set α) ⧸ W.nullIdeal)) with
    isIdempotentElem := fun a => by
      induction a using Quotient.inductionOn' with
      | h a =>
        change Ideal.Quotient.mk W.nullIdeal a *
          Ideal.Quotient.mk W.nullIdeal a = _
        rw [← map_mul, BooleanRing.mul_self]
        rfl }

/-- The Boolean algebra of sets modulo vanishing weighted mass. -/
def Algebra := AsBoolAlg (AsBoolRing (Set α) ⧸ W.nullIdeal)

noncomputable instance : BooleanAlgebra W.Algebra :=
  inferInstanceAs (BooleanAlgebra (AsBoolAlg (AsBoolRing (Set α) ⧸ W.nullIdeal)))

end WeightSequence

/-- Ordinary counting-density weights on positive initial segments. -/
noncomputable def ordinaryWeights : WeightSequence ℕ where
  support n := Finset.Icc 1 n
  weight n _ := (n : ℝ)⁻¹
  nonneg n _ := inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Logarithmic-density weights on positive initial segments. -/
noncomputable def logarithmicWeights : WeightSequence ℕ where
  support n := Finset.Icc 1 n
  weight n x := (x : ℝ)⁻¹ / Real.log n
  nonneg n x := div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg x))
    (Real.log_natCast_nonneg n)

abbrev B₁ := ordinaryWeights.Algebra

abbrev B₂ := logarithmicWeights.Algebra

/-- Under the continuum hypothesis, the density quotient Boolean algebras
are order-isomorphic. -/
theorem erdos_1123
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1) :
    Nonempty (B₁ ≃o B₂) := by
  sorry

end Erdos1123
