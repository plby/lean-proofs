import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-! # Boolean quotients defined by vanishing finite weighted masses -/

namespace Erdos1123

open Filter
open scoped Topology symmDiff

/-- A sequence of nonnegative, finitely supported weights. Normalization and
vanishing atom sizes are imposed separately when they are needed. -/
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

@[simp] theorem mass_empty (n : ℕ) : W.mass ∅ n = 0 := by
  classical
  simp [mass]

theorem mass_nonneg (A : Set α) (n : ℕ) : 0 ≤ W.mass A n := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact W.nonneg n x
  · exact le_rfl

theorem mass_mono {A B : Set α} (h : A ⊆ B) (n : ℕ) : W.mass A n ≤ W.mass B n := by
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

theorem mass_symmDiff_le (A B : Set α) (n : ℕ) :
    W.mass (A ∆ B) n ≤ W.mass A n + W.mass B n :=
  (W.mass_mono Set.symmDiff_subset_union n).trans (W.mass_union_le A B n)

theorem mass_congr {A B : Set α} (n : ℕ)
    (h : ∀ x ∈ W.support n, x ∈ A ↔ x ∈ B) : W.mass A n = W.mass B n := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  simp only [h x hx]

theorem mass_inter_add_sdiff (A B : Set α) (n : ℕ) :
    W.mass (A ∩ B) n + W.mass (A \ B) n = W.mass A n := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]

theorem mass_sub_mass_le (A B : Set α) (n : ℕ) :
    W.mass A n - W.mass B n ≤ W.mass (A ∆ B) n := by
  have hsub : A ⊆ B ∪ (A ∆ B) := by
    intro x hx
    by_cases hb : x ∈ B
    · exact Or.inl hb
    · exact Or.inr (by simp [Set.mem_symmDiff, hx, hb])
  have h := (W.mass_mono hsub n).trans (W.mass_union_le B (A ∆ B) n)
  linarith

theorem abs_mass_sub_mass_le (A B : Set α) (n : ℕ) :
    |W.mass A n - W.mass B n| ≤ W.mass (A ∆ B) n := by
  rw [abs_le]
  have h₁ := W.mass_sub_mass_le A B n
  have h₂ := W.mass_sub_mass_le B A n
  rw [symmDiff_comm B A] at h₂
  constructor <;> linarith

/-- Null sets are those whose coordinate masses tend to zero. -/
def IsNull (A : Set α) : Prop := Tendsto (W.mass A) atTop (𝓝 0)

@[simp] theorem isNull_empty : W.IsNull ∅ := by
  unfold IsNull
  have h : W.mass ∅ = fun _ => 0 := funext W.mass_empty
  rw [h]
  exact tendsto_const_nhds

theorem IsNull.mono {A B : Set α} (hB : W.IsNull B) (hAB : A ⊆ B) : W.IsNull A :=
  squeeze_zero (W.mass_nonneg A) (W.mass_mono hAB) hB

theorem IsNull.union {A B : Set α} (hA : W.IsNull A) (hB : W.IsNull B) :
    W.IsNull (A ∪ B) := by
  apply squeeze_zero (W.mass_nonneg _) (W.mass_union_le A B)
  simpa using hA.add hB

theorem IsNull.symmDiff {A B : Set α} (hA : W.IsNull A) (hB : W.IsNull B) :
    W.IsNull (A ∆ B) :=
  IsNull.mono W (IsNull.union W hA hB) Set.symmDiff_subset_union

/-- The null ideal in the Boolean ring of sets. -/
noncomputable def nullIdeal : Ideal (AsBoolRing (Set α)) where
  carrier := {A | W.IsNull (ofBoolRing A)}
  zero_mem' := W.isNull_empty
  add_mem' := fun hA hB => IsNull.symmDiff W hA hB
  smul_mem' := fun _ _ hA => IsNull.mono W hA Set.inter_subset_right

@[simp] theorem mem_nullIdeal (A : AsBoolRing (Set α)) :
    A ∈ W.nullIdeal ↔ W.IsNull (ofBoolRing A) := Iff.rfl

noncomputable instance quotientBooleanRing : BooleanRing (AsBoolRing (Set α) ⧸ W.nullIdeal) :=
  { (inferInstance : Ring (AsBoolRing (Set α) ⧸ W.nullIdeal)) with
    isIdempotentElem := fun a => by
      induction a using Quotient.inductionOn' with
      | h a =>
        change Ideal.Quotient.mk W.nullIdeal a * Ideal.Quotient.mk W.nullIdeal a = _
        rw [← map_mul, BooleanRing.mul_self]
        rfl }

/-- The Boolean algebra of sets modulo vanishing `W`-mass. -/
def Algebra := AsBoolAlg (AsBoolRing (Set α) ⧸ W.nullIdeal)

noncomputable instance : BooleanAlgebra W.Algebra :=
  inferInstanceAs (BooleanAlgebra (AsBoolAlg (AsBoolRing (Set α) ⧸ W.nullIdeal)))

/-- The quotient map, viewed as a Boolean algebra homomorphism. -/
noncomputable def quotientMap : BoundedLatticeHom (Set α) W.Algebra :=
  (Ideal.Quotient.mk W.nullIdeal).asBoolAlg.comp
    ((OrderIso.asBoolAlgAsBoolRing (Set α)).symm :
      BoundedLatticeHom (Set α) (AsBoolAlg (AsBoolRing (Set α))))

@[simp] theorem quotientMap_eq_iff (A B : Set α) :
    W.quotientMap A = W.quotientMap B ↔ W.IsNull (A ∆ B) := by
  change Ideal.Quotient.mk W.nullIdeal (toBoolRing A) =
      Ideal.Quotient.mk W.nullIdeal (toBoolRing B) ↔ _
  rw [Ideal.Quotient.eq]
  rfl

theorem quotientMap_surjective : Function.Surjective W.quotientMap := by
  intro b
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ofBoolAlg b)
  exact ⟨ofBoolRing a, congrArg toBoolAlg ha⟩

end WeightSequence
end Erdos1123
