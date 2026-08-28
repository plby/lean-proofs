import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.SetTheory.Cardinal.Order

/-!
# Leading coefficients of an arbitrary integral submodule

The support filtration of a well-ordered free module has principal leading
coefficient ideals.  Their generators can be lifted to triangular vectors
in the original submodule.  No finite-rank hypothesis is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyFreeEvaluation

open Submodule Submodule.IsPrincipal

namespace LocalFree

variable {ι : Type*} [LinearOrder ι] (N : Submodule ℤ (ι →₀ ℤ))

/-- Vectors of the submodule supported on the closed initial segment at `i`. -/
def initialSubmodule (i : ι) : Submodule ℤ (ι →₀ ℤ) :=
  N ⊓ Finsupp.supported ℤ ℤ (Set.Iic i)

theorem mem_initialSubmodule_iff (i : ι) (x : ι →₀ ℤ) :
    x ∈ initialSubmodule N i ↔ x ∈ N ∧ ∀ j, i < j → x j = 0 := by
  simp only [initialSubmodule, Submodule.mem_inf, Finsupp.mem_supported',
    Set.mem_Iic, not_le]

/-- The ideal of coefficients in degree `i` of vectors with support at most `i`. -/
def leadingIdeal (i : ι) : Ideal ℤ :=
  (initialSubmodule N i).map (Finsupp.lapply i)

theorem exists_leadingVector (i : ι) :
    ∃ x : ι →₀ ℤ, x ∈ N ∧ (∀ j, i < j → x j = 0) ∧
      x i = generator (leadingIdeal N i) := by
  obtain ⟨x, hx, he⟩ := (show generator (leadingIdeal N i) ∈
    (initialSubmodule N i).map (Finsupp.lapply i) from
      generator_mem (leadingIdeal N i))
  exact ⟨x, (mem_initialSubmodule_iff N i x).mp hx |>.1,
    (mem_initialSubmodule_iff N i x).mp hx |>.2, he⟩

/-- A lift of the generator of the actual leading coefficient ideal. -/
def leadingVector (i : ι) : N :=
  ⟨(exists_leadingVector N i).choose, (exists_leadingVector N i).choose_spec.1⟩

theorem leadingVector_above (i j : ι) (h : i < j) :
    (leadingVector N i).val j = 0 :=
  (exists_leadingVector N i).choose_spec.2.1 j h

theorem leadingVector_diagonal (i : ι) :
    (leadingVector N i).val i = generator (leadingIdeal N i) :=
  (exists_leadingVector N i).choose_spec.2.2

theorem generator_dvd_coefficient (i : ι) (x : N)
    (hx : ∀ j, i < j → x.val j = 0) :
    generator (leadingIdeal N i) ∣ x.val i := by
  apply (mem_iff_generator_dvd (leadingIdeal N i)).mp
  exact ⟨x.val, (mem_initialSubmodule_iff N i x.val).mpr ⟨x.property, hx⟩, rfl⟩

/-- Only the nonzero leading ideals contribute a basis vector. -/
abbrev LeadingIndex := {i : ι // generator (leadingIdeal N i) ≠ 0}

/-- The triangular family in the original submodule. -/
def leadingFamily (i : LeadingIndex N) : N := leadingVector N i.val

theorem leadingFamily_diagonal_ne_zero (i : LeadingIndex N) :
    (leadingFamily N i).val i.val ≠ 0 := by
  rw [leadingFamily, leadingVector_diagonal]
  exact i.property

theorem leadingFamily_above (i j : LeadingIndex N) (h : i < j) :
    (leadingFamily N i).val j.val = 0 :=
  leadingVector_above N i.val j.val h

end LocalFree

/-- A nonzero finitely supported vector has a largest nonzero coordinate. -/
theorem exists_largest_support {ι : Type*} [LinearOrder ι] (x : ι →₀ ℤ) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ ∀ j, i < j → x j = 0 := by
  classical
  have hs : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hx
  refine ⟨x.support.max' hs, Finsupp.mem_support_iff.mp (Finset.max'_mem _ _), ?_⟩
  intro j hj
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  exact not_le_of_gt hj (Finset.le_max' _ _ hmem)

/-- A family with nonzero diagonal and zero entries above it is linearly independent,
even when its ordered index set is infinite. -/
theorem triangular_linearIndependent {ι M : Type*} [LinearOrder ι]
    [AddCommGroup M] [Module ℤ M] (v : ι → M) (coord : ι → M →ₗ[ℤ] ℤ)
    (hdiag : ∀ i, coord i (v i) ≠ 0)
    (htri : ∀ i j, i < j → coord j (v i) = 0) : LinearIndependent ℤ v := by
  classical
  apply linearIndependent_iff.mpr
  intro l hl
  by_contra hne
  obtain ⟨i, hi, himax⟩ := exists_largest_support l hne
  have his : i ∈ l.support := Finsupp.mem_support_iff.mpr hi
  have heval : ∑ j ∈ l.support, l j * coord i (v j) = 0 := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      smul_eq_mul, map_zero] using congrArg (coord i) hl
  have hsum : (∑ j ∈ l.support, l j * coord i (v j)) = l i * coord i (v i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hle : j ≤ i := le_of_not_gt fun hij =>
        Finsupp.mem_support_iff.mp hj (himax j hij)
      rw [htri j i (lt_of_le_of_ne hle hji), mul_zero]
    · intro h
      exact (h his).elim
  rw [hsum] at heval
  exact (mul_ne_zero hi (hdiag i)) heval

end Wikipedia.HopfProblem.SingularCohomologyFreeEvaluation
