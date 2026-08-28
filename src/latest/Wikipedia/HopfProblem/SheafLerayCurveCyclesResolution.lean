import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The actual cycles augmented resolution in every degree

For the original cochain complex `K`, this is the native exact sequence
`0 → Zⁿ(K) → Kⁿ → Zⁿ⁺¹(K) → Hⁿ⁺¹(K) → 0`.
The objects and maps are the existing cycles, differential into cycles,
and homology quotient. No reindexed or replacement complex is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- The native short complex from the original differential and homology quotient. -/
@[simps] def cyclesComplex (K : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ n (n + 1))

/-- The original homology quotient is the cokernel of the actual differential into cycles. -/
theorem cyclesComplex_exact (K : CochainComplex C ℕ) (n : ℕ) :
    (cyclesComplex K n).Exact :=
  (cyclesComplex K n).exact_of_g_is_cokernel
    (K.homologyIsCokernel n (n + 1) (CochainComplex.prev_nat_succ n))

instance cyclesComplex_epi_g (K : CochainComplex C ℕ) (n : ℕ) :
    Epi (cyclesComplex K n).g := inferInstanceAs (Epi (K.homologyπ (n + 1)))

/-- The actual cycle inclusion is killed by the actual differential into cycles. -/
@[reassoc (attr := simp)] theorem iCycles_toCycles (K : CochainComplex C ℕ) (n : ℕ) :
    K.iCycles n ≫ K.toCycles n (n + 1) = 0 := by
  rw [← cancel_mono (K.iCycles (n + 1)), assoc, K.toCycles_i, zero_comp]
  exact K.iCycles_d n (n + 1)

/-- Exactness at the original degree-`n` term is the native cycles kernel property. -/
theorem cyclesInitial_exact (K : CochainComplex C ℕ) (n : ℕ) :
    (ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (iCycles_toCycles K n)).Exact := by
  let S := ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (iCycles_toCycles K n)
  let T := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 (K.cycles n)
      τ₂ := 𝟙 (K.X n)
      τ₃ := K.iCycles (n + 1)
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (K.cycles n)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (K.X n)))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (K.iCycles (n + 1)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (T.exact_of_f_is_kernel (K.cyclesIsKernel n (n + 1) (CochainComplex.next ℕ n)))

/-- The actual all-degree cycles augmented resolution. -/
def cyclesResolution (K : CochainComplex C ℕ) (n : ℕ) :
    CuspNormalization.SheafCohomologyResolution.AugmentedResolution C where
  F := K.cycles n
  complex := cyclesComplex K n
  ι := K.iCycles n
  zero := iCycles_toCycles K n
  initial_exact := cyclesInitial_exact K n
  exact := cyclesComplex_exact K n
  mono_ι := inferInstanceAs (Mono (K.iCycles n))
  epi_g := cyclesComplex_epi_g K n

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
