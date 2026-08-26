import ErdosProblems.Erdos788.CanonicalTrevisan
import ErdosProblems.Erdos788.UpperExponentBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final upper bound

This module joins the canonical extractor, the finite palette construction,
and the pointwise exponent calculation for every sufficiently large integer.
-/

namespace Erdos788

/-- Pointwise upper bound at every regular parameter value. -/
theorem cast_fNat_le_rpow_of_parameterRegular
    {N : ℕ} (h : ParameterRegular N) :
    (fNat N : ℝ) ≤
      (N : ℝ) ^
        ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  obtain ⟨C, ⟨E⟩⟩ := exists_chosenLinearExtractorFamily h
  have hp : 2 < parameterPrime N := two_lt_parameterPrime N
  have hr : 0 < parameterDimension N := parameterDimension_pos_of_regular h
  have hnR : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  have hn : 1 ≤ N := by exact_mod_cast hnR.le
  have hcover : N - 1 ≤ parameterPrime N ^ (2 * parameterDimension N) :=
    (Nat.sub_le N 1).trans (parameterDimension_cover N)
  have hfinite := fNat_succ_le_of_trevisanFamily hp hr hcover E
  rw [Nat.sub_add_cancel hn] at hfinite
  have hfiniteReal :
      (fNat N : ℝ) ≤
        (trevisanFiniteUpperBound (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℝ) := by
    exact_mod_cast hfinite
  exact hfiniteReal.trans (cast_trevisanFiniteUpperBound_le_rpow_chosen h C)

/-- The same bound for the integer-valued function in the problem statement. -/
theorem cast_f_le_rpow_of_parameterRegular
    {N : ℕ} (h : ParameterRegular N) :
    (f N : ℝ) ≤
      (N : ℝ) ^
        ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  simpa [f] using! cast_fNat_le_rpow_of_parameterRegular h

/-- Eventual quantified form of the strong upper bound. -/
theorem exists_upperBound_threshold :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (f N : ℝ) ≤
        (N : ℝ) ^
          ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      (f N : ℝ) ≤
        (N : ℝ) ^
          ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) :=
    eventually_parameterRegular.mono fun _N hN ↦
      cast_f_le_rpow_of_parameterRegular hN
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro N hN
  exact hm N ((le_max_right 1 m).trans hN)

end Erdos788
