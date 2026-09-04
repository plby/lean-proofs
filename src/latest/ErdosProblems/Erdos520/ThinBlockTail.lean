import ErdosProblems.Erdos520.ConditionalTail
import ErdosProblems.Erdos520.ThinBlock

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory Set

namespace Erdos
namespace Problem520

/-!
# From the thin-block moment bound to the exponential tail

This file removes the conditional-Markov step from the list of paper inputs.
It specializes equation (16) at `r = ell` and proves equation (26), including
the localization to the old-measurable small-energy event.
-/

/-- The old-measurable event on which the preceding Euler-product energy is
at most `A`. -/
def thinBlockSmallEnergy {Ω : Type*} [MeasurableSpace Ω]
    (d : ThinBlockData Ω) (ell j : ℕ) (A : ℝ) : Set Ω :=
  {omega | d.I ell (j - 1) omega ≤ A}

/-- The localized bad event used in the honest union bound.  We use `≤` at
the threshold; this only enlarges the strict event in the paper. -/
def localizedThinBlockBad {Ω : Type*} [MeasurableSpace Ω]
    (d : ThinBlockData Ω) (ell j : ℕ) (A B : ℝ) : Set Ω :=
  {omega | B * A ≤ d.U ell j omega} ∩ thinBlockSmallEnergy d ell j A

/-- Equation (16), specialized at `r = ell`, implies a `2⁻ell` tail for each
localized thin block.  The single constant `C0 = C exp(C)` is independent of
`ell` and `j`.

The only extra hypothesis is the expected one: `I_{j-1}` must be measurable
with respect to the old prime filtration. -/
theorem exists_localizedThinBlockTailConstant_of_momentBound
    {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ThinBlockData Ω)
    (hI : ∀ ell j,
      StronglyMeasurable[d.filtration ell (j - 1)] (d.I ell (j - 1)))
    (hmoment : ThinPrimeBlockMomentBound μ d) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ ell : ℕ, 2 ≤ ell →
        ∀ j : ℕ, 1 ≤ j → j ≤ d.J ell →
          ∀ A B : ℝ, 0 < A → 0 < B → 2 * C0 ≤ B →
            μ.real (localizedThinBlockBad d ell j A B) ≤
              (1 / 2 : ℝ) ^ ell := by
  rcases hmoment with ⟨C, hC, hU, hmoment⟩
  refine ⟨C * Real.exp C, mul_pos hC (Real.exp_pos C), ?_⟩
  intro ell hell j hj hJ A B hA hB hBC
  have hellPos : 0 < ell := lt_of_lt_of_le (by omega : 0 < 2) hell
  have hm := hmoment ell (by omega) j hj hJ ell hell
  have hm_le : d.filtration ell (j - 1) ≤ m0 :=
    d.filtration_le ell (j - 1)
  let : SigmaFinite (μ.trim hm_le) := inferInstance
  have hE : MeasurableSet[d.filtration ell (j - 1)]
      (thinBlockSmallEnergy d ell j A) := by
    exact measurableSet_le (hI ell j).measurable measurable_const
  have hIon : ∀ omega ∈ thinBlockSmallEnergy d ell j A,
      d.I ell (j - 1) omega ≤ A := by
    intro omega homega
    exact homega
  have hroot : ∀ᵐ omega ∂μ,
      (μ[(fun omega => d.U ell j omega ^ ell) |
          d.filtration ell (j - 1)] omega) ^
          (1 / (ell : ℝ)) ≤
        (C * Real.exp C) * d.I ell (j - 1) omega := by
    filter_upwards [hm.2] with omega homega
    have hellReal : (ell : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hellPos
    have hquot : C * (ell : ℝ) / (ell : ℝ) = C := by
      field_simp
    simpa only [hquot, mul_assoc] using! homega
  change μ.real
      ({omega | B * A ≤ d.U ell j omega} ∩
        thinBlockSmallEnergy d ell j A) ≤ (1 / 2 : ℝ) ^ ell
  exact measureReal_inter_le_two_pow_of_condExp_rpow_on_event
    (m := d.filtration ell (j - 1)) (m0 := m0)
    hm_le hE hellPos hA hB (mul_pos hC (Real.exp_pos C)).le hBC
    (hU ell j) hIon hm.1 hroot

/-- All-scale version of the preceding theorem.  At `ell = 0` the desired
bound is the probability bound `μ(E) ≤ 1`; at `ell = 1` we use the second
moment.  From `ell ≥ 2` onward this is exactly the specialization `r = ell`.

The explicit nonnegativity of `I` is automatic for Caich's Euler-product
energy and lets one use the common constant `C exp(2C)` at every scale. -/
theorem exists_localizedThinBlockTailConstant_allScales
    {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ThinBlockData Ω)
    (hI : ∀ ell j,
      StronglyMeasurable[d.filtration ell (j - 1)] (d.I ell (j - 1)))
    (hI_nonneg : ∀ ell j omega, 0 ≤ d.I ell j omega)
    (hmoment : ThinPrimeBlockMomentBound μ d) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ ell j : ℕ, 1 ≤ j → j ≤ d.J ell →
        ∀ A B : ℝ, 0 < A → 0 < B → 2 * C0 ≤ B →
          μ.real (localizedThinBlockBad d ell j A B) ≤
            (1 / 2 : ℝ) ^ ell := by
  rcases hmoment with ⟨C, hC, hU, hmoment⟩
  refine ⟨C * Real.exp (2 * C), mul_pos hC (Real.exp_pos _), ?_⟩
  intro ell j hj hJ A B hA hB hBC
  by_cases hell0 : ell = 0
  · subst ell
    simpa using! (measureReal_le_one (μ := μ)
      (s := localizedThinBlockBad d 0 j A B))
  have hellPos : 0 < ell := Nat.pos_of_ne_zero hell0
  let r := max 2 ell
  have hr2 : 2 ≤ r := le_max_left 2 ell
  have hellr : ell ≤ r := le_max_right 2 ell
  have hm := hmoment ell hellPos j hj hJ r hr2
  have hm_le : d.filtration ell (j - 1) ≤ m0 :=
    d.filtration_le ell (j - 1)
  let : SigmaFinite (μ.trim hm_le) := inferInstance
  have hE : MeasurableSet[d.filtration ell (j - 1)]
      (thinBlockSmallEnergy d ell j A) := by
    exact measurableSet_le (hI ell j).measurable measurable_const
  have hIon : ∀ omega ∈ thinBlockSmallEnergy d ell j A,
      d.I ell (j - 1) omega ≤ A := by
    intro omega homega
    exact homega
  have hexponent : C * (r : ℝ) / (ell : ℝ) ≤ 2 * C := by
    by_cases hell2 : 2 ≤ ell
    · have hrEq : r = ell := max_eq_right hell2
      rw [hrEq]
      have hellReal : (ell : ℝ) ≠ 0 := by exact_mod_cast hell0
      field_simp
      linarith
    · have hell1 : ell = 1 := by omega
      subst ell
      norm_num [r]
      have hcomm : C * 2 = 2 * C := by ring
      exact hcomm.le
  have hroot : ∀ᵐ omega ∂μ,
      (μ[(fun omega => d.U ell j omega ^ r) |
          d.filtration ell (j - 1)] omega) ^
          (1 / (r : ℝ)) ≤
        (C * Real.exp (2 * C)) * d.I ell (j - 1) omega := by
    filter_upwards [hm.2] with omega homega
    refine homega.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hC.le)
      (hI_nonneg ell (j - 1) omega)
  have htail :
      μ.real ({omega | B * A ≤ d.U ell j omega} ∩
        thinBlockSmallEnergy d ell j A) ≤ (1 / 2 : ℝ) ^ r :=
    measureReal_inter_le_two_pow_of_condExp_rpow_on_event
      (m := d.filtration ell (j - 1)) (m0 := m0)
      hm_le hE (lt_of_lt_of_le (by omega : 0 < 2) hr2) hA hB
      (mul_pos hC (Real.exp_pos _)).le hBC (hU ell j) hIon hm.1 hroot
  change μ.real
      ({omega | B * A ≤ d.U ell j omega} ∩
        thinBlockSmallEnergy d ell j A) ≤ (1 / 2 : ℝ) ^ ell
  exact htail.trans
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hellr)

end Problem520
end Erdos
