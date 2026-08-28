import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonBaseUnits
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorInverse
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnit

/-!
# The nonvanishing elliptic comparison coefficient

The actual finite-coordinate differential divided by the global generator
is compared with the already constructed local canonical coefficient.
The three actual vanishing orders cancel.  The quotient on the punctured
disc consequently extends to a holomorphic unit on the original whole
disc; only the proved local unit germs are used at the center.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Elliptic GlobalGenerator SectionsUnit

/-- The source's three exponents agree for both actual elliptic types. -/
theorem exponent_balance (j : Kind) :
    j.order - 1 = ellipticExponent j + vanishingOrder j := by
  cases j <;> rfl

/-- The original modular generator has no other zero in the punctured
normalized elliptic neighborhood. -/
theorem discGenerator_ne_zero (j : Kind) (s : Disc) (hs : (s : ℂ) ≠ 0) :
    discGenerator j s ≠ 0 :=
  generator_ne_zero_regular (EllipticFilling.localBase j ⟨s, hs⟩)

/-- The literal comparison quotient, before filling in its central value. -/
def puncturedRatio (j : Kind) (s : Disc) : ℂ :=
  baseDerivative j s / (discGenerator j s * specialCoefficient j s)

/-- The value forced by the three already established analytic unit germs. -/
def centralRatio (j : Kind) : ℂ :=
  baseUnit j 0 / (ellipticUnit j 0 * specialUnit j discZero)

theorem centralRatio_ne_zero (j : Kind) : centralRatio j ≠ 0 :=
  div_ne_zero (baseUnit_zero_ne_zero j)
    (mul_ne_zero (ellipticUnit_zero_ne_zero j) (specialUnit_ne_zero j discZero))

/-- The extension of the actual punctured quotient, with its forced central value. -/
def ratio (j : Kind) (s : Disc) : ℂ :=
  if (s : ℂ) = 0 then centralRatio j else puncturedRatio j s

@[simp] theorem ratio_zero (j : Kind) : ratio j discZero = centralRatio j := by
  simp only [ratio, discZero_val, ite_true]

theorem ratio_of_ne_zero (j : Kind) (s : Disc) (hs : (s : ℂ) ≠ 0) :
    ratio j s = puncturedRatio j s := if_neg hs

/-- An actual positive radius on which both cancelling analytic factors are valid. -/
def ratioRadius (j : Kind) : ℝ := min (baseUnitRadius j) (ellipticUnitRadius j)

theorem ratioRadius_pos (j : Kind) : 0 < ratioRadius j :=
  lt_min (baseUnitRadius_pos j) (ellipticUnitRadius_pos j)

theorem ratioRadius_le_one (j : Kind) : ratioRadius j ≤ 1 :=
  (min_le_left _ _).trans (baseUnitRadius_le_one j)

/-- Cancellation is performed on the genuine punctured quotient, not by
assigning a power-order tag to the desired extension. -/
theorem puncturedRatio_eq_unit (j : Kind) (s : Disc)
    (hs : ‖(s : ℂ)‖ < ratioRadius j) (hs0 : (s : ℂ) ≠ 0) :
    puncturedRatio j s = baseUnit j s / (ellipticUnit j s * specialUnit j s) := by
  have hb : ‖(s : ℂ)‖ < baseUnitRadius j := lt_of_lt_of_le hs (min_le_left _ _)
  have hf : ‖(s : ℂ)‖ < ellipticUnitRadius j := lt_of_lt_of_le hs (min_le_right _ _)
  rw [puncturedRatio, baseDerivative_disc_factor j s hb,
    discGenerator_factor j s hf, specialCoefficient_eq, exponent_balance, pow_add]
  have hp : (s : ℂ) ^ ellipticExponent j * (s : ℂ) ^ vanishingOrder j ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hs0) (pow_ne_zero _ hs0)
  calc
    _ = (((s : ℂ) ^ ellipticExponent j * (s : ℂ) ^ vanishingOrder j) * baseUnit j s) /
        (((s : ℂ) ^ ellipticExponent j * (s : ℂ) ^ vanishingOrder j) *
          (ellipticUnit j s * specialUnit j s)) := by congr 1; ring
    _ = _ := mul_div_mul_left _ _ hp

/-- The central value and the punctured quotient are represented by the
same analytic unit on an honest neighborhood inside the original disc. -/
theorem ratio_eq_unit (j : Kind) (s : Disc) (hs : ‖(s : ℂ)‖ < ratioRadius j) :
    ratio j s = baseUnit j s / (ellipticUnit j s * specialUnit j s) := by
  by_cases hs0 : (s : ℂ) = 0
  · have he : s = discZero := Subtype.ext hs0
    subst s
    exact ratio_zero j
  · exact (ratio_of_ne_zero j s hs0).trans (puncturedRatio_eq_unit j s hs hs0)

theorem ratio_eq_unit_eventually (j : Kind) :
    ratio j =ᶠ[𝓝 discZero]
      fun s : Disc => baseUnit j s / (ellipticUnit j s * specialUnit j s) := by
  have hn : ∀ᶠ s : Disc in 𝓝 discZero, ‖(s : ℂ)‖ < ratioRadius j :=
    (continuous_subtype_val.norm.tendsto discZero).eventually
      (gt_mem_nhds (by simpa only [discZero_val, norm_zero] using ratioRadius_pos j))
  exact hn.mono (fun s hs => ratio_eq_unit j s hs)

theorem ratio_holomorphicAt_zero (j : Kind) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ratio j) discZero := by
  have hu := (baseUnit_native_holomorphicAt j).div₀
    ((ellipticUnit_native_holomorphicAt j).mul (specialUnit_holomorphic j discZero))
    (mul_ne_zero (ellipticUnit_zero_ne_zero j) (specialUnit_ne_zero j discZero))
  exact hu.congr_of_eventuallyEq (ratio_eq_unit_eventually j)

theorem ratio_holomorphicAt_of_ne_zero (j : Kind) (s : Disc) (hs : (s : ℂ) ≠ 0) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ratio j) s := by
  have hc : specialCoefficient j s ≠ 0 :=
    (specialCoefficient_ne_zero_iff j s).mpr (Or.inr hs)
  have hu := (baseDerivative_native_holomorphic j s).div₀
    ((discGenerator_holomorphic j s).mul (specialCoefficient_holomorphic j s))
    (mul_ne_zero (discGenerator_ne_zero j s hs) hc)
  apply hu.congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt.eventually_ne hs] with t ht
  exact ratio_of_ne_zero j t ht

/-- The extension is holomorphic on the entire original disc, with no
global radius or globally nonzero analytic-factor hypothesis. -/
theorem ratio_holomorphic (j : Kind) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ratio j) := by
  intro s
  by_cases hs : (s : ℂ) = 0
  · have he : s = discZero := Subtype.ext hs
    subst s
    exact ratio_holomorphicAt_zero j
  · exact ratio_holomorphicAt_of_ne_zero j s hs

theorem ratio_ne_zero (j : Kind) (s : Disc) : ratio j s ≠ 0 := by
  by_cases hs : (s : ℂ) = 0
  · rw [ratio, if_pos hs]
    exact centralRatio_ne_zero j
  · rw [ratio_of_ne_zero j s hs]
    exact div_ne_zero (baseDerivative_ne_zero j s hs)
      (mul_ne_zero (discGenerator_ne_zero j s hs)
        ((specialCoefficient_ne_zero_iff j s).mpr (Or.inr hs)))

/-- On the actual puncture this unit is exactly the coefficient relating
the original global differential to the original elliptic canonical section. -/
theorem coefficient_eq_ratio_mul (j : Kind) (s : Disc) (hs : (s : ℂ) ≠ 0) :
    baseDerivative j s / discGenerator j s = ratio j s * specialCoefficient j s := by
  rw [ratio_of_ne_zero j s hs, puncturedRatio, div_mul_eq_div_div,
    div_mul_cancel₀ _ ((specialCoefficient_ne_zero_iff j s).mpr (Or.inr hs))]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
