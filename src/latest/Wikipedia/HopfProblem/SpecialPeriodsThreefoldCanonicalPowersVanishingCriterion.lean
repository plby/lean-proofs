import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleGauges
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalNonTorsionCriterion

/-!
# All positive powers vanish from a genuine square comparison

Suppose the square of a native holomorphic line bundle is genuinely
holomorphically isomorphic to another line whose positive powers have
no holomorphic sections.  Squaring any section of any positive power,
and transporting through the actual power-bundle maps, proves that
section zero.  This handles odd as well as even powers and therefore
also rules out every positive torsion order.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
  {A : TransitionData M ι} {B : TransitionData M κ}
  [A.IsHolomorphic I] [B.IsHolomorphic I]

/-- The square of a section of `A^n` is transported through the actual
native power-swap and powered square-comparison bundle isomorphisms. -/
theorem section_eq_zero_of_square_comparison
    (G : CrossGauge I (A.power 2) B)
    (hB : ∀ n : ℕ, 0 < n → ∀ s : ContMDiffSection I ℂ ω (B.power n).core.Fiber, s = 0)
    (n : ℕ) (hn : 0 < n) (s : ContMDiffSection I ℂ ω (A.power n).core.Fiber) : s = 0 := by
  let J : CrossGauge I ((A.power n).power 2) (B.power n) :=
    (powerSwapGauge I A n 2).toCrossGauge.trans (G.power n)
  have hs : holomorphicSectionPower (A.power n) 2 I s = 0 :=
    J.sections_zero_of_target (hB n hn) _
  exact (holomorphicSectionPower_eq_zero_iff (A.power n) 2 I (by decide) s).mp hs

/-- The vanishing assertion identifies the whole positive-power
holomorphic section space with its zero element. -/
theorem subsingleton_sections_of_square_comparison
    (G : CrossGauge I (A.power 2) B)
    (hB : ∀ n : ℕ, 0 < n → ∀ s : ContMDiffSection I ℂ ω (B.power n).core.Fiber, s = 0)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (ContMDiffSection I ℂ ω (A.power n).core.Fiber) :=
  ⟨fun s t => (section_eq_zero_of_square_comparison G hB n hn s).trans
    (section_eq_zero_of_square_comparison G hB n hn t).symm⟩

/-- Non-torsion uses vanishing in every positive degree, not merely
vanishing of the first canonical section space. -/
theorem not_trivial_power_of_square_comparison [Nonempty M]
    (G : CrossGauge I (A.power 2) B)
    (hB : ∀ n : ℕ, 0 < n → ∀ s : ContMDiffSection I ℂ ω (B.power n).core.Fiber, s = 0)
    (n : ℕ) (hn : 0 < n) : ¬ HolomorphicallyTrivial I (A.power n) :=
  not_holomorphicallyTrivial_of_sections_zero I (A.power n)
    (section_eq_zero_of_square_comparison G hB n hn)

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
