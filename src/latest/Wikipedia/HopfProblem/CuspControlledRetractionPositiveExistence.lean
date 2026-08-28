import Wikipedia.HopfProblem.CuspControlledRetractionPositive
import Wikipedia.HopfProblem.CuspPositiveRetractionExistence

/-!
# Existence of the controlled positive cusp deformation

The original positive deformation is constructed from the actual toric
charts and quotient covering, then modified by the explicit supported
interpolation.  The sufficiently small tube radius is chosen before the
prescribed positive height. No deformation or endpoint map is assumed.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspPositiveRetraction CuspHoneycomb CuspPositive

/-- Below any quantitative small-drift radius, every sufficiently small
closed positive tube has a deformation with the prescribed honeycomb
endpoint on any chosen positive-height shell. -/
theorem exists_positive_controlled_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < ε ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ η →
          ∃ P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η),
            (∀ q, P (0, q) = q) ∧
            (∀ s (q : ClosedPositiveTube η), time (q.1 : Space) = 0 → P (s, q) = q) ∧
            (∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0) ∧
            (∀ s v q, P (s, closedPositiveTranslate C₀ η v q) =
              closedPositiveTranslate C₀ η v (P (s, q))) ∧
            (∀ s q, ‖time ((P (s, q)).1 : Space)‖ ≤ ‖time (q.1 : Space)‖) ∧
            (∀ q, ‖time (q.1 : Space)‖ = ρ → P (1, q) =
              positiveCentralInclusion η hη.le
                (honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space)))) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ :=
    exists_positive_closed_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀ ρ hρ _hρη
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono⟩ := hP η hη hηη₀
  obtain ⟨Q, hQzero, hQfix, hQone, hQequiv, hQmono, hQend, _hQnear⟩ :=
    exists_positive_modification C₀ hε1 hR (hηη₀.trans_lt hη₀ε) hη.le ρ hρ
      P hzero hfix hone hequiv hmono
  exact ⟨Q, hQzero, hQfix, hQone, hQequiv, hQmono, hQend⟩

/-- A constant correction matrix alone supplies the small radius. The
same radius works for every later choice of positive endpoint height. -/
theorem exists_positive_controlled_deformation
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ η →
          ∃ P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η),
            (∀ q, P (0, q) = q) ∧
            (∀ s (q : ClosedPositiveTube η), time (q.1 : Space) = 0 → P (s, q) = q) ∧
            (∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0) ∧
            (∀ s v q, P (s, closedPositiveTranslate C₀ η v q) =
              closedPositiveTranslate C₀ η v (P (s, q))) ∧
            (∀ s q, ‖time ((P (s, q)).1 : Space)‖ ≤ ‖time (q.1 : Space)‖) ∧
            (∀ q, ‖time (q.1 : Space)‖ = ρ → P (1, q) =
              positiveCentralInclusion η hη.le
                (honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space)))) := by
  obtain ⟨ε, hε, hε1, hR⟩ := positiveTwist_exists_smallDrift_radius C₀
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ :=
    exists_positive_controlled_deformation_below C₀ ε hε hε1 hR
  exact ⟨η₀, hη₀, hη₀ε.trans hε1, hP⟩

end Wikipedia.HopfProblem.CuspControlledRetraction
