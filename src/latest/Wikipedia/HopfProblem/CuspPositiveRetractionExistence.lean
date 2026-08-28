import Wikipedia.HopfProblem.CuspPositiveRetractionPositive

/-!
# Unconditional existence of the positive cusp deformation

For every constant correction matrix, sufficiently small literal closed
positive tubes admit an actual continuous deformation onto their central
part.  The deformation fixes that part pointwise, decreases height, and
commutes with the genuine positive twisted lattice action.

The homotopy is constructed from the actual toric charts, compact quotient
sublevels, and the covering homotopy lift. No deformation, collar, CW
structure, or homotopy equivalence is assumed.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

open ToricSpace

/-- The positive deformation may be constructed below any radius for
which the already proved quantitative proper-action bound holds. -/
theorem exists_positive_closed_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < ε ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η),
          (∀ q, P (0, q) = q) ∧
          (∀ s q, time (q.1 : Space) = 0 → P (s, q) = q) ∧
          (∀ q, time ((P (1, q)).1 : Space) = 0) ∧
          (∀ s v q, P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
            CuspPositive.closedPositiveTranslate C₀ η v (P (s, q))) ∧
          (∀ s q, ‖time ((P (s, q)).1 : Space)‖ ≤ ‖time (q.1 : Space)‖) := by
  obtain ⟨η₀, hη₀, hη₀ε, A, hA⟩ :=
    exists_positiveQuotient_collapse C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η _hη hηη₀
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  have hAη : {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet :=
    fun _ hx => hA (hx.trans hηη₀)
  refine ⟨positiveDeformation C₀ ε hε hε1 hR A hηε,
    positiveDeformation_zero C₀ ε hε hε1 hR A hηε,
    positiveDeformation_fixed C₀ ε hε hε1 hR A hηε,
    positiveDeformation_one_central C₀ ε hε hε1 hR A hηε hAη,
    positiveDeformation_equivariant C₀ ε hε hε1 hR A hηε,
    positiveDeformation_nonincreasing C₀ ε hε hε1 hR A hηε⟩

/-- Lemma 7.8: a constant matrix alone supplies a small positive closed
tube and an actual lattice-equivariant deformation onto its central part. -/
theorem exists_positive_closed_deformation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η),
          (∀ q, P (0, q) = q) ∧
          (∀ s q, time (q.1 : Space) = 0 → P (s, q) = q) ∧
          (∀ q, time ((P (1, q)).1 : Space) = 0) ∧
          (∀ s v q, P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
            CuspPositive.closedPositiveTranslate C₀ η v (P (s, q))) ∧
          (∀ s q, ‖time ((P (s, q)).1 : Space)‖ ≤ ‖time (q.1 : Space)‖) := by
  obtain ⟨ε, hε, hε1, hR⟩ := exists_smallDrift_radius (CuspPositive.positiveTwist C₀)
    (fun _ _ => continuousAt_const)
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ :=
    exists_positive_closed_deformation_below C₀ ε hε hε1 hR
  exact ⟨η₀, hη₀, hη₀ε.trans hε1, hP⟩

end Wikipedia.HopfProblem.CuspPositiveRetraction
