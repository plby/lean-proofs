import Wikipedia.HopfProblem.CuspPositiveRetractionExistence
import Wikipedia.HopfProblem.CuspPositiveRetractionEquivariance
import Wikipedia.HopfProblem.CuspPositiveRetractionPolarProperties

/-!
# Constructing the frozen cusp deformation

Spreading the constructed positive-part deformation through the actual
compact-torus polar quotient gives the deformation of the full closed
toric tube. The exact phase covariance proves frozen-lattice equivariance.
The compact torus and its fibre subtorus act equivariantly throughout.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

open ToricSpace CuspRetraction

/-- Lemma 7.9 below a prescribed small-drift radius, with the positive
deformation constructed by Lemma 7.8 rather than supplied as an input. -/
theorem exists_frozen_closed_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < ε ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ H : C(unitInterval × ClosedTube η, ClosedTube η),
          (∀ x, H (0, x) = x) ∧
          (∀ s (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x) ∧
          (∀ x, time (H (1, x) : Space) = 0) ∧
          (∀ s v x, H (s, closedTranslate (fun _ => C₀) η v x) =
            closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
          (∀ s u x, H (s, closedCompactAction η u x) =
            closedCompactAction η u (H (s, x))) ∧
          (∀ s (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
            ∀ x, H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x))) ∧
          (∀ s x, ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ :=
    exists_positive_closed_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono⟩ := hP η hη hηη₀
  let H : C(unitInterval × ClosedTube η, ClosedTube η) :=
    ⟨fun p => polarSpread P p.1 p.2, polarSpread_continuous P hfix⟩
  exact ⟨H, polarSpread_zero P hfix hzero, polarSpread_fixed P hfix,
    polarSpread_one_central P hfix hone,
    polarSpread_frozen_equivariant C₀ P hfix hequiv,
    polarSpread_compactTorus_equivariant P hfix,
    polarSpread_fibre_torus_equivariant P hfix,
    polarSpread_norm_time_le P hfix hmono⟩

/-- Every constant correction admits actual equivariant closed-tube
deformations at all sufficiently small positive radii. -/
theorem exists_frozen_closed_deformation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ H : C(unitInterval × ClosedTube η, ClosedTube η),
          (∀ x, H (0, x) = x) ∧
          (∀ s (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x) ∧
          (∀ x, time (H (1, x) : Space) = 0) ∧
          (∀ s v x, H (s, closedTranslate (fun _ => C₀) η v x) =
            closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
          (∀ s u x, H (s, closedCompactAction η u x) =
            closedCompactAction η u (H (s, x))) ∧
          (∀ s (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
            ∀ x, H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x))) ∧
          (∀ s x, ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖) := by
  obtain ⟨ε, hε, hε1, hR⟩ := exists_smallDrift_radius (CuspPositive.positiveTwist C₀)
    (fun _ _ => continuousAt_const)
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ := exists_frozen_closed_deformation_below C₀ ε hε hε1 hR
  exact ⟨η₀, hη₀, hη₀ε.trans hε1, hH⟩

end Wikipedia.HopfProblem.CuspPositiveRetraction
