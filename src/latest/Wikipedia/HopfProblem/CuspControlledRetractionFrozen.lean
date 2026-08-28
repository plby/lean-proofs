import Wikipedia.HopfProblem.CuspControlledRetractionPositiveExistence
import Wikipedia.HopfProblem.CuspControlledRetractionPolarEndpoint

/-!
# Existence of the controlled frozen cusp deformation

The constructed positive homotopy is spread through the actual polar
quotient. It retains all seven frozen-deformation properties, and its
endpoint agrees exactly with the independently defined prescribed
collapse on any chosen positive-height shell.  A single sufficiently
small radius works for all later choices of that height.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositive

/-- The controlled frozen deformation is constructed below a given
small-drift radius; no positive or full deformation is supplied. -/
theorem exists_frozen_controlled_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < ε ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ η →
          ∃ H : C(unitInterval × ClosedTube η, ClosedTube η),
            (∀ x, H (0, x) = x) ∧
            (∀ s (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x) ∧
            (∀ x, time (H (1, x) : Space) = 0) ∧
            (∀ s v x, H (s, closedTranslate (fun _ => C₀) η v x) =
              closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
            (∀ s φ x, H (s, closedCompactAction η φ x) =
              closedCompactAction η φ (H (s, x))) ∧
            (∀ s (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
              ∀ x, H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x))) ∧
            (∀ s x, ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖) ∧
            (∀ x : PuncturedClosedTube η, ‖time (x.1 : Space)‖ = ρ →
              H (1, x.1) = centralIntoClosedTube η hη.le (prescribedCollapse C₀ η x)) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ :=
    exists_positive_controlled_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono, hEnd⟩ := hP η hη hηη₀ ρ hρ hρη
  obtain ⟨hHzero, hHfix, hHone, hHequiv, hHcompact, hHfibre, hHmono⟩ :=
    polarDeformation_properties C₀ P hfix hzero hone hequiv hmono
  refine ⟨polarDeformation P hfix, hHzero, hHfix, hHone,
    hHequiv, hHcompact, hHfibre, hHmono, ?_⟩
  exact polarDeformation_prescribedCollapse C₀ P hfix ρ hη.le hEnd

/-- Unconditional controlled Lemma 7.10 for every frozen correction:
there is a common small tube radius, and for every later positive height
the actual equivariant deformation has exactly the prescribed endpoint. -/
theorem exists_frozen_controlled_deformation
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ η →
          ∃ H : C(unitInterval × ClosedTube η, ClosedTube η),
            (∀ x, H (0, x) = x) ∧
            (∀ s (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x) ∧
            (∀ x, time (H (1, x) : Space) = 0) ∧
            (∀ s v x, H (s, closedTranslate (fun _ => C₀) η v x) =
              closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
            (∀ s φ x, H (s, closedCompactAction η φ x) =
              closedCompactAction η φ (H (s, x))) ∧
            (∀ s (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
              ∀ x, H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x))) ∧
            (∀ s x, ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖) ∧
            (∀ x : PuncturedClosedTube η, ‖time (x.1 : Space)‖ = ρ →
              H (1, x.1) = centralIntoClosedTube η hη.le (prescribedCollapse C₀ η x)) := by
  obtain ⟨ε, hε, hε1, hR⟩ := positiveTwist_exists_smallDrift_radius C₀
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ :=
    exists_frozen_controlled_deformation_below C₀ ε hε hε1 hR
  exact ⟨η₀, hη₀, hη₀ε.trans hε1, hH⟩

end Wikipedia.HopfProblem.CuspControlledRetraction
