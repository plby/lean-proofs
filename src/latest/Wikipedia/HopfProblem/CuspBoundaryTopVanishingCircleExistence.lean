import Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircleBasic

/-!
# One controlled retraction for an entire nonzero base circle

The radius of the closed tube is chosen before its positive norm shell.
After fixing that shell, one retraction and one strong deformation work
simultaneously at every complex time on the circle.  All endpoint
identities are pointwise identities for the independently prescribed
collapse.  The original ambient radius is retained, and the admissible
small radius is derived from the holomorphic data.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircle

open ToricSpace CuspQuotient CuspRetraction CuspControlledRetraction CuspPositiveRetraction

/-- A single actual strong deformation retraction has the prescribed
endpoint on every point of the chosen norm circle.  In particular its
choice does not depend on a complex time or on an argument of that time. -/
theorem exists_controlled_circle_retraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ → ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η),
        ∃ R : C(ClosedQuotient C r η, QuotientCentralFibre C r),
          R.comp (quotientCentralIntoClosed C r η hη.le) =
            ContinuousMap.id (QuotientCentralFibre C r) ∧
          ∃ H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
              ((quotientCentralIntoClosed C r η hη.le).comp R)
              {q : ClosedQuotient C r η | projection C r q = 0},
            (∀ s q, ‖projection C r (H (s, q))‖ ≤ ‖projection C r q‖) ∧
            HasPrescribedCircleEndpoint C r hr η ρ R ∧
            ∀ hηr : η < r,
              Continuous (prescribedCircleCollapse C r hr η ρ hρ hρη hηr) ∧
              (∀ q : NormCircle C r ρ,
                R (normCircleIntoClosed C r η ρ hρη q) =
                  prescribedCircleCollapse C r hr η ρ hρ hρη hηr q) ∧
              ∀ (t : ℂ) (ht : t ≠ 0) (hnorm : ‖t‖ = ρ),
                Continuous
                  (prescribedActualFibreCollapse C r hr hηr t ht (hnorm.trans_le hρη)) ∧
                ∀ q : ActualQuotientFibre C r t,
                  R ((quotientLevelFibreHomeomorph C r η t (hnorm.trans_le hρη)).symm q).1 =
                    prescribedActualFibreCollapse C r hr hηr t ht (hnorm.trans_le hρη) q := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hret⟩ :=
    exists_closed_quotient_controlled_strongDeformationRetraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  obtain ⟨R, hR, H, hmono, hEnd⟩ := hret η hη hηη₀ ρ hρ hρη
  refine ⟨R, hR, H, hmono, hEnd, ?_⟩
  intro hηr
  refine ⟨prescribedCircleCollapse_continuous_of_endpoint
      C r hr η ρ hρ hρη hηr R hEnd,
    controlledRetraction_normCircle_eq C r hr η ρ hρ hρη hηr R hEnd, ?_⟩
  intro t ht hnorm
  exact ⟨prescribedActualFibreCollapse_continuous_of_circle_endpoint
      C r hr η ρ hρη hηr R hEnd t ht hnorm,
    controlledRetraction_actualFibre_eq C r hr η ρ hρη hηr R hEnd t ht hnorm⟩

end Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircle
