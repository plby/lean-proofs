import Wikipedia.HopfProblem.CuspControlledRetractionFrozen
import Wikipedia.HopfProblem.CuspControlledRetractionStraightenedCollapse
import Wikipedia.HopfProblem.CuspCollapseCentralProjection

/-!
# Controlled deformation of the original closed cusp neighborhood

The explicitly modified positive deformation is spread through the
actual polar quotient, then conjugated by the genuine frozen straightening.
Its endpoint agrees exactly with the independently defined prescribed
honeycomb collapse on a chosen positive-height shell. The resulting
equivariant homotopy descends to a strong deformation retraction of the
literal closed neighborhood in the original cusp quotient.

The small radius is chosen before the height; the deformation is chosen
after the height. No assertion of simultaneous control at every height
by one homotopy, or of an open-tube retraction, is made.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse

/-- Controlled Lemma 7.10 for the original varying twist, on actual closed
toric tubes and with an independently defined endpoint map. -/
theorem exists_closed_tube_controlled_deformation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ η →
        ∃ H : C(unitInterval × ClosedTube η, ClosedTube η),
          (∀ x, H (0, x) = x) ∧
          (∀ s (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x) ∧
          (∀ x, time (H (1, x) : Space) = 0) ∧
          (∀ s v x, H (s, closedTranslate C η v x) =
            closedTranslate C η v (H (s, x))) ∧
          (∀ s (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
            ∀ x, H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x))) ∧
          (∀ s x, ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖) ∧
          (∀ x : PuncturedClosedTube η, ‖time (x.1 : Space)‖ = ρ →
            H (1, x.1) = centralIntoClosedTube η hη.le (straightenedPrescribedCollapse C η x)) := by
  obtain ⟨ε, hε, hεr, hε1, hRC, hRD⟩ := exists_common_frozen_radius C hr hC
  have hCε : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε) :=
    fun i j => (hC i j).mono (Metric.ball_subset_ball hεr.le)
  have hRP : SmallDrift (CuspPositive.positiveTwist (C 0)) ε :=
    CuspPositive.smallDrift_positiveTwist (C 0) hRD
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ :=
    exists_frozen_controlled_deformation_below (C 0) ε hε hε1 hRP
  refine ⟨η₀, hη₀, hη₀ε.trans hεr, hη₀ε.trans hε1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  obtain ⟨H, hzero, hfix, hone, hequiv, _hcompact, hfibre, hmono, hEnd⟩ :=
    hH η hη hηη₀ ρ hρ hρη
  refine ⟨straightenedHomotopy C hε hε1 hCε hRC hRD hηε H,
    straightenedHomotopy_zero C hε hε1 hCε hRC hRD hηε H hzero,
    straightenedHomotopy_fixed C hε hε1 hCε hRC hRD hηε H hfix,
    straightenedHomotopy_one_central C hε hε1 hCε hRC hRD hηε H hone,
    straightenedHomotopy_equivariant C hε hε1 hCε hRC hRD hηε H hequiv,
    straightenedHomotopy_fibre_torus_equivariant C hε hε1 hCε hRC hRD hηε H hfibre,
    straightenedHomotopy_norm_time_le C hε hε1 hCε hRC hRD hηε H hmono, ?_⟩
  exact straightenedHomotopy_prescribed_endpoint C hε hε1 hCε hRC hRD hηε H hη.le hEnd

/-- The controlled endpoint survives passage to the literal original
cusp quotient. The last identity is on every actual toric representative
at the chosen positive height. -/
theorem exists_closed_quotient_controlled_strongDeformationRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ η →
        ∃ R : C(ClosedQuotient C r η, QuotientCentralFibre C r),
          R.comp (quotientCentralIntoClosed C r η hη.le) =
            ContinuousMap.id (QuotientCentralFibre C r) ∧
          ∃ H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
              ((quotientCentralIntoClosed C r η hη.le).comp R)
              {q : ClosedQuotient C r η | CuspQuotient.projection C r q = 0},
            (∀ s q, ‖CuspQuotient.projection C r (H (s, q))‖ ≤
              ‖CuspQuotient.projection C r q‖) ∧
            (∀ (hηr : η < r) (x : PuncturedClosedTube η), ‖time (x.1 : Space)‖ = ρ →
              R (closedQuotientMap C hηr x.1) =
                centralProject C r hr (straightenedPrescribedCollapse C η x)) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hH⟩ :=
    exists_closed_tube_controlled_deformation C hr (fun i j => (hC i j).continuousOn)
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  have hηr : η < r := hηη₀.trans_lt hη₀r
  obtain ⟨H, hzero, hfix, hone, hequiv, _hfibre, hmono, hEnd⟩ :=
    hH η hη hηη₀ ρ hρ hρη
  refine ⟨closedHomotopyDescentRetraction C hηr H hequiv hC hone,
    closedHomotopyDescentRetraction_comp_inclusion C hηr H hequiv hC hfix hone hη.le,
    closedHomotopyDescentHomotopyRel C hηr H hequiv hC hzero hfix hone hη.le,
    closedHomotopyDescent_norm_nonincrease C hηr H hequiv hmono, ?_⟩
  intro hηr' x hx
  apply Subtype.ext
  exact closedHomotopyDescentRetraction_endpoint_of_eq C hηr H hequiv hC hone hη.le
    x.1 (straightenedPrescribedCollapse C η x) (hEnd x hx)

end Wikipedia.HopfProblem.CuspControlledRetraction
