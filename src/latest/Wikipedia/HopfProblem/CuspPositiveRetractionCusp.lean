import Wikipedia.HopfProblem.CuspPositiveRetractionFrozen
import Wikipedia.HopfProblem.CuspPositiveRetractionStraightened
import Wikipedia.HopfProblem.CuspPositiveRetractionDescent

/-!
# Deformation of actual closed cusp neighborhoods onto the central fibre

The constant-matrix positive deformation is constructed, spread through
the genuine polar quotient, and conjugated by the explicit frozen
straightening. Its lattice-equivariant descent is a strong deformation
retraction of the literal closed subspace of the original cusp quotient.

Only continuity of the supplied correction is needed upstairs; its
already available holomorphicity gives the continuous quotient descent.
No assertion about a deformation retraction of the entire open tube is
made.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

open ToricSpace CuspRetraction

/-- A varying continuous correction has a genuine central deformation on
all sufficiently small closed toric tubes. The original twisted action
and the compact fibre torus commute with every stage. -/
theorem exists_closed_tube_deformation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ H : C(unitInterval × ClosedTube η, ClosedTube η),
          (∀ x, H (0, x) = x) ∧
          (∀ s (x : ClosedTube η), time (x : Space) = 0 → H (s, x) = x) ∧
          (∀ x, time (H (1, x) : Space) = 0) ∧
          (∀ s v x, H (s, closedTranslate C η v x) =
            closedTranslate C η v (H (s, x))) ∧
          (∀ s (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
            ∀ x, H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x))) ∧
          (∀ s x, ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖) := by
  obtain ⟨ε, hε, hεr, hε1, hRC, hRD⟩ := exists_common_frozen_radius C hr hC
  have hCε : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε) :=
    fun i j => (hC i j).mono (Metric.ball_subset_ball hεr.le)
  have hRP : SmallDrift (CuspPositive.positiveTwist (C 0)) ε :=
    CuspPositive.smallDrift_positiveTwist (C 0) hRD
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ :=
    exists_frozen_closed_deformation_below (C 0) ε hε hε1 hRP
  refine ⟨η₀, hη₀, hη₀ε.trans hεr, hη₀ε.trans hε1, ?_⟩
  intro η hη hηη₀
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  obtain ⟨H, hzero, hfix, hone, hequiv, _hcompact, hfibre, hmono⟩ := hH η hη hηη₀
  refine ⟨straightenedHomotopy C hε hε1 hCε hRC hRD hηε H,
    straightenedHomotopy_zero C hε hε1 hCε hRC hRD hηε H hzero,
    straightenedHomotopy_fixed C hε hε1 hCε hRC hRD hηε H hfix,
    straightenedHomotopy_one_central C hε hε1 hCε hRC hRD hηε H hone,
    straightenedHomotopy_equivariant C hε hε1 hCε hRC hRD hηε H hequiv,
    straightenedHomotopy_fibre_torus_equivariant C hε hε1 hCε hRC hRD hηε H hfibre,
    straightenedHomotopy_norm_time_le C hε hε1 hCε hRC hRD hηε H hmono⟩

/-- The central-fibre part of Proposition 7.2 on genuine closed
neighborhoods of the original quotient. The retraction and relative
homotopy are constructed without a geometric or homotopy hypothesis. -/
theorem exists_closed_quotient_strongDeformationRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ →
        ∃ R : C(ClosedQuotient C r η, QuotientCentralFibre C r),
          R.comp (quotientCentralIntoClosed C r η hη.le) =
            ContinuousMap.id (QuotientCentralFibre C r) ∧
          ∃ H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
              ((quotientCentralIntoClosed C r η hη.le).comp R)
              {q : ClosedQuotient C r η | CuspQuotient.projection C r q = 0},
            ∀ s q, ‖CuspQuotient.projection C r (H (s, q))‖ ≤
              ‖CuspQuotient.projection C r q‖ := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hH⟩ :=
    exists_closed_tube_deformation C hr (fun i j => (hC i j).continuousOn)
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀
  have hηr : η < r := hηη₀.trans_lt hη₀r
  obtain ⟨H, hzero, hfix, hone, hequiv, _hfibre, hmono⟩ := hH η hη hηη₀
  refine ⟨closedHomotopyDescentRetraction C hηr H hequiv hC hone,
    closedHomotopyDescentRetraction_comp_inclusion C hηr H hequiv hC hfix hone hη.le,
    closedHomotopyDescentHomotopyRel C hηr H hequiv hC hzero hfix hone hη.le, ?_⟩
  exact closedHomotopyDescent_norm_nonincrease C hηr H hequiv hmono

end Wikipedia.HopfProblem.CuspPositiveRetraction
