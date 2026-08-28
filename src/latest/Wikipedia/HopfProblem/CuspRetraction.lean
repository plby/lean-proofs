import Wikipedia.HopfProblem.CuspRetractionFrozenQuotient
import Wikipedia.HopfProblem.CuspRetractionPolarHomotopy

/-!
# Concrete prerequisites for the closed cusp retraction

This file proves the explicit straightening of Lemma 7.5 on sufficiently
small actual closed sub-tubes.  The imported polar construction proves
Lemma 7.6(i),(ii), and spreads a supplied positive-part homotopy as in
Lemma 7.9.

The existence of the positive-part homotopy in Lemma 7.8 is not asserted.
Consequently this file does not claim a deformation retraction of a cusp
neighbourhood onto its central fibre.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- Lemma 7.5(a),(b), on the actual closed toric tube.  The common small
radius follows from continuity; no homeomorphism or extension property
is assumed.  The last conjunct identifies the map with the displayed
exponential correction, while the preceding conjuncts record its
geometric properties. -/
theorem exists_closed_frozen_straightening {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ G : ClosedTube η ≃ₜ ClosedTube η,
          (∀ x : ClosedTube η, time (G x : Space) = time x) ∧
          (∀ x : ClosedTube η, time (x : Space) = 0 → G x = x) ∧
          (∀ (v : Fin 2 → ℤ) x,
            G (closedTranslate C η v x) = closedTranslate (frozen C) η v (G x)) ∧
          (∀ (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
            ∀ x, G (closedFibreAction η u x) = closedFibreAction η u (G x)) ∧
          (∀ x, (G x : Space) = changeTwist C (frozen C) x) := by
  obtain ⟨ε, hε, hεr, hε1, hRC, hRD⟩ := exists_common_frozen_radius C hr hC
  have hCε : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε) :=
    fun i j => (hC i j).mono (Metric.ball_subset_ball hεr.le)
  have hDε : ∀ i j, ContinuousOn (fun t => frozen C t i j) (Metric.ball 0 ε) :=
    fun _ _ => continuousOn_const
  refine ⟨ε / 2, half_pos hε, (half_lt_self hε).trans hεr,
    (half_lt_self hε).trans hε1, ?_⟩
  intro η _hη hη₀
  have hηε : η < ε := hη₀.trans_lt (half_lt_self hε)
  refine ⟨closedTubeHomeomorph C (frozen C) hε hε1 hCε hDε rfl hRC hRD hηε,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact closedTubeHomeomorph_base C (frozen C) hε hε1 hCε hDε rfl hRC hRD hηε
  · exact closedTubeHomeomorph_fixes_central C (frozen C)
      hε hε1 hCε hDε rfl hRC hRD hηε
  · exact closedTubeHomeomorph_equivariant C (frozen C)
      hε hε1 hCε hDε rfl hRC hRD hηε
  · exact closedTubeHomeomorph_fibre_torus C (frozen C)
      hε hε1 hCε hDε rfl hRC hRD hηε
  · intro x
    rfl

end Wikipedia.HopfProblem.CuspRetraction
