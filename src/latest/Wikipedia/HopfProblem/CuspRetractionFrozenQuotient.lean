import Wikipedia.HopfProblem.CuspRetractionRadius

/-!
# Frozen-twist comparison inside the original cusp neighbourhood

Shrinking the working radius does not replace the closed subspace of the
original quotient.  The radius comparison identifies those literal
subspaces by the same toric representatives.  Composing it with the
explicit straightening gives the frozen-twist homeomorphism inside the
original cusp neighbourhood.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricSpace CuspQuotient

theorem closedQuotientHomeomorph_closedQuotientMap
    (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (hηε : η < ε) (x : ClosedTube η) :
    closedQuotientHomeomorph C D η hε hε1 hC hD hzero hRC hRD
      (closedQuotientMap C hηε x) =
        closedQuotientMap D hηε (closedTubeChangeTwist C D η x) := by
  apply Subtype.ext
  rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

def frozenClosedQuotientHomeomorph {r δ η : ℝ}
    (hδr : δ ≤ r) (hηδ : η < δ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hRC : SmallDrift C δ) (hRD : SmallDrift (frozen C) δ) :
    ClosedQuotient C r η ≃ₜ ClosedQuotient (frozen C) r η :=
  (closedQuotientRadiusHomeomorph C hδr hηδ hC).symm.trans
    ((closedQuotientHomeomorph C (frozen C) η hδ hδ1
      (fun i j => ((hC i j).mono (Metric.ball_subset_ball hδr)).continuousOn)
      (fun _ _ => continuousOn_const) rfl hRC hRD).trans
        (closedQuotientRadiusHomeomorph (frozen C) hδr hηδ
          (fun _ _ => contDiffOn_const)))

theorem frozenClosedQuotientHomeomorph_closedQuotientMap {r δ η : ℝ}
    (hδr : δ ≤ r) (hηδ : η < δ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hRC : SmallDrift C δ) (hRD : SmallDrift (frozen C) δ) (x : ClosedTube η) :
    frozenClosedQuotientHomeomorph C hδr hηδ hδ hδ1 hC hRC hRD
      (closedQuotientMap C (hηδ.trans_le hδr) x) =
        closedQuotientMap (frozen C) (hηδ.trans_le hδr)
          (closedTubeChangeTwist C (frozen C) η x) := by
  simp only [frozenClosedQuotientHomeomorph, Homeomorph.trans_apply,
    closedQuotientRadiusHomeomorph_symm_closedQuotientMap]
  rw [closedQuotientHomeomorph_closedQuotientMap C (frozen C) hδ hδ1
    (fun i j => ((hC i j).mono (Metric.ball_subset_ball hδr)).continuousOn)
    (fun _ _ => continuousOn_const) rfl hRC hRD hηδ x]
  exact closedQuotientRadiusHomeomorph_closedQuotientMap (frozen C) hδr hηδ
    (fun _ _ => contDiffOn_const) _

theorem frozenClosedQuotientHomeomorph_base {r δ η : ℝ}
    (hδr : δ ≤ r) (hηδ : η < δ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hRC : SmallDrift C δ) (hRD : SmallDrift (frozen C) δ) (x : ClosedQuotient C r η) :
    projection (frozen C) r
      (frozenClosedQuotientHomeomorph C hδr hηδ hδ hδ1 hC hRC hRD x) =
        projection C r x := by
  obtain ⟨y, rfl⟩ := closedQuotientMap_surjective C (hηδ.trans_le hδr) x
  rw [frozenClosedQuotientHomeomorph_closedQuotientMap,
    closedQuotientMap_projection, closedQuotientMap_projection]
  exact time_changeTwist C (frozen C) y

theorem frozenClosedQuotientHomeomorph_central {r δ η : ℝ}
    (hδr : δ ≤ r) (hηδ : η < δ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hRC : SmallDrift C δ) (hRD : SmallDrift (frozen C) δ)
    (x : ClosedTube η) (hx : time (x : Space) = 0) :
    frozenClosedQuotientHomeomorph C hδr hηδ hδ hδ1 hC hRC hRD
      (closedQuotientMap C (hηδ.trans_le hδr) x) =
        closedQuotientMap (frozen C) (hηδ.trans_le hδr) x := by
  rw [frozenClosedQuotientHomeomorph_closedQuotientMap]
  apply congrArg (closedQuotientMap (frozen C) (hηδ.trans_le hδr))
  exact Subtype.ext (changeTwist_of_time_zero C (frozen C) hx)

/-- An actual sufficiently small closed subspace of the original cusp
quotient is identified over the base with the frozen-twist quotient.
The map is explicitly induced by the toric correction on representatives. -/
theorem exists_frozen_closedQuotient_homeomorph {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ G : ClosedQuotient C r η ≃ₜ ClosedQuotient (frozen C) r η,
          (∀ x, projection (frozen C) r (G x) = projection C r x) ∧
          (∀ (hηr : η < r) (x : ClosedTube η),
            G (closedQuotientMap C hηr x) =
              closedQuotientMap (frozen C) hηr (closedTubeChangeTwist C (frozen C) η x)) := by
  obtain ⟨δ, hδ, hδr, hδ1, hRC, hRD⟩ := exists_common_frozen_radius C hr
    (fun i j => (hC i j).continuousOn)
  refine ⟨δ / 2, half_pos hδ, (half_lt_self hδ).trans hδr,
    (half_lt_self hδ).trans hδ1, ?_⟩
  intro η _hη hη₀
  have hηδ : η < δ := hη₀.trans_lt (half_lt_self hδ)
  refine ⟨frozenClosedQuotientHomeomorph C hδr.le hηδ hδ hδ1 hC hRC hRD,
    frozenClosedQuotientHomeomorph_base C hδr.le hηδ hδ hδ1 hC hRC hRD, ?_⟩
  intro _hηr x
  exact frozenClosedQuotientHomeomorph_closedQuotientMap C hδr.le hηδ hδ hδ1 hC hRC hRD x

end Wikipedia.HopfProblem.CuspRetraction
