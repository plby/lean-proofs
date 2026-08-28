import Wikipedia.HopfProblem.CuspRetractionContinuity
import Wikipedia.HopfProblem.CuspRetractionStraightening

/-!
# Actual homeomorphisms straightening the cusp twist

The maps of Lemma 7.5 are homeomorphisms of the actual toric tubes.  Their
restrictions to closed sub-tubes preserve the base, fix the central fibre,
and intertwine the two lattice actions.  Small radii are obtained from
continuity of the period matrices, not supplied as geometric assumptions.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace

variable (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

def tubeHomeomorph {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε) :
    Tube (CuspQuotient.disc ε) ≃ₜ Tube (CuspQuotient.disc ε) where
  toFun := tubeChangeTwist C D ε
  invFun := tubeChangeTwist D C ε
  left_inv x := by
    apply Subtype.ext
    exact changeTwist_inverse_on_disc C D hε1 hRC hRD
      (by
        have hx : time (x : Space) ∈ Metric.ball 0 ε := x.2
        simpa only [Metric.mem_ball, dist_zero_right] using hx)
  right_inv x := by
    apply Subtype.ext
    exact changeTwist_inverse_on_disc D C hε1 hRD hRC
      (by
        have hx : time (x : Space) ∈ Metric.ball 0 ε := x.2
        simpa only [Metric.mem_ball, dist_zero_right] using hx)
  continuous_toFun := tubeChangeTwist_continuous C D hε hε1 hC hD hzero hRC
  continuous_invFun := tubeChangeTwist_continuous D C hε hε1 hD hC hzero.symm hRD

@[simp] theorem tubeHomeomorph_coe {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (x : Tube (CuspQuotient.disc ε)) :
    (tubeHomeomorph C D hε hε1 hC hD hzero hRC hRD x : Space) = changeTwist C D x := rfl

theorem closedTubeChangeTwist_continuous {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hR : SmallDrift C ε) (hηε : η < ε) :
    Continuous (closedTubeChangeTwist C D η) := by
  have h : ContinuousOn (changeTwist C D) {x : Space | ‖time x‖ ≤ η} :=
    (changeTwist_continuousOn C D hε hε1 hC hD hzero hR).mono (fun x hx => by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx.trans_lt hηε)
  exact h.domRestrict.subtype_mk _

def closedTubeHomeomorph {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (hηε : η < ε) : ClosedTube η ≃ₜ ClosedTube η where
  toFun := closedTubeChangeTwist C D η
  invFun := closedTubeChangeTwist D C η
  left_inv x := Subtype.ext (changeTwist_inverse_on_disc C D hε1 hRC hRD
    (x.2.trans_lt hηε))
  right_inv x := Subtype.ext (changeTwist_inverse_on_disc D C hε1 hRD hRC
    (x.2.trans_lt hηε))
  continuous_toFun := closedTubeChangeTwist_continuous C D hε hε1 hC hD hzero hRC hηε
  continuous_invFun := closedTubeChangeTwist_continuous D C hε hε1 hD hC hzero.symm hRD hηε

@[simp] theorem closedTubeHomeomorph_coe {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (hηε : η < ε) (x : ClosedTube η) :
    (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x : Space) =
      changeTwist C D x := rfl

def closedTranslate (η : ℝ) (v : Fin 2 → ℤ) (x : ClosedTube η) : ClosedTube η :=
  ⟨twistedTranslate C v x, by simpa only [time_twistedTranslate] using x.2⟩

def closedFibreAction (η : ℝ) (u : Fin 2 → ℂˣ) (x : ClosedTube η) : ClosedTube η :=
  ⟨torusAction (fibreMultiplier u) x, by simpa only [time_fibreMultiplier] using x.2⟩

theorem closedTubeHomeomorph_base {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (hηε : η < ε) (x : ClosedTube η) :
    time (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x : Space) = time x :=
  time_changeTwist C D x

theorem closedTubeHomeomorph_fixes_central {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (hηε : η < ε) (x : ClosedTube η) (hx : time (x : Space) = 0) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x = x :=
  Subtype.ext (changeTwist_of_time_zero C D hx)

theorem closedTubeHomeomorph_equivariant {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (hηε : η < ε) (v : Fin 2 → ℤ) (x : ClosedTube η) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε (closedTranslate C η v x) =
      closedTranslate D η v (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x) :=
  Subtype.ext (changeTwist_equivariant_on_disc C D hzero hε1 hRC v (x.2.trans_lt hηε))

theorem closedTubeHomeomorph_fibre_torus {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (hηε : η < ε) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε (closedFibreAction η u x) =
      closedFibreAction η u (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x) :=
  Subtype.ext (changeTwist_unit_fibreAction C D u hu x)

/-- Continuity supplies a common genuine small-drift radius for the
varying twist and its frozen central value. -/
theorem exists_common_frozen_radius {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧ ε < 1 ∧ SmallDrift C ε ∧ SmallDrift (frozen C) ε := by
  have hC0 (i j) : ContinuousAt (fun t => C t i j) 0 :=
    (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
  obtain ⟨δ, hδ, hδ1, hRδ⟩ := exists_smallDrift_radius C hC0
  obtain ⟨δ₀, hδ₀, _, hRδ₀⟩ := exists_smallDrift_radius (frozen C)
    (fun _ _ => continuousAt_const)
  refine ⟨min (r / 2) (min δ δ₀), lt_min (half_pos hr) (lt_min hδ hδ₀),
    (min_le_left _ _).trans_lt (half_lt_self hr),
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt hδ1,
    hRδ.mono ((min_le_right _ _).trans (min_le_left _ _)),
    hRδ₀.mono ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The source's explicit sign and matrix in the straightening exponent. -/
theorem correction_frozen_formula (x : Space) :
    correction C (frozen C) x =
      -((C (time x) - C 0) *ᵥ
        realToComplex (inverseDisplacement C (time x) (position x))) := by
  rw [correction, frozen_apply,
    show C 0 - C (time x) = -(C (time x) - C 0) by abel, Matrix.neg_mulVec]

end Wikipedia.HopfProblem.CuspRetraction
