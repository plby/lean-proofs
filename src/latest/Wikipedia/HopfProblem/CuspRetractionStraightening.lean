import Wikipedia.HopfProblem.CuspRetractionBasic

/-!
# Algebra of the cusp-twist straightening

The inverse real displacement converts the logarithmic position into
lattice coordinates.  Exponentiating the difference of two period
matrices in these coordinates changes the twisted action, with an
explicit inverse obtained by exchanging the two matrices.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace CuspUniformization

theorem displacement_change_matrix
    (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) (u : Fin 2 → ℝ) :
    displacement C t u +
        (fun i => (-2 * Real.pi) *
          (((D t - C t) *ᵥ (fun j => (u j : ℂ))) i).im / Real.log ‖t‖) =
      displacement D t u := by
  ext i
  simp only [displacement, LinearMap.add_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.sub_apply, Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, driftMatrix, div_eq_mul_inv]
  ring

variable (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

theorem changeTwist_mem_openTorus {x : Space} (hx : x ∈ openTorus) :
    changeTwist C D x ∈ openTorus := by
  simpa only [mem_openTorus_iff, time_changeTwist] using hx

/-- The new position is the target displacement of the original lattice coordinates. -/
theorem position_changeTwist {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0)
    (hC : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    position (changeTwist C D x) =
      displacement D (time x) (inverseDisplacement C (time x) (position x)) := by
  rw [changeTwist, position_expFibreAction _ hx]
  have h := displacement_change_matrix C D (time x)
    (inverseDisplacement C (time x) (position x))
  rw [displacement_inverseDisplacement C ht hC] at h
  convert h using 1
  congr 1
  ext i
  have hu : realToComplex (inverseDisplacement C (time x) (position x)) =
      (fun j => ((inverseDisplacement C (time x) (position x)) j : ℂ)) := by
    ext j
    rfl
  simp only [correction, hu, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Exchanging the two matrices negates the exponent at the transformed point. -/
theorem correction_reverse {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0)
    (hC : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4)
    (hD : entryNorm (driftMatrix D (time x)) ≤ -Real.log ‖time x‖ / 4) :
    correction D C (changeTwist C D x) = -correction C D x := by
  unfold correction
  rw [time_changeTwist, position_changeTwist C D hx ht hC,
    inverseDisplacement_displacement D ht hD]
  rw [show C (time x) - D (time x) = -(D (time x) - C (time x)) by abel,
    Matrix.neg_mulVec]

/-- The reverse change of twist is an actual pointwise inverse on the torus. -/
theorem changeTwist_inverse_on_torus {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0)
    (hC : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4)
    (hD : entryNorm (driftMatrix D (time x)) ≤ -Real.log ‖time x‖ / 4) :
    changeTwist D C (changeTwist C D x) = x := by
  change expFibreAction (correction D C (changeTwist C D x)) (changeTwist C D x) = x
  rw [correction_reverse C D hx ht hC hD]
  change expFibreAction (-correction C D x) (expFibreAction (correction C D x) x) = x
  rw [expFibreAction_add, neg_add_cancel, expFibreAction_zero]

/-- The inverse identity also includes the actual central fibre. -/
theorem changeTwist_inverse_on_disc {ε : ℝ} (hε : ε < 1)
    (hC : SmallDrift C ε) (hD : SmallDrift D ε)
    {x : Space} (hx : ‖time x‖ < ε) :
    changeTwist D C (changeTwist C D x) = x := by
  by_cases hx0 : time x = 0
  · rw [changeTwist_of_time_zero C D hx0, changeTwist_of_time_zero D C hx0]
  · have hp : 0 < ‖time x‖ := norm_pos_iff.mpr hx0
    exact changeTwist_inverse_on_torus C D ((mem_openTorus_iff x).mpr hx0)
      (Real.log_neg hp (hx.trans hε)) (hC _ hp hx) (hD _ hp hx)

theorem correction_twistedTranslate (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0)
    (hC : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    correction C D (twistedTranslate C v x) = correction C D x +
      (D (time x) - C (time x)) *ᵥ (fun i => (v i : ℂ)) := by
  unfold correction
  rw [time_twistedTranslate, position_twistedTranslate_displacement C v hx ht.ne,
    inverseDisplacement_add, inverseDisplacement_displacement C ht hC, map_add,
    Matrix.mulVec_add]
  congr 2

/-- On the nonzero fibres the change of twist intertwines the two actual actions. -/
theorem changeTwist_equivariant_on_torus (v : Fin 2 → ℤ) {x : Space}
    (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hC : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    changeTwist C D (twistedTranslate C v x) =
      twistedTranslate D v (changeTwist C D x) := by
  change expFibreAction (correction C D (twistedTranslate C v x)) (twistedTranslate C v x) =
    twistedTranslate D v (expFibreAction (correction C D x) x)
  rw [correction_twistedTranslate C D v hx ht hC,
    twistedTranslate_eq_expFibreAction C v x,
    twistedTranslate_eq_expFibreAction D v (expFibreAction (correction C D x) x),
    time_expFibreAction, ← expFibreAction_translate,
    expFibreAction_add, expFibreAction_add]
  congr 1
  rw [Matrix.sub_mulVec]
  abel

/-- Matching the matrices at zero extends equivariance across every central stratum. -/
theorem changeTwist_equivariant_on_disc (h₀ : C 0 = D 0) {ε : ℝ} (hε : ε < 1)
    (hC : SmallDrift C ε) (v : Fin 2 → ℤ) {x : Space} (hx : ‖time x‖ < ε) :
    changeTwist C D (twistedTranslate C v x) =
      twistedTranslate D v (changeTwist C D x) := by
  by_cases hx0 : time x = 0
  · rw [changeTwist_of_time_zero C D (by simpa only [time_twistedTranslate] using hx0),
      changeTwist_of_time_zero C D hx0,
      twistedTranslate_eq_expFibreAction C v x, twistedTranslate_eq_expFibreAction D v x,
      hx0, h₀]
  · have hp : 0 < ‖time x‖ := norm_pos_iff.mpr hx0
    exact changeTwist_equivariant_on_torus C D v ((mem_openTorus_iff x).mpr hx0)
      (Real.log_neg hp (hx.trans hε)) (hC _ hp hx)

theorem changeTwist_frozen_equivariant {ε : ℝ} (hε : ε < 1) (hC : SmallDrift C ε)
    (v : Fin 2 → ℤ) {x : Space} (hx : ‖time x‖ < ε) :
    changeTwist C (frozen C) (twistedTranslate C v x) =
      twistedTranslate (frozen C) v (changeTwist C (frozen C) x) :=
  changeTwist_equivariant_on_disc C (frozen C) rfl hε hC v hx

/-- Unit-modulus fibre multipliers leave logarithmic position unchanged,
including on the central fibre where its total extension is zero. -/
theorem position_unit_fibreAction (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1)
    (x : Space) :
    position (torusAction (fibreMultiplier u) x) = position x := by
  by_cases hx0 : time x = 0
  · rw [position_of_time_zero (by simpa only [time_fibreMultiplier] using hx0),
      position_of_time_zero hx0]
  · have hx := (mem_openTorus_iff x).mpr hx0
    ext i
    simp only [position, time_fibreMultiplier, logCoordinates, logNorm,
      torusCoordinates_action _ hx, Pi.mul_apply]
    fin_cases i <;> simp [fibreMultiplier, hu]

/-- The straightening commutes with the actual compact fibre torus. -/
theorem changeTwist_unit_fibreAction (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1)
    (x : Space) :
    changeTwist C D (torusAction (fibreMultiplier u) x) =
      torusAction (fibreMultiplier u) (changeTwist C D x) := by
  have hc : correction C D (torusAction (fibreMultiplier u) x) = correction C D x := by
    simp only [correction, time_fibreMultiplier, position_unit_fibreAction u hu]
  simp only [changeTwist, hc, expFibreAction, torusAction_mul]
  rw [mul_comm]

end Wikipedia.HopfProblem.CuspRetraction
