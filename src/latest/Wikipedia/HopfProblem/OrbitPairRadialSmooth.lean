import Wikipedia.HopfProblem.OrbitPairScalarHopf
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Smoothness on the free part of the radial normal model

The radial coordinate changes are smooth away from zero in the usual
Euclidean atlases. This is the compatibility needed between free orbit
charts and the radial charts at the fixed set; no smoothness of the
radial change at zero is claimed.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair

namespace Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ∞ω} {x : E}

theorem contDiffAt_square (hx : x ≠ 0) : ContDiffAt ℝ n square x :=
  (contDiffAt_norm ℝ hx).smul contDiffAt_id

theorem contDiffAt_root (hx : x ≠ 0) : ContDiffAt ℝ n root x :=
  (((contDiffAt_norm ℝ hx).sqrt (norm_ne_zero_iff.mpr hx)).inv
    (Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hx))).smul contDiffAt_id

end Radial

open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

theorem contDiff_hopfMap {n : ℕ∞ω} : ContDiff ℝ n hopfMap := by
  change ContDiff ℝ n (fun v : ℂ × ℂ =>
    (2 * v.1 * v.2, Complex.normSq v.1 - Complex.normSq v.2))
  simp only [Complex.normSq_eq_norm_sq]
  have hs : ContDiff ℝ n (fun v : ℂ × ℂ => ‖v.1‖ ^ 2 - ‖v.2‖ ^ 2) :=
    (contDiff_fst.norm_sq ℂ).sub (contDiff_snd.norm_sq ℂ)
  exact ((contDiff_const.mul contDiff_fst).mul contDiff_snd).prodMk hs

theorem contDiff_euclideanHopfMap {n : ℕ∞ω} : ContDiff ℝ n euclideanHopfMap :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ).symm.contDiff.comp
    (contDiff_hopfMap.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).contDiff)

/-- The radial Hopf map is smooth on the original punctured Euclidean normal space. -/
theorem contDiffAt_radialHopfMap {n : ℕ∞ω} {v : Normal} (hv : v ≠ 0) :
    ContDiffAt ℝ n radialHopfMap v := by
  have he : radialHopfMap = (fun w => ‖w‖⁻¹ • euclideanHopfMap w) :=
    funext radialHopfMap_eq
  rw [he]
  exact ((contDiffAt_norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul
    contDiff_euclideanHopfMap.contDiffAt

/-- The same statement for the unchanged scalar framing used on the actual normal tube. -/
theorem contDiffAt_scalarHopfMap {n : ℕ∞ω} {v : ℂ × ℂ} (hv : v ≠ 0) :
    ContDiffAt ℝ n scalarHopfMap v := by
  have hc : scalarCoordinates v ≠ 0 := by
    intro h
    apply hv
    exact scalarCoordinates.injective (h.trans scalarCoordinates.map_zero.symm)
  exact (contDiffAt_radialHopfMap hc).comp v scalarCoordinates.contDiff.contDiffAt

end Wikipedia.HopfProblem.OrbitPair
