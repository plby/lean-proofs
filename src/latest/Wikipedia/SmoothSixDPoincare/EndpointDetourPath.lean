import Wikipedia.SmoothSixDPoincare.RelativeCurveHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Endpoint detours retain the original path class

Follow the prescribed initial curve out and back, then the original path,
then the terminal curve out and back. The two detours cancel by actual path
homotopies. Their parametrizations agree with the prescribed real curves
on the initial and terminal quarters of the unit interval.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CurveImmersion

variable {N : Type*} [TopologicalSpace N] (a b : C(ℝ, N))

def initialDetour : Path (a (1 / 4)) (a 0) :=
  Path.ofLine (f := fun t : ℝ => a ((1 - t) / 4))
    ((a.continuous.comp ((continuous_const.sub continuous_id).div_const 4)).continuousOn)
    (by norm_num) (by norm_num)

def terminalDetour : Path (b 1) (b (3 / 4)) :=
  Path.ofLine (f := fun t : ℝ => b (1 - t / 4))
    ((b.continuous.comp (continuous_const.sub (continuous_id.div_const 4))).continuousOn)
    (by norm_num) (by norm_num)

def endpointDetourPath (γ : Path (a 0) (b 1)) : Path (a 0) (b 1) :=
  ((initialDetour a).symm.trans (initialDetour a)).trans
    ((γ.trans (terminalDetour b)).trans (terminalDetour b).symm)

theorem endpointDetourPath_homotopic (γ : Path (a 0) (b 1)) :
    (endpointDetourPath a b γ).Homotopic γ := by
  have hr : ((γ.trans (terminalDetour b)).trans (terminalDetour b).symm).Homotopic γ :=
    (Path.Homotopic.trans_assoc γ (terminalDetour b) (terminalDetour b).symm).trans
      (((Path.Homotopic.refl γ).hcomp (Path.Homotopic.trans_symm (terminalDetour b))).trans
        (Path.Homotopic.trans_refl γ))
  exact ((Path.Homotopic.symm_trans (initialDetour a)).hcomp hr).trans
    (Path.Homotopic.refl_trans γ)

theorem endpointDetourPath_left (γ : Path (a 0) (b 1))
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 4) :
    endpointDetourPath a b γ t = a t := by
  rw [endpointDetourPath, Path.trans_apply, dif_pos (show (t : ℝ) ≤ 1 / 2 by linarith)]
  rw [Path.trans_apply, dif_pos (show 2 * (t : ℝ) ≤ 1 / 2 by linarith)]
  change a ((1 - (1 - 2 * (2 * (t : ℝ)))) / 4) = a t
  congr 1
  ring

theorem endpointDetourPath_right (γ : Path (a 0) (b 1))
    (t : unitInterval) (ht : 3 / 4 < (t : ℝ)) :
    endpointDetourPath a b γ t = b t := by
  rw [endpointDetourPath, Path.trans_apply,
    dif_neg (show ¬ (t : ℝ) ≤ 1 / 2 by linarith)]
  rw [Path.trans_apply, dif_neg (show ¬ 2 * (t : ℝ) - 1 ≤ 1 / 2 by linarith)]
  change b (1 - (1 - (2 * (2 * (t : ℝ) - 1) - 1)) / 4) = b t
  congr 1
  ring

end Wikipedia.SmoothSixDPoincare.CurveImmersion
