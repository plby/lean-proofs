import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Exact closed-disk collar equality determines the actual ordinary derivative

Unique within-differentiability of the closed disk handles its boundary.
The transverse dimension is arbitrary; no equality on an open ambient
collar is assumed or inferred from the closed-disk identity.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskDerivative

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ}

theorem uniqueDiffOn_closedDiskProduct :
    UniqueDiffOn ℝ (closedBall (0 : Vector 4) 1 ×ˢ (univ : Set (Vector d))) := by
  have hD : UniqueDiffOn ℝ (closedBall (0 : Vector 4) 1) :=
    uniqueDiffOn_convex (convex_closedBall (0 : Vector 4) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 (by norm_num))⟩
  exact hD.prod uniqueDiffOn_univ

theorem fderiv_eq_of_closedDisk_collar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H G : Vector 4 × Vector d → F) (r : ℝ)
    (heq : ∀ y ∈ closedBall (0 : Vector 4) 1, r ≤ ‖y‖ → ∀ w : Vector d,
      H (y, w) = G (y, w))
    {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : r < ‖x‖) (v : Vector d)
    (hH : DifferentiableAt ℝ H (x, v)) (hG : DifferentiableAt ℝ G (x, v)) :
    fderiv ℝ H (x, v) = fderiv ℝ G (x, v) := by
  let S := closedBall (0 : Vector 4) 1 ×ˢ (univ : Set (Vector d))
  have hxS : (x, v) ∈ S := ⟨hx, mem_univ v⟩
  have hs : UniqueDiffWithinAt ℝ S (x, v) := uniqueDiffOn_closedDiskProduct _ hxS
  have hn : {p : Vector 4 × Vector d | r < ‖p.1‖} ∈ 𝓝 (x, v) :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).mem_nhds hxr
  have he : H =ᶠ[𝓝[S] (x, v)] G := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with p hp hpn
    exact heq p.1 hp.1 hpn.le p.2
  have hd : fderivWithin ℝ H S (x, v) = fderivWithin ℝ G S (x, v) :=
    he.fderivWithin_eq_of_mem hxS
  rw [fderivWithin_eq_fderiv hs hH, fderivWithin_eq_fderiv hs hG] at hd
  exact hd

end Wikipedia.HopfProblem.DegreeCollapse.GeneralDiskDerivative
