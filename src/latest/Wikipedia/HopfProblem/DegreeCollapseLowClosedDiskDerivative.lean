import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!

# Actual derivatives from exact closed-disk collar identities in all dimensions

Unique within-differentiability of the closed disk handles its boundary.
An exact closed-collar identity determines the ordinary product derivative;
no equality on an open ambient collar is assumed.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LowDiskDerivative

open NoExoticSixSphere GLOrthonormalization

variable {d q : ℕ}

theorem uniqueDiffOn_closedDiskProduct :
    UniqueDiffOn ℝ (closedBall (0 : Vector (d + 1)) 1 ×ˢ (univ : Set (Vector q))) := by
  have hD : UniqueDiffOn ℝ (closedBall (0 : Vector (d + 1)) 1) :=
    uniqueDiffOn_convex (convex_closedBall (0 : Vector (d + 1)) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 (by norm_num))⟩
  exact hD.prod uniqueDiffOn_univ

theorem fderiv_eq_of_closedDisk_collar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H G : Vector (d + 1) × Vector q → F) (r : ℝ)
    (heq : ∀ y ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖y‖ → ∀ w : Vector q,
      H (y, w) = G (y, w))
    {x : Vector (d + 1)} (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) (hxr : r < ‖x‖) (v : Vector q)
    (hH : DifferentiableAt ℝ H (x, v)) (hG : DifferentiableAt ℝ G (x, v)) :
    fderiv ℝ H (x, v) = fderiv ℝ G (x, v) := by
  let S := closedBall (0 : Vector (d + 1)) 1 ×ˢ (univ : Set (Vector q))
  have hxS : (x, v) ∈ S := ⟨hx, mem_univ v⟩
  have hs : UniqueDiffWithinAt ℝ S (x, v) := uniqueDiffOn_closedDiskProduct _ hxS
  have hn : {p : Vector (d + 1) × Vector q | r < ‖p.1‖} ∈ 𝓝 (x, v) :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).mem_nhds hxr
  have he : H =ᶠ[𝓝[S] (x, v)] G := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with p hp hpn
    exact heq p.1 hp.1 hpn.le p.2
  have hd : fderivWithin ℝ H S (x, v) = fderivWithin ℝ G S (x, v) :=
    he.fderivWithin_eq_of_mem hxS
  rw [fderivWithin_eq_fderiv hs hH, fderivWithin_eq_fderiv hs hG] at hd
  exact hd

end Wikipedia.HopfProblem.DegreeCollapse.LowDiskDerivative

