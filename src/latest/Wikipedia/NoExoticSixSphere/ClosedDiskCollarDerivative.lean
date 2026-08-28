import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Ordinary derivative comparison from an exact closed-disk collar formula

The closed ball has unique within-derivatives, also at its boundary. Two
differentiable product maps agreeing on its outer collar therefore have the
same ordinary derivative there. No equality on an open ambient collar is
assumed or inferred from equality on the closed disk.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace NoExoticSixSphere

open GLOrthonormalization

theorem fderiv_eq_of_closedBall_collar {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H G : Vector n → F) (r : ℝ)
    (heq : ∀ y ∈ closedBall (0 : Vector n) 1, r ≤ ‖y‖ → H y = G y)
    {x : Vector n} (hx : x ∈ closedBall (0 : Vector n) 1) (hxr : r < ‖x‖)
    (hH : DifferentiableAt ℝ H x) (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ H x = fderiv ℝ G x := by
  have hs : UniqueDiffOn ℝ (closedBall (0 : Vector n) 1) :=
    uniqueDiffOn_convex (convex_closedBall _ _)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 (by norm_num))⟩
  have hn : {y : Vector n | r < ‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hxr
  have he : H =ᶠ[𝓝[closedBall 0 1] x] G := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with y hy hyr
    exact heq y hy hyr.le
  have hd : fderivWithin ℝ H (closedBall 0 1) x = fderivWithin ℝ G (closedBall 0 1) x :=
    he.fderivWithin_eq_of_mem hx
  rw [fderivWithin_eq_fderiv (hs x hx) hH, fderivWithin_eq_fderiv (hs x hx) hG] at hd
  exact hd

theorem uniqueDiffOn_closedDiskProduct {d : ℕ} :
    UniqueDiffOn ℝ (closedBall (0 : Vector 4) 1 ×ˢ (univ : Set (Vector d))) := by
  have hD : UniqueDiffOn ℝ (closedBall (0 : Vector 4) 1) :=
    uniqueDiffOn_convex (convex_closedBall (0 : Vector 4) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 (by norm_num))⟩
  exact hD.prod uniqueDiffOn_univ

theorem fderiv_eq_of_closedDisk_collar {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
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

end NoExoticSixSphere
