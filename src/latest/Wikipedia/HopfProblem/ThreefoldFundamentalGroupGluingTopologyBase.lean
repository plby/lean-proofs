import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connected base patches for the actual threefold star cover

The regular patch is the actual regular triangle quotient.  Each filling
patch is a genuine coordinate disc, and its intersection with the regular
patch is precisely the image of the corresponding punctured disc.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

/-- A complex disc remains path connected after removing its center. -/
theorem punctured_complex_ball_isPathConnected {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball (0 : ℂ) r \ {0}) := by
  let e : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.univBall (0 : ℂ) r
  have hsource : e.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have htarget : e.target = Metric.ball 0 r := OpenPartialHomeomorph.univBall_target _ hr
  have hzero : e 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero _ _
  have hinj : Function.Injective e := by
    intro z w h
    exact e.injOn (by rw [hsource]; trivial) (by rw [hsource]; trivial) h
  have himage : e '' ({0}ᶜ : Set ℂ) = Metric.ball 0 r \ {0} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← htarget]
        exact e.map_source (by rw [hsource]; trivial)
      · change e w ≠ 0
        intro h
        exact hw (hinj (h.trans hzero.symm))
    · rintro ⟨hz, hne⟩
      have hzt : z ∈ e.target := by rwa [htarget]
      refine ⟨e.symm z, ?_, e.right_inv hzt⟩
      change e.symm z ≠ 0
      intro h
      have he := e.right_inv hzt
      rw [h, hzero] at he
      exact hne he.symm
  have hconn : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank (by simp) 0
  have him := hconn.image (OpenPartialHomeomorph.continuous_univBall (0 : ℂ) r)
  change IsPathConnected (e '' ({0}ᶜ : Set ℂ)) at him
  rwa [himage] at him

/-- The full regular base is path connected, using its actual quotient inclusion. -/
theorem regularPatch_isPathConnected :
    IsPathConnected (regularPatch : Set TriangleCompactifiedOrbitSpace) := by
  rw [← regularInclusion_range]
  exact isPathConnected_range regularInclusion_isOpenEmbedding.continuous

namespace BaseCover

variable (C : BaseCover)

/-- Every chosen actual filling disc is path connected. -/
theorem fillingPatch_isPathConnected (i : Puncture) :
    IsPathConnected (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace) := by
  rw [C.fillingPatch_eq_inverse_image i]
  exact (Metric.isPathConnected_ball (C.radius_pos i)).image'
    ((punctureChart i).continuousOn_symm.mono (C.coordinateBall_subset_target i))

/-- The literal regular/filling overlap is the image of the whole punctured disc. -/
theorem regular_inter_fillingPatch_eq_image (i : Puncture) :
    (regularPatch : Set TriangleCompactifiedOrbitSpace) ∩ C.fillingPatch i =
      (punctureChart i).symm '' (Metric.ball 0 (C.radius i) \ {0}) := by
  ext x
  constructor
  · rintro ⟨hr, hx⟩
    refine ⟨punctureChart i x, ⟨?_, ?_⟩,
      (punctureChart i).left_inv (C.fillingPatch_subset_chart i hx)⟩
    · simpa only [Metric.mem_ball, dist_zero_right] using
        ((C.mem_fillingPatch i x).mp hx).2
    · exact (C.fillingPatch_regular_iff_coordinate_ne_zero i hx).mp hr
  · rintro ⟨z, ⟨hz, hne⟩, rfl⟩
    exact ⟨(C.inverse_mem_regular_iff i hz).mpr hne,
      C.inverse_mem_fillingPatch i hz⟩

/-- The actual punctured overlap is path connected and nonempty. -/
theorem regular_inter_fillingPatch_isPathConnected (i : Puncture) :
    IsPathConnected ((regularPatch : Set TriangleCompactifiedOrbitSpace) ∩
      C.fillingPatch i) := by
  rw [C.regular_inter_fillingPatch_eq_image i]
  exact (punctured_complex_ball_isPathConnected (C.radius_pos i)).image'
    ((punctureChart i).continuousOn_symm.mono
      (sdiff_subset.trans (C.coordinateBall_subset_target i)))

/-- All four members of the actual base cover are path connected. -/
theorem patch_isPathConnected (i : Index) :
    IsPathConnected (C.patch i : Set TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact regularPatch_isPathConnected
  | some i => exact C.fillingPatch_isPathConnected i

end BaseCover

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
