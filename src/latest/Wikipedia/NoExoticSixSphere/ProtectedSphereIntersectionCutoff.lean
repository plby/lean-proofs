import Wikipedia.NoExoticSixSphere.GloballyCleanSphereSheetChart
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# A protected source region containing only the chosen mutual intersection

The actual globally clean chart identifies every branch of both maps near
their unique common value. A smooth cutoff is constructed whose zero set
lies in the moving sheet's small source disk. Any mutual intersection there
is exactly the chosen center pair, even when the fixed source is unrestricted.
-/

noncomputable section

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_protected_intersection_cutoff (F G : C(Sphere 3, M))
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hzero : F (sourceChart 0) = G (sourceChart 0))
    (hFu : ∀ x, F x = F (sourceChart 0) → x = sourceChart 0)
    (hGu : ∀ x, G x = G (sourceChart 0) → x = sourceChart 0)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))) :
    ∃ χ : Sphere 3 → ℝ, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ ∧
      (∀ s, 0 ≤ χ s) ∧ (∀ s, ‖χ s‖ ≤ 1) ∧ χ (sourceChart 0) = 0 ∧
      ∀ x y, χ x = 0 → F x = G y → x = sourceChart 0 ∧ y = sourceChart 0 := by
  obtain ⟨b, hb, Φ, hprod, _, hleft, _, hclean⟩ :=
    exists_globally_clean_sphere_sheetChart F G hF hG hzero hFu hGu ht
      isOpen_univ (mem_univ _)
  let U := sourceChart '' ball (0 : Vector 3) b
  have hU : IsOpen U := sourceChart_isOpenMap _ isOpen_ball
  have h0U : sourceChart 0 ∈ U := ⟨0, mem_ball_self hb, rfl⟩
  obtain ⟨β, _, hβU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 3) (sourceChart 0)).mem_iff.mp
      (hU.mem_nhds h0U)
  let χ : Sphere 3 → ℝ := fun s ↦ 1 - β s
  have hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ := contMDiff_const.sub β.contMDiff
  have hn : ∀ s, 0 ≤ χ s := fun s ↦ sub_nonneg.mpr β.le_one
  have hbound : ∀ s, ‖χ s‖ ≤ 1 := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hn s)]
    exact sub_le_self 1 β.nonneg
  have hxχ : χ (sourceChart 0) = 0 := by simp only [χ, β.eq_one, sub_self]
  refine ⟨χ, hχ, hn, hbound, hxχ, ?_⟩
  intro x y hx hxy
  have hβx : β x = 1 := (sub_eq_zero.mp hx).symm
  have hxU : x ∈ U := hβU
    (subset_tsupport β (by change β x ≠ 0; rw [hβx]; exact one_ne_zero))
  obtain ⟨v, hv, rfl⟩ := hxU
  have hq : (v, 0) ∈ Φ.source :=
    hprod ⟨ball_subset_closedBall hv, mem_closedBall_self hb.le⟩
  have hy : G y = Φ (v, 0) := hxy.symm.trans (hleft v hq).symm
  obtain ⟨hv0, hy0⟩ := ((hclean (v, 0) hq).2 y).mp hy
  exact ⟨congrArg sourceChart hv0, hy0⟩

end NoExoticSixSphere.SphereSumNeck
