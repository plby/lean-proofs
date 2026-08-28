import Wikipedia.NoExoticSixSphere.SmoothHalfCubeCoordinates
import Wikipedia.NoExoticSixSphere.SmoothCubeSphereQuotient

/-!
# The two smooth branches of native sphere concatenation

Conjugate the actual affine half-cube expansion by the smooth cube-interior
sphere chart. Each branch is a native partial diffeomorphism onto the
punctured sphere. The two sources are disjoint and cover everything apart
from the pole and the middle cube-coordinate seam.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization

def halfSphere (b : ℝ) : Set (Sphere 3) :=
  (sphereChart 3).source ∩ sphereChart 3 ⁻¹' halfCube 3 0 b

def halfSphereCoordinates (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ where
  toFun y := (sphereChart 3).symm (expand 3 0 b (sphereChart 3 y))
  invFun y := (sphereChart 3).symm (compress 3 0 b (sphereChart 3 y))
  source := halfSphere b
  target := {spherePole 3}ᶜ
  map_source' y hy := (sphereChart 3).map_target (expand_mem_openCube 3 0 b hy.2)
  map_target' y hy := by
    have hc := compress_mem_halfCube 3 0 b hb ((sphereChart 3).map_source hy)
    refine ⟨(sphereChart 3).map_target hc.1, ?_⟩
    change sphereChart 3 ((sphereChart 3).symm (compress 3 0 b (sphereChart 3 y))) ∈ halfCube 3 0 b
    rw [sphereChart_right_inv 3 hc.1]
    exact hc
  left_inv' y hy := by
    change (sphereChart 3).symm (compress 3 0 b
      (sphereChart 3 ((sphereChart 3).symm (expand 3 0 b (sphereChart 3 y))))) = y
    rw [sphereChart_right_inv 3 (expand_mem_openCube 3 0 b hy.2), compress_expand]
    exact sphereChart_left_inv 3 hy.1
  right_inv' y hy := by
    have hc := compress_mem_halfCube 3 0 b hb ((sphereChart 3).map_source hy)
    change (sphereChart 3).symm (expand 3 0 b
      (sphereChart 3 ((sphereChart 3).symm (compress 3 0 b (sphereChart 3 y))))) = y
    rw [sphereChart_right_inv 3 hc.1, expand_compress]
    exact sphereChart_left_inv 3 hy
  open_source := (sphereChart 3).toOpenPartialHomeomorph.isOpen_inter_preimage
    (isOpen_halfCube 3 0 b)
  open_target := isClosed_singleton.isOpen_compl
  contMDiffOn_toFun := by
    have hc := (sphereChart 3).contMDiffOn_toFun.mono
      (show halfSphere b ⊆ (sphereChart 3).source from inter_subset_left)
    exact (sphereChart 3).contMDiffOn_invFun.comp
      ((contDiff_expand 3 0 b).contMDiff.comp_contMDiffOn hc)
      (fun y hy ↦ expand_mem_openCube 3 0 b hy.2)
  contMDiffOn_invFun := by
    exact (sphereChart 3).contMDiffOn_invFun.comp
      ((contDiff_compress 3 0 b).contMDiff.comp_contMDiffOn
        (sphereChart 3).contMDiffOn_toFun)
      (fun y hy ↦ (compress_mem_halfCube 3 0 b hb ((sphereChart 3).map_source hy)).1)

theorem halfSphereCoordinates_apply (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (y : Sphere 3) :
    halfSphereCoordinates b hb y =
      (sphereChart 3).symm (expand 3 0 b (sphereChart 3 y)) := rfl

theorem halfSphereCoordinates_symm_apply (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (y : Sphere 3) :
    (halfSphereCoordinates b hb).symm y =
      (sphereChart 3).symm (compress 3 0 b (sphereChart 3 y)) := rfl

theorem halfSphereCoordinates_source (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (halfSphereCoordinates b hb).source = halfSphere b := rfl

theorem halfSphereCoordinates_target (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (halfSphereCoordinates b hb).target = {spherePole 3}ᶜ := rfl

theorem halfSphereCoordinates_right_inv (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1)
    {y : Sphere 3} (hy : y ≠ spherePole 3) :
    halfSphereCoordinates b hb ((halfSphereCoordinates b hb).symm y) = y :=
  (halfSphereCoordinates b hb).right_inv hy

theorem halfSphereCoordinates_left_inv (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1)
    {y : Sphere 3} (hy : y ∈ halfSphere b) :
    (halfSphereCoordinates b hb).symm (halfSphereCoordinates b hb y) = y :=
  (halfSphereCoordinates b hb).left_inv hy

theorem halfSphere_disjoint : Disjoint (halfSphere 0) (halfSphere 1) := by
  apply disjoint_left.mpr
  intro y hy₀ hy₁
  have hl := hy₀.2.2.2
  have hr := hy₁.2.2.1
  norm_num at hl hr
  exact lt_asymm hl hr

theorem mem_halfSphere_zero {y : Sphere 3} (hy : y ≠ spherePole 3)
    (ht : sphereChart 3 y 0 < 1 / 2) : y ∈ halfSphere 0 := by
  have hs : y ∈ (sphereChart 3).source := hy
  have hc := (sphereChart 3).map_source hs
  refine ⟨hs, hc, ?_, ?_⟩
  · simpa only [zero_div] using (hc 0).1
  · simpa only [zero_add] using ht

theorem mem_halfSphere_one {y : Sphere 3} (hy : y ≠ spherePole 3)
    (ht : 1 / 2 < sphereChart 3 y 0) : y ∈ halfSphere 1 := by
  have hs : y ∈ (sphereChart 3).source := hy
  have hc := (sphereChart 3).map_source hs
  refine ⟨hs, hc, ht, ?_⟩
  simpa only [one_add_one_eq_two, div_self (two_ne_zero : (2 : ℝ) ≠ 0)] using (hc 0).2

theorem halfSphere_cover (y : Sphere 3) :
    y = spherePole 3 ∨ sphereChart 3 y 0 = 1 / 2 ∨ y ∈ halfSphere 0 ∨ y ∈ halfSphere 1 := by
  by_cases hy : y = spherePole 3
  · exact Or.inl hy
  · rcases lt_trichotomy (sphereChart 3 y 0) (1 / 2) with h | h | h
    · exact Or.inr (Or.inr (Or.inl (mem_halfSphere_zero hy h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (mem_halfSphere_one hy h)))

theorem bijective_mfderiv_halfSphereCoordinates (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1)
    (y : Sphere 3) (hy : y ∈ halfSphere b) :
    Bijective (mfderiv (𝓡 3) (𝓡 3) (halfSphereCoordinates b hb) y) := by
  have hloc : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (halfSphereCoordinates b hb) y :=
    ⟨halfSphereCoordinates b hb, hy, fun _ _ ↦ rfl⟩
  exact (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective

end NoExoticSixSphere.SmoothCube
