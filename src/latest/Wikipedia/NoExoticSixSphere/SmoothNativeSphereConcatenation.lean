import Wikipedia.NoExoticSixSphere.NativeSphereConcatenationCoordinates
import Wikipedia.NoExoticSixSphere.SpherePinchTransversality

/-!
# Native smoothness and transversality of cubical sphere concatenation

Local constancy near the pole protects the seam and the collapsed boundary.
On the two remaining open pieces the exact branch formulas give smoothness
and the native chain rule. Each branch differential is invertible, so
transversality of the input pairs transfers to their actual concatenation.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] {m : M}

theorem contMDiff_concatenate (f g : BasedMap 3 M m)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f.val) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g.val)
    {U : Set (Sphere 3)} (hU : IsOpen U) (hb : spherePole 3 ∈ U)
    (hfU : EqOn f.val (fun _ ↦ m) U) (hgU : EqOn g.val (fun _ ↦ m) U) :
    ContMDiff (𝓡 3) (𝓡 6) ∞ (concatenate f g).val := by
  intro y
  by_cases hy : y = spherePole 3
  · subst y
    exact contMDiffAt_const.congr_of_eventuallyEq
      (concatenate_eventuallyEq_const f g hU hb hfU hgU _ leftCollapse_pole rightCollapse_pole)
  · rcases lt_trichotomy (sphereChart 3 y 0) (1 / 2) with hl | hs | hr
    · have hL := mem_halfSphere_zero hy hl
      have hc := (halfSphereCoordinates 0 (by constructor <;> norm_num)).contMDiffOn_toFun
      have hcat := hc.contMDiffAt
        ((halfSphereCoordinates 0 (by constructor <;> norm_num)).open_source.mem_nhds hL)
      exact (hf.contMDiffAt.comp y hcat).congr_of_eventuallyEq
        (concatenate_eventuallyEq_left f g y hL)
    · have hsides := collapse_coordinate_seam y hy hs
      exact contMDiffAt_const.congr_of_eventuallyEq
        (concatenate_eventuallyEq_const f g hU hb hfU hgU y hsides.1 hsides.2)
    · have hR := mem_halfSphere_one hy hr
      have hc := (halfSphereCoordinates 1 (by constructor <;> norm_num)).contMDiffOn_toFun
      have hcat := hc.contMDiffAt
        ((halfSphereCoordinates 1 (by constructor <;> norm_num)).open_source.mem_nhds hR)
      exact (hg.contMDiffAt.comp y hcat).congr_of_eventuallyEq
        (concatenate_eventuallyEq_right f g y hR)

theorem mfderiv_concatenate_left (f g : BasedMap 3 M m)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f.val) (y : Sphere 3) (hy : y ∈ halfSphere 0) :
    (mfderiv (𝓡 3) (𝓡 6) (concatenate f g).val y : Vector 3 →L[ℝ] Vector 6) =
      (mfderiv (𝓡 3) (𝓡 6) f.val
        (halfSphereCoordinates 0 (by constructor <;> norm_num) y) :
          Vector 3 →L[ℝ] Vector 6).comp
        (mfderiv (𝓡 3) (𝓡 3) (halfSphereCoordinates 0 (by constructor <;> norm_num)) y :
          Vector 3 →L[ℝ] Vector 3) := by
  have hc := (halfSphereCoordinates 0 (by constructor <;> norm_num)).contMDiffOn_toFun
  have hcat := hc.contMDiffAt
    ((halfSphereCoordinates 0 (by constructor <;> norm_num)).open_source.mem_nhds hy)
  rw [(concatenate_eventuallyEq_left f g y hy).mfderiv_eq]
  exact mfderiv_comp y (hf.mdifferentiableAt (by simp)) (hcat.mdifferentiableAt (by simp))

theorem mfderiv_concatenate_right (f g : BasedMap 3 M m)
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g.val) (y : Sphere 3) (hy : y ∈ halfSphere 1) :
    (mfderiv (𝓡 3) (𝓡 6) (concatenate f g).val y : Vector 3 →L[ℝ] Vector 6) =
      (mfderiv (𝓡 3) (𝓡 6) g.val
        (halfSphereCoordinates 1 (by constructor <;> norm_num) y) :
          Vector 3 →L[ℝ] Vector 6).comp
        (mfderiv (𝓡 3) (𝓡 3) (halfSphereCoordinates 1 (by constructor <;> norm_num)) y :
          Vector 3 →L[ℝ] Vector 3) := by
  have hc := (halfSphereCoordinates 1 (by constructor <;> norm_num)).contMDiffOn_toFun
  have hcat := hc.contMDiffAt
    ((halfSphereCoordinates 1 (by constructor <;> norm_num)).open_source.mem_nhds hy)
  rw [(concatenate_eventuallyEq_right f g y hy).mfderiv_eq]
  exact mfderiv_comp y (hg.mdifferentiableAt (by simp)) (hcat.mdifferentiableAt (by simp))

theorem concatenate_intersection_off_seam (f g : BasedMap 3 M m) (k : Sphere 3 → M)
    (hm : m ∉ range k) (y z : Sphere 3) (hyz : (concatenate f g).val y = k z) :
    y ≠ spherePole 3 ∧ sphereChart 3 y 0 ≠ 1 / 2 := by
  have hy : y ≠ spherePole 3 := by
    intro h
    subst y
    exact hm ⟨z, hyz.symm.trans (concatenate f g).property⟩
  refine ⟨hy, ?_⟩
  intro ht
  exact hm ⟨z, hyz.symm.trans (concatenate_coordinate_seam f g y hy ht)⟩

theorem transverse_concatenate (f g : BasedMap 3 M m) (k : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f.val) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g.val)
    (hm : m ∉ range k)
    (hfk : ∀ y z, f.val y = k z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f.val y).coprod (mfderiv (𝓡 3) (𝓡 6) k z)))
    (hgk : ∀ y z, g.val y = k z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g.val y).coprod (mfderiv (𝓡 3) (𝓡 6) k z))) :
    ∀ y z, (concatenate f g).val y = k z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (concatenate f g).val y).coprod
        (mfderiv (𝓡 3) (𝓡 6) k z)) := by
  intro y z hyz
  have hs := concatenate_intersection_off_seam f g k hm y z hyz
  change Surjective
    ((mfderiv (𝓡 3) (𝓡 6) (concatenate f g).val y : Vector 3 →L[ℝ] Vector 6).coprod
      (mfderiv (𝓡 3) (𝓡 6) k z : Vector 3 →L[ℝ] Vector 6))
  rcases lt_or_gt_of_ne hs.2 with hl | hr
  · have hL := mem_halfSphere_zero hs.1 hl
    have hfy := (concatenate_left f g y hL).symm.trans hyz
    rw [mfderiv_concatenate_left f g hf y hL]
    exact SphereFold.surjective_coprod_comp_left _ _ _
      (bijective_mfderiv_halfSphereCoordinates 0 (by constructor <;> norm_num) y hL).2
      (hfk _ z hfy)
  · have hR := mem_halfSphere_one hs.1 hr
    have hgy := (concatenate_right f g y hR).symm.trans hyz
    rw [mfderiv_concatenate_right f g hg y hR]
    exact SphereFold.surjective_coprod_comp_left _ _ _
      (bijective_mfderiv_halfSphereCoordinates 1 (by constructor <;> norm_num) y hR).2
      (hgk _ z hgy)

end NoExoticSixSphere.SmoothCube
