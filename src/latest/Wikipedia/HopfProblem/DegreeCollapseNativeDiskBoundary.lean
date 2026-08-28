import Wikipedia.HopfProblem.DegreeCollapseNativeSublevelDisk
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The actual smooth boundary transition between native disk neighborhoods

The inverse of each partial chart is defined and smooth on the entire
common boundary. Composing the actual charts therefore gives a genuine
diffeomorphism of standard spheres, with the exact boundary-matching
identity. No extension of this diffeomorphism across a disk is asserted.
-/

noncomputable section

open Set Function Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {a b : ℝ} {n : ℕ}

theorem NativeSublevelDisk.mem_target_of_level (d : NativeSublevelDisk n E f a)
    {y : M} (hy : f y = a) : y ∈ d.chart.target := by
  have hh : y ∈ d.chart '' sphere (0 : Hemisphere.Ambient n) 1 := by
    rw [d.image_sphere]
    exact hy
  obtain ⟨v, hv, rfl⟩ := hh
  exact d.chart.map_source' (d.closedBall_source (sphere_subset_closedBall hv))

theorem NativeSublevelDisk.inverse_mem_sphere_of_level (d : NativeSublevelDisk n E f a)
    {y : M} (hy : f y = a) : d.chart.symm y ∈ sphere (0 : Hemisphere.Ambient n) 1 := by
  have hh : y ∈ d.chart '' sphere (0 : Hemisphere.Ambient n) 1 := by
    rw [d.image_sphere]
    exact hy
  obtain ⟨v, hv, rfl⟩ := hh
  have heq : d.chart.symm (d.chart v) = v :=
    d.chart.left_inv' (d.closedBall_source (sphere_subset_closedBall hv))
  rw [heq]
  exact hv

def nativeBoundaryTransition (L : NativeSublevelDisk (n + 1) E f a)
    (R : NativeSublevelDisk (n + 1) E g b)
    (hlevel : {x : M | f x = a} = {x : M | g x = b}) :
    Diffeomorph (𝓡 n) (𝓡 n) (Hemisphere.Sphere n) (Hemisphere.Sphere n) ∞ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hL (v : Hemisphere.Sphere n) : g (L.chart v.val) = b := by
    have hh : L.chart v.val ∈ {x : M | f x = a} := by
      rw [← L.image_sphere]
      exact ⟨v.val, v.property, rfl⟩
    rwa [hlevel] at hh
  have hR (v : Hemisphere.Sphere n) : f (R.chart v.val) = a := by
    have hh : R.chart v.val ∈ {x : M | g x = b} := by
      rw [← R.image_sphere]
      exact ⟨v.val, v.property, rfl⟩
    rwa [← hlevel] at hh
  have hF (v : Hemisphere.Sphere n) :
      R.chart.symm (L.chart v.val) ∈ sphere (0 : Hemisphere.Ambient (n + 1)) 1 :=
    R.inverse_mem_sphere_of_level (hL v)
  have hG (v : Hemisphere.Sphere n) :
      L.chart.symm (R.chart v.val) ∈ sphere (0 : Hemisphere.Ambient (n + 1)) 1 :=
    L.inverse_mem_sphere_of_level (hR v)
  have hLs : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (fun v : Hemisphere.Sphere n => L.chart v.val) :=
    L.chart.contMDiffOn_toFun.comp_contMDiff (contMDiff_coe_sphere (n := n))
      (fun v => L.closedBall_source (sphere_subset_closedBall v.property))
  have hRs : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (fun v : Hemisphere.Sphere n => R.chart v.val) :=
    R.chart.contMDiffOn_toFun.comp_contMDiff (contMDiff_coe_sphere (n := n))
      (fun v => R.closedBall_source (sphere_subset_closedBall v.property))
  have hFs : ContMDiff (𝓡 n) 𝓘(ℝ, Hemisphere.Ambient (n + 1)) ∞
      (fun v : Hemisphere.Sphere n => R.chart.symm (L.chart v.val)) :=
    R.chart.contMDiffOn_invFun.comp_contMDiff hLs (fun v => R.mem_target_of_level (hL v))
  have hGs : ContMDiff (𝓡 n) 𝓘(ℝ, Hemisphere.Ambient (n + 1)) ∞
      (fun v : Hemisphere.Sphere n => L.chart.symm (R.chart v.val)) :=
    L.chart.contMDiffOn_invFun.comp_contMDiff hRs (fun v => L.mem_target_of_level (hR v))
  exact {
    toFun := fun v => ⟨R.chart.symm (L.chart v.val), hF v⟩
    invFun := fun v => ⟨L.chart.symm (R.chart v.val), hG v⟩
    left_inv := by
      intro v
      apply Subtype.ext
      change L.chart.symm (R.chart (R.chart.symm (L.chart v.val))) = v.val
      exact (congrArg (fun y => L.chart.symm y)
        (R.chart.right_inv' (R.mem_target_of_level (hL v)))).trans
          (L.chart.left_inv' (L.closedBall_source (sphere_subset_closedBall v.property)))
    right_inv := by
      intro v
      apply Subtype.ext
      change R.chart.symm (L.chart (L.chart.symm (R.chart v.val))) = v.val
      exact (congrArg (fun y => R.chart.symm y)
        (L.chart.right_inv' (L.mem_target_of_level (hR v)))).trans
          (R.chart.left_inv' (R.closedBall_source (sphere_subset_closedBall v.property)))
    contMDiff_toFun := hFs.codRestrict_sphere hF
    contMDiff_invFun := hGs.codRestrict_sphere hG }

theorem nativeBoundaryTransition_match (L : NativeSublevelDisk (n + 1) E f a)
    (R : NativeSublevelDisk (n + 1) E g b)
    (hlevel : {x : M | f x = a} = {x : M | g x = b}) (v : Hemisphere.Sphere n) :
    R.chart (nativeBoundaryTransition L R hlevel v).val = L.chart v.val := by
  have hh : g (L.chart v.val) = b := by
    have hh : L.chart v.val ∈ {x : M | f x = a} := by
      rw [← L.image_sphere]
      exact ⟨v.val, v.property, rfl⟩
    rwa [hlevel] at hh
  exact R.chart.right_inv' (R.mem_target_of_level hh)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
