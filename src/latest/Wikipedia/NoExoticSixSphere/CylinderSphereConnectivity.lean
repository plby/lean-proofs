import Wikipedia.NoExoticSixSphere.RelativeSphereConnectivity
import Wikipedia.NoExoticSixSphere.CylinderTime

/-!
# Sphere-valued cylinder contractions relative to both ends

In target dimension greater than the cylinder dimension, every sphere-valued
cylinder map with one constant value on both ends contracts relative to those
ends. Time collars permit relative smooth approximation on the boundaryless
real-time cylinder; the Hausdorff-dimension argument supplies an omitted point.
-/

open scoped Manifold ContDiff Topology
open Set Module

namespace NoExoticSixSphere

/-- Both ends of a sphere-valued cylinder can be kept fixed during a nullhomotopy above
the cylinder dimension. -/
theorem sphereCylinder_nullhomotopicRel_boundary {m n : ℕ} (hd : m + 1 < n)
    (H : C(unitInterval × Sphere m, Sphere n)) (v : Sphere n)
    (hzero : ∀ x, H (0, x) = v) (hone : ∀ x, H (1, x) = v) :
    Nonempty (H.HomotopyRel (ContinuousMap.const _ v) CylinderTime.boundary) := by
  let F := CylinderTime.realCollaredMap H
  let S : Set (ℝ × Sphere m) := {q | q.1 = 0 ∨ q.1 = 1}
  let U : Set (ℝ × Sphere m) := {q | q.1 < 1 / 3 ∨ 2 / 3 < q.1}
  have hS : IsClosed S :=
    (isClosed_eq continuous_fst continuous_const).union
      (isClosed_eq continuous_fst continuous_const)
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_fst continuous_const).union
      (isOpen_lt continuous_const continuous_fst)
  have hSU : S ⊆ U := by
    intro q hq
    rcases hq with hq | hq
    · left
      rw [hq]
      norm_num
    · right
      rw [hq]
      norm_num
  have hUnhds : U ∈ 𝓝ˢ S := mem_nhdsSet_iff_forall.mpr
    (fun q hq ↦ hUopen.mem_nhds (hSU hq))
  have hSne : S.Nonempty := by
    let x : Sphere m := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
    exact ⟨(0, x), Or.inl rfl⟩
  have hFU : ∀ q ∈ U, F q = v := by
    intro q hq
    change H (CylinderTime.collar q.1, q.2) = v
    rcases hq with hq | hq
    · rw [CylinderTime.collar_left hq.le]
      exact hzero q.2
    · rw [CylinderTime.collar_right hq.le]
      exact hone q.2
  have hFsmooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun q ↦ (F q : EuclideanSpace ℝ (Fin (n + 1)))) U :=
    contMDiffOn_const.congr (fun q hq ↦ congrArg Subtype.val (hFU q hq))
  have hdim : finrank ℝ (ℝ × EuclideanSpace ℝ (Fin m)) < n := by
    simpa only [Module.finrank_prod, finrank_self, finrank_euclideanSpace_fin, Nat.add_comm]
      using hd
  obtain ⟨G⟩ := sphereMap_nullhomotopicRel_of_dim_lt
    (I := (𝓘(ℝ, ℝ)).prod (𝓡 m)) n F v hS hSne hUnhds hFsmooth
      (fun q hq ↦ hFU q (hSU hq)) hdim
  let J : (CylinderTime.collaredMap H).HomotopyRel
      (ContinuousMap.const _ v) CylinderTime.boundary :=
    { toHomotopy := G.toHomotopy.compContinuousMap CylinderTime.inclusion
      prop' := fun t q hq ↦ G.eq_fst t (by
        change (q.1 : ℝ) = 0 ∨ (q.1 : ℝ) = 1
        rcases hq with hq | hq
        · left
          rw [hq]
          rfl
        · right
          rw [hq]
          rfl) }
  exact ⟨(CylinderTime.collarHomotopy H).trans J⟩

end NoExoticSixSphere
