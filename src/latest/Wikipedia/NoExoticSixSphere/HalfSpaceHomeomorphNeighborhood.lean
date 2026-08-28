import Wikipedia.NoExoticSixSphere.ProductHalfSpaceModel
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Local half-space preservation by the inverse homeomorphism

If an ambient homeomorphism sends the boundary plane to the boundary plane
and the positive side to the positive side near a boundary point, its inverse
preserves the closed positive side on a target neighborhood. Connectedness of
an open half-ball fixes the inverse's sign, and closure supplies its boundary.
-/

open Set Function Filter Metric
open scoped Topology

namespace NoExoticSixSphere.ProductHalfSpace

variable {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

theorem closure_positive_halfSpace :
    closure {z : ℝ × B | 0 < z.1} = {z | 0 ≤ z.1} := by
  change closure ((Prod.fst : ℝ × B → ℝ) ⁻¹' Ioi 0) = Prod.fst ⁻¹' Ici 0
  rw [← isOpenMap_fst.preimage_closure_eq_closure_preimage continuous_fst, closure_Ioi]

theorem exists_inverse_halfSpace_neighborhood
    (G : (ℝ × B) ≃ₜ (ℝ × C)) {x : ℝ × B} (hx : x.1 = 0)
    {U : Set (ℝ × B)} (hU : IsOpen U) (hxU : x ∈ U)
    (hz : ∀ z ∈ U, z.1 = 0 → (G z).1 = 0)
    (hp : ∀ z ∈ U, 0 < z.1 → 0 < (G z).1) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball (G x) r, 0 ≤ y.1 →
      G.symm y ∈ U ∧ 0 ≤ (G.symm y).1 := by
  have himage : G '' U ∈ 𝓝 (G x) :=
    (G.isOpenMap U hU).mem_nhds (mem_image_of_mem G hxU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himage
  have hinv : ∀ y ∈ ball (G x) r, G.symm y ∈ U := by
    intro y hy
    obtain ⟨z, hzU, rfl⟩ := hball hy
    simpa only [G.symm_apply_apply] using hzU
  let V : Set (ℝ × C) := ball (G x) r ∩ {y | 0 < y.1}
  have hV : IsPreconnected V :=
    ((convex_ball (G x) r).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ C))).isPreconnected
  have hne : ∀ y ∈ V, (G.symm y).1 ≠ 0 := by
    intro y hy he
    have hz' := hz (G.symm y) (hinv y hy.1) he
    rw [G.apply_symm_apply] at hz'
    exact (ne_of_gt hy.2) hz'
  have hxcl : x ∈ closure {z : ℝ × B | 0 < z.1} := by
    rw [closure_positive_halfSpace]
    exact le_of_eq hx.symm
  have hnear : U ∩ G ⁻¹' ball (G x) r ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hxU) (G.continuous.continuousAt (ball_mem_nhds (G x) hr))
  obtain ⟨z, hznear, hzpos⟩ := mem_closure_iff_nhds.mp hxcl _ hnear
  have hsome : ∃ y ∈ V, 0 < (G.symm y).1 := by
    refine ⟨G z, ⟨hznear.2, hp z hznear.1 hzpos⟩, ?_⟩
    rw [G.symm_apply_apply]
    exact hzpos
  have hc : Continuous (fun y : ℝ × C ↦ (G.symm y).1) :=
    continuous_fst.comp G.symm.continuous
  have hpos : ∀ y ∈ V, 0 < (G.symm y).1 :=
    fun _ hy ↦ hV.lt_of_ne hc.continuousOn hne hsome hy
  have hclosed : IsClosed {y : ℝ × C | 0 ≤ (G.symm y).1} :=
    isClosed_le continuous_const hc
  have hclosure : closure V ⊆ {y : ℝ × C | 0 ≤ (G.symm y).1} :=
    hclosed.closure_subset_iff.mpr (fun y hy ↦ (hpos y hy).le)
  refine ⟨r, hr, fun y hy hy0 ↦ ⟨hinv y hy, ?_⟩⟩
  apply hclosure
  apply isOpen_ball.inter_closure
  exact ⟨hy, by rw [closure_positive_halfSpace]; exact hy0⟩

end NoExoticSixSphere.ProductHalfSpace
