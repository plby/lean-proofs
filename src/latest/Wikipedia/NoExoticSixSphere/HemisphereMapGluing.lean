import Wikipedia.NoExoticSixSphere.Equator
import Mathlib.Topology.ContinuousOn

/-!
# Gluing maps across the closed hemisphere cover

The maps are defined on the actual hemisphere subtypes and must agree
exactly on their common equator.
-/

open Set

namespace NoExoticSixSphere

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y]

theorem exists_glued_hemisphereMap (v : UnitSphere E)
    (a : C(ClosedHemisphere v, Y)) (b : C(ClosedHemisphere (antipode v), Y))
    (hab : ∀ x : Equator v, a (equatorNorth v x) = b (equatorSouth v x)) :
    ∃ f : C(UnitSphere E, Y),
      (∀ x : ClosedHemisphere v, f x.1 = a x) ∧
      (∀ x : ClosedHemisphere (antipode v), f x.1 = b x) := by
  classical
  have hS (x : UnitSphere E) (hx : x ∉ closedHemisphere v) :
      x ∈ closedHemisphere (antipode v) := by
    have hm : x ∈ closedHemisphere v ∪ closedHemisphere (antipode v) := by
      rw [hemispheres_cover]
      exact mem_univ x
    exact hm.resolve_left hx
  let f : UnitSphere E → Y := fun x ↦
    if hx : x ∈ closedHemisphere v then a ⟨x, hx⟩ else b ⟨x, hS x hx⟩
  have hN (x : ClosedHemisphere v) : f x.1 = a x := by
    simp only [f, dif_pos x.2]
  have hB (x : ClosedHemisphere (antipode v)) : f x.1 = b x := by
    by_cases hx : x.1 ∈ closedHemisphere v
    · simp only [f, dif_pos hx]
      have he : x.1 ∈ equator v := by
        rw [← hemispheres_inter]
        exact ⟨hx, x.2⟩
      exact hab ⟨x.1, he⟩
    · simp only [f, dif_neg hx]
  have hcN : ContinuousOn f (closedHemisphere v) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (closedHemisphere v).domRestrict f = a := funext hN
    rw [he]
    exact a.continuous
  have hcS : ContinuousOn f (closedHemisphere (antipode v)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (closedHemisphere (antipode v)).domRestrict f = b := funext hB
    rw [he]
    exact b.continuous
  refine ⟨⟨f, ?_⟩, hN, hB⟩
  exact continuousOn_univ.mp ((hemispheres_cover v) ▸
    hcN.union_of_isClosed hcS (ClosedHemisphere.isClosed v)
      (ClosedHemisphere.isClosed (antipode v)))

end NoExoticSixSphere
