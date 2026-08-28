import Wikipedia.NoExoticSixSphere.SphereFiniteHomotopyComparison
import Wikipedia.NoExoticSixSphere.SemicircleSuspensionCoordinates

/-!
# Ordinary suspension homotopies give genuine fixed-endpoint path homotopies

Correct the ordinary homotopy at both suspension poles without changing
its endpoint maps. Pulling back along the literal cosine latitudes and
currying then gives a homotopy in the native fixed-endpoint path space.
No identification of arbitrarily chosen homotopy-group operations is used.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.SemicircleSuspension

variable {m n : ℕ}

theorem pathMap_homotopic_of_relative_suspension
    {f g : C(Sphere m, Sphere n)}
    (H : (SphereMapSuspension.map f).HomotopyRel (SphereMapSuspension.map g)
      {south m, north m}) : (pathMap f).Homotopic (pathMap g) := by
  let K : (PathFamilies.uncurry (pathMap f)).HomotopyRel
      (PathFamilies.uncurry (pathMap g))
      {z : I × Sphere m | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ (∅ : Set (Sphere m))} := {
    toFun := fun z ↦ H (z.1, meridianMap m z.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk ((meridianMap m).continuous.comp continuous_snd))
    map_zero_left := by
      intro z
      exact (H.apply_zero (meridianMap m z)).trans (pathMap_apply f z.2 z.1).symm
    map_one_left := by
      intro z
      exact (H.apply_one (meridianMap m z)).trans (pathMap_apply g z.2 z.1).symm
    prop' := by
      intro r z hz
      rcases z with ⟨t, x⟩
      have hmem : meridianMap m (t, x) ∈ ({south m, north m} : Set (Sphere (m + 1))) := by
        rcases hz with ht | ht | hx
        · change t = 0 at ht
          subst t
          rw [meridianMap_zero]
          exact mem_insert _ _
        · change t = 1 at ht
          subst t
          rw [meridianMap_one]
          exact mem_insert_of_mem _ (mem_singleton _)
        · exact hx.elim
      exact (H.eq_fst r hmem).trans (pathMap_apply f x t).symm }
  exact ContinuousMap.homotopicRel_empty.mp ⟨PathFamilies.curryHomotopy K⟩

theorem pathMap_homotopic_of_suspension [SimplyConnectedSpace (Sphere (n + 1))]
    {f g : C(Sphere m, Sphere n)}
    (H : (SphereMapSuspension.map f).Homotopic (SphereMapSuspension.map g)) :
    (pathMap f).Homotopic (pathMap g) := by
  obtain ⟨H⟩ := H
  have hbase : EqOn (SphereMapSuspension.map f) (SphereMapSuspension.map g)
      {south m, north m} := by
    intro x hx
    rcases mem_insert_iff.mp hx with hx | hx
    · subst x
      rw [suspension_south, suspension_south]
    · have hx' : x = north m := mem_singleton_iff.mp hx
      subst x
      rw [suspension_north, suspension_north]
  obtain ⟨K⟩ := sphere_homotopicRel_finite_of_homotopic {south m, north m}
    ((finite_singleton (north m)).insert (south m)) hbase H
  exact pathMap_homotopic_of_relative_suspension K

end NoExoticSixSphere.SemicircleSuspension
