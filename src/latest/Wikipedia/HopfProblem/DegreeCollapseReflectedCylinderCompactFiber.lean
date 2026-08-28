import Wikipedia.HopfProblem.DegreeCollapseReflectedCylinderRegularity

/-!
# The reflected regular fiber is compact and retains the original half

The omitted right-end fiber confines the double to the reflected open time
interval. Its nonnegative half is homeomorphic to the actual original slab,
with the exact original time and sphere point. No original nullhomotopy or
filling is assumed to exist without the supplied cylinder data.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b)

include hmiss in
theorem time_mem_Ioo_of_fiber {p : ℝ × Sphere m} (hp : map d p = b) :
    p.1 ∈ Ioo (-1 : ℝ) 1 := by
  have ha : |p.1| < 1 := by
    by_contra hn
    exact hmiss p.2 ((map_outside d (le_of_not_gt hn) p.2).symm.trans hp)
  exact abs_lt.mp ha

include hmiss in
theorem isCompact_fiber : IsCompact {p : ℝ × Sphere m | map d p = b} := by
  have hc : IsClosed {p : ℝ × Sphere m | map d p = b} :=
    isClosed_eq (map d).continuous continuous_const
  have hbox : IsCompact (Icc (-1 : ℝ) 1 ×ˢ (univ : Set (Sphere m))) :=
    isCompact_Icc.prod isCompact_univ
  apply hbox.of_isClosed_subset hc
  intro p hp
  have ht := time_mem_Ioo_of_fiber d hmiss hp
  exact ⟨⟨ht.1.le, ht.2.le⟩, mem_univ _⟩

include hmiss in
theorem compactSpace_fiber : CompactSpace {p : ℝ × Sphere m // map d p = b} :=
  isCompact_iff_compactSpace.mp (isCompact_fiber d hmiss)

abbrev NonnegativeHalf := {p : {p : ℝ × Sphere m // map d p = b} // 0 ≤ p.val.1}

def originalHalfHomeomorph : CylinderFiberSlab.slab d.map b 0 1 ≃ₜ NonnegativeHalf d where
  toFun p := ⟨⟨p.val.val, (map_original d p.property p.val.val.2).trans p.val.property⟩,
    p.property.1⟩
  invFun p :=
    let ht : p.val.val.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨p.property, (time_mem_Ioo_of_fiber d hmiss p.val.property).2.le⟩
    ⟨⟨p.val.val, (map_original d ht p.val.val.2).symm.trans p.val.property⟩, ht⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem originalHalfHomeomorph_point (p : CylinderFiberSlab.slab d.map b 0 1) :
    (originalHalfHomeomorph d hmiss p).val.val = p.val.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
