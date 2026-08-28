import Wikipedia.NoExoticSixSphere.Hemisphere

/-!
# Antipodal hemispheres and their actual equator

The equator is identified with the unit sphere in the orthogonal hyperplane,
not with an abstractly substituted sphere. Its two inclusions provide the
common domain for the hemisphere change-of-frame map.
-/

open Set

namespace NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The antipodal unit vector. -/
def antipode (v : UnitSphere E) : UnitSphere E :=
  ⟨-(v : E), by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using ClosedHemisphere.unit_norm v⟩

/-- The equatorial points orthogonal to a given pole. -/
def equator (v : UnitSphere E) : Set (UnitSphere E) := {x | inner ℝ (v : E) (x : E) = 0}

/-- The actual common boundary of the antipodal hemispheres. -/
abbrev Equator (v : UnitSphere E) := ↥(equator v)

/-- The actual equator is a closed subset of the sphere. -/
theorem isClosed_equator (v : UnitSphere E) : IsClosed (equator v) :=
  isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const

/-- In finite dimensions the equator is compact. -/
instance [FiniteDimensional ℝ E] (v : UnitSphere E) : CompactSpace (Equator v) :=
  isCompact_iff_compactSpace.mp (isClosed_equator v).isCompact

/-- The two antipodal closed hemispheres cover the sphere. -/
theorem hemispheres_cover (v : UnitSphere E) :
    closedHemisphere v ∪ closedHemisphere (antipode v) = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases h : 0 ≤ inner ℝ (v : E) (x : E)
  · exact Or.inl h
  · right
    change 0 ≤ inner ℝ (-(v : E)) (x : E)
    rw [inner_neg_left]
    linarith

/-- Their intersection is precisely the orthogonal equator. -/
theorem hemispheres_inter (v : UnitSphere E) :
    closedHemisphere v ∩ closedHemisphere (antipode v) = equator v := by
  ext x
  change (0 ≤ inner ℝ (v : E) (x : E) ∧ 0 ≤ inner ℝ (-(v : E)) (x : E)) ↔
    inner ℝ (v : E) (x : E) = 0
  rw [inner_neg_left]
  constructor
  · rintro ⟨h, h'⟩
    linarith
  · intro h
    simp only [h, neg_zero, le_refl, and_self]

/-- Include an equatorial point in the northern hemisphere. -/
def equatorNorth (v : UnitSphere E) (x : Equator v) : ClosedHemisphere v :=
  ⟨x.1, le_of_eq x.2.symm⟩

/-- Include the same equatorial point in the southern hemisphere. -/
def equatorSouth (v : UnitSphere E) (x : Equator v) : ClosedHemisphere (antipode v) :=
  ⟨x.1, by
    change 0 ≤ inner ℝ (-(v : E)) (x.1 : E)
    rw [inner_neg_left, x.2]
    simp only [neg_zero, le_refl]⟩

/-- The northern equator inclusion is continuous. -/
theorem continuous_equatorNorth (v : UnitSphere E) : Continuous (equatorNorth v) :=
  continuous_subtype_val.subtype_mk _

/-- The southern equator inclusion is continuous. -/
theorem continuous_equatorSouth (v : UnitSphere E) : Continuous (equatorSouth v) :=
  continuous_subtype_val.subtype_mk _

/-- Reversing the pole does not change the actual equatorial points. -/
noncomputable def equatorAntipode (v : UnitSphere E) : Equator v ≃ₜ Equator (antipode v) :=
  Homeomorph.setCongr (by
    ext x
    change inner ℝ (v : E) (x : E) = 0 ↔ inner ℝ (-(v : E)) (x : E) = 0
    rw [inner_neg_left, neg_eq_zero])

/-- The linear hyperplane orthogonal to the pole. -/
noncomputable def equatorialSpace (v : UnitSphere E) : Submodule ℝ E :=
  (innerSL ℝ (v : E)).ker

/-- The equator is homeomorphic to the unit sphere of its actual orthogonal hyperplane. -/
noncomputable def equatorHomeomorph (v : UnitSphere E) :
    Equator v ≃ₜ UnitSphere (equatorialSpace v) where
  toFun x := ⟨⟨(x.1 : E), x.2⟩, by
    rw [Metric.mem_sphere, dist_zero_right]
    change ‖(x.1 : E)‖ = 1
    exact ClosedHemisphere.unit_norm x.1⟩
  invFun x := ⟨⟨(x.1 : E), by
    rw [Metric.mem_sphere, dist_zero_right]
    change ‖(x.1 : equatorialSpace v)‖ = 1
    exact ClosedHemisphere.unit_norm x⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h : Continuous (fun x : Equator v ↦ (x.1 : E)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h.subtype_mk _).subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun x : UnitSphere (equatorialSpace v) ↦ (x.1 : E)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h.subtype_mk _).subtype_mk _

end NoExoticSixSphere
