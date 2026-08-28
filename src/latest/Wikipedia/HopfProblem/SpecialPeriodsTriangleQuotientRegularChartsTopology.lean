import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBasic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic

/-!
# The regular quotient inside the full triangle orbit space

The inclusion of the invariant regular domain induces an actual open embedding
of orbit quotients. Its range is precisely the complement of the two elliptic
orbits in the full quotient. No complex structure on that full quotient is used.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleGeometricAction
  triangleGeometricAction_properlyDiscontinuous triangleGeometricAction_continuous

/-- Inclusion of the regular orbit quotient into the full orbit quotient,
induced by the literal inclusion of the regular upper-half-plane points. -/
def triangleRegularToOrbit : TriangleRegularQuotient → TriangleOrbitSpace :=
  Quotient.lift (fun z : TriangleRegularPoint => triangleOrbitProjection z.val) fun x y h => by
    obtain ⟨g, hg⟩ := h
    apply (triangleOrbitProjection_eq_iff _ _).mpr
    exact ⟨g, congrArg Subtype.val hg⟩

@[simp] theorem triangleRegularToOrbit_project (z : TriangleRegularPoint) :
    triangleRegularToOrbit (triangleRegularProject z) = triangleOrbitProjection z.val := rfl

theorem triangleRegularToOrbit_continuous : Continuous triangleRegularToOrbit :=
  (triangleOrbitProjection_continuous.comp continuous_subtype_val).quotient_lift _

/-- Two regular orbits become equal in the full quotient only when they
already agree as regular orbits. -/
theorem triangleRegularToOrbit_injective : Function.Injective triangleRegularToOrbit := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp hab
  apply Quotient.sound
  exact ⟨g, Subtype.ext hg⟩

theorem triangleRegularToOrbit_isOpenMap : IsOpenMap triangleRegularToOrbit :=
  IsOpenMap.of_comp triangleRegularProject_covering.continuous
    triangleRegularProject_surjective
    (triangleOrbitProjection_isOpenMap.comp triangleRegularDomain.isOpen.isOpenMap_subtype_val)

/-- This is an open embedding for the existing quotient topologies. -/
theorem triangleRegularToOrbit_isOpenEmbedding : IsOpenEmbedding triangleRegularToOrbit :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap triangleRegularToOrbit_continuous
    triangleRegularToOrbit_injective triangleRegularToOrbit_isOpenMap

/-- The image is the image of the actual regular locus under the full orbit
projection, not an independently selected open subset. -/
theorem triangleRegularToOrbit_range :
    range triangleRegularToOrbit = triangleOrbitProjection '' triangleRegularLocus := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := triangleRegularProject_surjective y
    exact ⟨z.val, z.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨triangleRegularProject ⟨z, hz⟩, rfl⟩

/-- The regular image as an open subset of the full orbit space. -/
def triangleOrbitRegularDomain : TopologicalSpace.Opens TriangleOrbitSpace :=
  ⟨range triangleRegularToOrbit, triangleRegularToOrbit_isOpenEmbedding.isOpen_range⟩

theorem triangleOrbitRegularDomain_eq_image :
    (triangleOrbitRegularDomain : Set TriangleOrbitSpace) =
      triangleOrbitProjection '' triangleRegularLocus :=
  triangleRegularToOrbit_range

/-- Invariance of the regular locus identifies the entire inverse image of
its orbit image with the original regular locus. -/
theorem triangleOrbitProjection_mem_regularDomain_iff (z : ℍ) :
    triangleOrbitProjection z ∈ triangleOrbitRegularDomain ↔ z ∈ triangleRegularLocus := by
  change triangleOrbitProjection z ∈ range triangleRegularToOrbit ↔ _
  rw [triangleRegularToOrbit_range]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp he
    exact (triangleRegularLocus_invariant g z).mp (hg ▸ hw)
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem triangleOrbitProjection_preimage_regularDomain :
    triangleOrbitProjection ⁻¹' (triangleOrbitRegularDomain : Set TriangleOrbitSpace) =
      triangleRegularLocus :=
  Set.ext triangleOrbitProjection_mem_regularDomain_iff

/-- All full quotient points outside the regular image are exactly the two
distinguished elliptic orbits. -/
theorem triangleOrbitRegularDomain_mem_iff (x : TriangleOrbitSpace) :
    x ∈ triangleOrbitRegularDomain ↔
      x ≠ triangleOrbitCenterOne ∧ x ≠ triangleOrbitCenterTwo := by
  obtain ⟨z, rfl⟩ := triangleOrbitProjection_surjective x
  rw [triangleOrbitProjection_mem_regularDomain_iff,
    triangleRegularLocus_eq_compl_ellipticSet]
  simp only [triangleEllipticSet, mem_compl_iff, mem_union, mem_range, not_or, ne_eq,
    triangleOrbitCenterOne, triangleOrbitCenterTwo, triangleOrbitProjection_eq_iff]

theorem triangleOrbitRegularDomain_eq_compl_centers :
    (triangleOrbitRegularDomain : Set TriangleOrbitSpace) =
      ({triangleOrbitCenterOne, triangleOrbitCenterTwo} : Set TriangleOrbitSpace)ᶜ := by
  ext x
  change x ∈ triangleOrbitRegularDomain ↔
    ¬(x = triangleOrbitCenterOne ∨ x = triangleOrbitCenterTwo)
  rw [not_or]
  exact triangleOrbitRegularDomain_mem_iff x

/-- The regular quotient is homeomorphic to its actual open image in the
full quotient. Its forward map is the induced inclusion. -/
def triangleRegularOrbitHomeomorph :
    TriangleRegularQuotient ≃ₜ triangleOrbitRegularDomain :=
  triangleRegularToOrbit_isOpenEmbedding.toIsEmbedding.toHomeomorph

@[simp] theorem triangleRegularOrbitHomeomorph_val (x : TriangleRegularQuotient) :
    (triangleRegularOrbitHomeomorph x : TriangleOrbitSpace) = triangleRegularToOrbit x := rfl

@[simp] theorem triangleRegularOrbitHomeomorph_project (z : TriangleRegularPoint) :
    (triangleRegularOrbitHomeomorph (triangleRegularProject z) : TriangleOrbitSpace) =
      triangleOrbitProjection z.val := rfl

/-- The same inclusion as an open partial homeomorphism, with full source.
Its inverse is used to extend regular quotient charts into the full orbit space. -/
def triangleRegularOrbitParametrization :
    OpenPartialHomeomorph TriangleRegularQuotient TriangleOrbitSpace :=
  triangleRegularToOrbit_isOpenEmbedding.toOpenPartialHomeomorph triangleRegularToOrbit

@[simp] theorem triangleRegularOrbitParametrization_apply (x : TriangleRegularQuotient) :
    triangleRegularOrbitParametrization x = triangleRegularToOrbit x := rfl

@[simp] theorem triangleRegularOrbitParametrization_source :
    triangleRegularOrbitParametrization.source = univ := rfl

@[simp] theorem triangleRegularOrbitParametrization_target :
    triangleRegularOrbitParametrization.target =
      (triangleOrbitRegularDomain : Set TriangleOrbitSpace) := by
  simp [triangleRegularOrbitParametrization, triangleOrbitRegularDomain]

@[simp] theorem triangleRegularOrbitParametrization_symm_apply
    (x : TriangleRegularQuotient) :
    triangleRegularOrbitParametrization.symm (triangleRegularToOrbit x) = x :=
  triangleRegularOrbitParametrization.left_inv (mem_univ x)

end Wikipedia.HopfProblem.SpecialPeriods
