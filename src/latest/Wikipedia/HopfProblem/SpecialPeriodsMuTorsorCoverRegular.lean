import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRegularCharts

/-! # Actual regular sheets for the period torsor cover

The sheets are the targets of the chosen local inverses of the genuine
regular triangle covering, viewed as open subsets of the original upper
half-plane.  Their returning subgroup is trivial.  Their images under the
actual full orbit projection cover exactly the regular orbit domain.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Cover

attribute [local instance] triangleGeometricAction

/-- The chosen lift of a point of the actual regular orbit quotient. -/
def regularRepresentative (x : TriangleRegularQuotient) : TriangleRegularPoint :=
  CoveringQuotient.representative triangleRegularProject_covering x

@[simp] theorem regularRepresentative_project (x : TriangleRegularQuotient) :
    triangleRegularProject (regularRepresentative x) = x :=
  CoveringQuotient.project_representative triangleRegularProject_covering x

/-- The actual local covering inverse through the chosen regular lift. -/
def regularLift (x : TriangleRegularQuotient) :
    OpenPartialHomeomorph TriangleRegularQuotient TriangleRegularPoint :=
  CoveringQuotient.localInverse triangleRegularProject_covering (regularRepresentative x)

@[simp] theorem regularLift_symm (x : TriangleRegularQuotient) :
    (regularLift x).symm = triangleRegularProject :=
  CoveringQuotient.localInverse_symm triangleRegularProject_covering (regularRepresentative x)

theorem regularRepresentative_mem_target (x : TriangleRegularQuotient) :
    regularRepresentative x ∈ (regularLift x).target :=
  triangleRegularProject_covering.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target

theorem regularLift_self_mem_source (x : TriangleRegularQuotient) :
    x ∈ (regularLift x).source := by
  have h := (regularLift x).map_target (regularRepresentative_mem_target x)
  simpa only [regularLift_symm, regularRepresentative_project] using h

@[simp] theorem regularLift_apply_self (x : TriangleRegularQuotient) :
    regularLift x x = regularRepresentative x := by
  have h := (regularLift x).right_inv (regularRepresentative_mem_target x)
  simpa only [regularLift_symm, regularRepresentative_project] using h

/-- A regular sheet is literally the target of the local covering inverse,
included into the original upper half-plane. -/
def regularSheet (x : TriangleRegularQuotient) : TopologicalSpace.Opens ℍ :=
  ⟨Subtype.val '' (regularLift x).target,
    triangleRegularDomain.isOpen.isOpenMap_subtype_val _ (regularLift x).open_target⟩

@[simp] theorem regularSheet_coe (x : TriangleRegularQuotient) :
    (regularSheet x : Set ℍ) = Subtype.val '' (regularLift x).target := rfl

theorem regularSheet_subset_regularLocus (x : TriangleRegularQuotient) :
    (regularSheet x : Set ℍ) ⊆ triangleRegularLocus := by
  rintro z ⟨a, ha, rfl⟩
  exact a.property

theorem regularRepresentative_mem_sheet (x : TriangleRegularQuotient) :
    (regularRepresentative x).val ∈ regularSheet x :=
  ⟨regularRepresentative x, regularRepresentative_mem_target x, rfl⟩

theorem regularSheet_nonempty (x : TriangleRegularQuotient) :
    (regularSheet x : Set ℍ).Nonempty :=
  ⟨(regularRepresentative x).val, regularRepresentative_mem_sheet x⟩

/-- No nonidentity triangle element returns any point of a regular sheet
to that sheet.  This follows from covering-sheet injectivity and freeness
on the actual regular locus. -/
theorem regularSheet_no_return (x : TriangleRegularQuotient) (g : TriangleGroup)
    (hg : ((triangleGeometricRepresentation g '' (regularSheet x : Set ℍ)) ∩
      regularSheet x).Nonempty) : g = 1 := by
  rcases hg with ⟨z, ⟨w, ⟨a, ha, rfl⟩, hga⟩, ⟨b, hb, rfl⟩⟩
  have hab : g • a = b := Subtype.ext hga
  have hproj : triangleRegularProject b = triangleRegularProject a := by
    rw [← hab]
    exact triangleRegularProject_covering.map_smul g
  have hba : b = a := (regularLift x).symm.injOn hb ha (by
    simpa only [regularLift_symm] using hproj)
  exact (mem_triangleRegularLocus_iff a.val).mp a.property g
    (congrArg Subtype.val (hab.trans hba))

/-- The same no-return assertion written with the genuine geometric action. -/
theorem regularSheet_smul_no_return (x : TriangleRegularQuotient) (g : TriangleGroup)
    (hg : (((fun z : ℍ => g • z) '' (regularSheet x : Set ℍ)) ∩
      regularSheet x).Nonempty) : g = 1 :=
  regularSheet_no_return x g hg

@[simp] theorem regularRepresentative_orbitProjection (x : TriangleRegularQuotient) :
    triangleOrbitProjection (regularRepresentative x).val = triangleRegularToOrbit x := by
  rw [← triangleRegularToOrbit_project, regularRepresentative_project]

/-- The image of the sheet under the actual full orbit projection. -/
def regularImage (x : TriangleRegularQuotient) : TopologicalSpace.Opens TriangleOrbitSpace :=
  ⟨triangleOrbitProjection '' (regularSheet x : Set ℍ),
    triangleOrbitProjection_isOpenMap _ (regularSheet x).isOpen⟩

@[simp] theorem regularImage_coe (x : TriangleRegularQuotient) :
    (regularImage x : Set TriangleOrbitSpace) =
      triangleOrbitProjection '' (regularSheet x : Set ℍ) := rfl

theorem regularImage_subset_regularDomain (x : TriangleRegularQuotient) :
    (regularImage x : Set TriangleOrbitSpace) ⊆ triangleOrbitRegularDomain := by
  rintro y ⟨z, hz, rfl⟩
  exact (triangleOrbitProjection_mem_regularDomain_iff z).mpr
    (regularSheet_subset_regularLocus x hz)

theorem regularImage_mem (x : TriangleRegularQuotient) :
    triangleRegularToOrbit x ∈ regularImage x :=
  ⟨(regularRepresentative x).val, regularRepresentative_mem_sheet x,
    regularRepresentative_orbitProjection x⟩

theorem regularImage_eq_localInverse_source (x : TriangleRegularQuotient) :
    (regularImage x : Set TriangleOrbitSpace) =
      triangleRegularToOrbit '' (regularLift x).source := by
  ext y
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨triangleRegularProject a, ?_, triangleRegularToOrbit_project a⟩
    simpa only [regularLift_symm] using (regularLift x).map_target ha
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(regularLift x u).val,
      ⟨regularLift x u, (regularLift x).map_source hu, rfl⟩, ?_⟩
    rw [← triangleRegularToOrbit_project]
    apply congrArg triangleRegularToOrbit
    have h := (regularLift x).left_inv hu
    simpa only [regularLift_symm] using h

/-- The already constructed full regular chart is contained in the orbit
image of this same actual covering sheet. -/
theorem regularFullChart_source_subset_regularImage (x : TriangleRegularQuotient) :
    (regularFullChart x).source ⊆ (regularImage x : Set TriangleOrbitSpace) := by
  intro y hy
  rw [regularImage_eq_localInverse_source]
  refine ⟨triangleRegularOrbitParametrization.symm y, hy.2.1, ?_⟩
  exact triangleRegularOrbitParametrization.right_inv hy.1

theorem exists_regularImage (y : TriangleOrbitSpace)
    (hy : y ∈ triangleOrbitRegularDomain) :
    ∃ x : TriangleRegularQuotient, y ∈ regularImage x := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, regularImage_mem x⟩

/-- The orbit images of the constructed sheets cover precisely the regular
domain, not a domain postulated to have local covering charts. -/
theorem regularImage_iUnion :
    (⋃ x : TriangleRegularQuotient, (regularImage x : Set TriangleOrbitSpace)) =
      (triangleOrbitRegularDomain : Set TriangleOrbitSpace) := by
  apply le_antisymm
  · exact iUnion_subset regularImage_subset_regularDomain
  · intro y hy
    obtain ⟨x, hx⟩ := exists_regularImage y hy
    exact mem_iUnion.mpr ⟨x, hx⟩

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Cover
