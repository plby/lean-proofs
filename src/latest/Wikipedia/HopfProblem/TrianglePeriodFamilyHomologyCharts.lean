import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySlitLifts
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySection
import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry

/-!
# Actual torus-product charts on the regular-family slit cover

The full inverse image of each slit is homeomorphic to that slit times
the real coordinate torus. The charts are built by inserting the actual
covering sections in the actual diagonal quotient. The same construction
applies to each of the three overlap components.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

variable (D : Data ℂ TriangleRegularPoint)

/-- The literal inverse image of an open subset under the actual family projection. -/
def familyOpen (U : TopologicalSpace.Opens TriangleRegularQuotient) :
    TopologicalSpace.Opens D.Space :=
  ⟨D.projection ⁻¹' (U : Set TriangleRegularQuotient),
    U.isOpen.preimage D.projection_continuous⟩

@[simp] theorem mem_familyOpen (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (x : D.Space) : x ∈ familyOpen D U ↔ D.projection x ∈ U := Iff.rfl

abbrev upperFamily := familyOpen D upperBase

abbrev lowerFamily := familyOpen D lowerBase

abbrev overlapFamily (i : Fin 3) := familyOpen D (overlapBase i)

/-- The two slit inverse images cover the actual regular family. -/
theorem upperFamily_union_lowerFamily :
    (upperFamily D : Set D.Space) ∪ lowerFamily D = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_upperSlit_or_lowerSlit (triangleRegularPlaneHomeomorph (D.projection x))

theorem overlapFamily_subset (i : Fin 3) :
    (overlapFamily D i : Set D.Space) ⊆ (upperFamily D : Set D.Space) ∩ lowerFamily D :=
  fun _ hx => overlapBase_subset i hx

theorem overlapFamily_pairwise_disjoint :
    Pairwise fun i j : Fin 3 => Disjoint
      (overlapFamily D i : Set D.Space) (overlapFamily D j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp (overlapBase_pairwise_disjoint hij) hi hj

/-- All of the actual family overlap is accounted for by these three inverse images. -/
theorem overlapFamily_iUnion :
    (⋃ i : Fin 3, (overlapFamily D i : Set D.Space)) =
      (upperFamily D : Set D.Space) ∩ lowerFamily D := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact overlapFamily_subset D i hi
  · intro hx
    have hh : D.projection x ∈ ⋃ i : Fin 3, (overlapBase i : Set TriangleRegularQuotient) := by
      rw [overlapBase_iUnion]
      exact hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hh
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- A genuine global product chart over any actual continuously lifted open set. -/
def sectionChart (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (s : C(U, TriangleRegularPoint)) (hs : ∀ x, triangleRegularProject (s x) = x.val) :
    familyOpen D U ≃ₜ U × RealTorus₄ :=
  DiagonalQuotient.sectionHomeomorph triangleRegularProject_covering U s hs

@[simp] theorem sectionChart_symm_coe (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (s : C(U, TriangleRegularPoint)) (hs : ∀ x, triangleRegularProject (s x) = x.val)
    (x : U × RealTorus₄) :
    ((sectionChart D U s hs).symm x : D.Space) = D.quotient (s x.1, x.2) := rfl

/-- The product chart preserves the literal family projection. -/
theorem sectionChart_projection (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (s : C(U, TriangleRegularPoint)) (hs : ∀ x, triangleRegularProject (s x) = x.val)
    (x : familyOpen D U) :
    ((sectionChart D U s hs x).1 : TriangleRegularQuotient) = D.projection x.val :=
  DiagonalQuotient.sectionHomeomorph_projection triangleRegularProject_covering U s hs x

@[simp] theorem sectionChart_apply_quotient
    (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (s : C(U, TriangleRegularPoint)) (hs : ∀ x, triangleRegularProject (s x) = x.val)
    (x : U) (f : RealTorus₄) :
    sectionChart D U s hs
      ⟨D.quotient (s x, f), by
        change triangleRegularProject (s x) ∈ U
        rw [hs x]
        exact x.property⟩ = (x, f) :=
  DiagonalQuotient.sectionHomeomorph_apply_quotient triangleRegularProject_covering U s hs x f

/-- The actual torus-product chart on the entire upper-slit inverse image. -/
def upperChart (b : SlitBaseLift) : upperFamily D ≃ₜ upperBase × RealTorus₄ :=
  sectionChart D upperBase (upperLift b) (upperLift_project b)

/-- The actual torus-product chart on the entire lower-slit inverse image. -/
def lowerChart (b : SlitBaseLift) : lowerFamily D ≃ₜ lowerBase × RealTorus₄ :=
  sectionChart D lowerBase (lowerLift b) (lowerLift_project b)

/-- Each overlap component is marked using the upper-slit lift. -/
def overlapChart (b : SlitBaseLift) (i : Fin 3) :
    overlapFamily D i ≃ₜ overlapBase i × RealTorus₄ :=
  sectionChart D (overlapBase i) (upperLiftOnOverlap b i) (upperLiftOnOverlap_project b i)

@[simp] theorem upperChart_symm_coe (b : SlitBaseLift) (x : upperBase × RealTorus₄) :
    ((upperChart D b).symm x : D.Space) = D.quotient (upperLift b x.1, x.2) := rfl

@[simp] theorem lowerChart_symm_coe (b : SlitBaseLift) (x : lowerBase × RealTorus₄) :
    ((lowerChart D b).symm x : D.Space) = D.quotient (lowerLift b x.1, x.2) := rfl

@[simp] theorem overlapChart_symm_coe (b : SlitBaseLift) (i : Fin 3)
    (x : overlapBase i × RealTorus₄) :
    ((overlapChart D b i).symm x : D.Space) =
      D.quotient (upperLiftOnOverlap b i x.1, x.2) := rfl

/-- The literal inclusion of one family overlap component into the upper member. -/
def overlapFamilyToUpper (i : Fin 3) : C(overlapFamily D i, upperFamily D) :=
  ⟨fun x => ⟨x.val, (overlapFamily_subset D i x.property).1⟩, by fun_prop⟩

/-- The literal inclusion into the lower member of the family cover. -/
def overlapFamilyToLower (i : Fin 3) : C(overlapFamily D i, lowerFamily D) :=
  ⟨fun x => ⟨x.val, (overlapFamily_subset D i x.property).2⟩, by fun_prop⟩

/-- On the upper side the actual overlap chart change is the identity on the torus. -/
theorem upperChart_overlapFamilyToUpper (b : SlitBaseLift) (i : Fin 3)
    (x : overlapFamily D i) :
    upperChart D b (overlapFamilyToUpper D i x) =
      (overlapToUpper i (overlapChart D b i x).1, (overlapChart D b i x).2) := by
  obtain ⟨y, rfl⟩ := (overlapChart D b i).symm.surjective x
  rw [Homeomorph.apply_symm_apply]
  exact sectionChart_apply_quotient D upperBase (upperLift b) (upperLift_project b)
    (overlapToUpper i y.1) y.2

/-- On the lower side the actual overlap change is precisely the constant triangle action. -/
theorem lowerChart_overlapFamilyToLower (b : SlitBaseLift) (i : Fin 3)
    (x : overlapFamily D i) :
    lowerChart D b (overlapFamilyToLower D i x) =
      (overlapToLower i (overlapChart D b i x).1,
        triangleTorusHomeomorph (overlapTransition b i) (overlapChart D b i x).2) := by
  obtain ⟨y, rfl⟩ := (overlapChart D b i).symm.surjective x
  rw [Homeomorph.apply_symm_apply]
  apply (lowerChart D b).symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  change D.quotient (upperLiftOnOverlap b i y.1, y.2) =
    D.quotient (lowerLiftOnOverlap b i y.1,
      triangleTorusHomeomorph (overlapTransition b i) y.2)
  rw [← overlapTransition_apply b i y.1]
  exact (DiagonalQuotient.quotient_smul TriangleGroup TriangleRegularPoint RealTorus₄
    (overlapTransition b i) (upperLiftOnOverlap b i y.1, y.2)).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
