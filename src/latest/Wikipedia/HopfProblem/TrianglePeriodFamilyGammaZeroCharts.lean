import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroFamily

/-!
# Restricted native product charts for the zero-γ subfamily

Every original section chart preserves the descended circle coordinate.
Restricting it gives an actual homeomorphism from the literal zero-γ
subfamily over the same open set to that open set times the zero fibre.
The chart inclusions retain the original quotient representative formulas.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SpecialPeriods Set Topology

variable (D : Data ℂ TriangleRegularPoint)

/-- The literal inverse image of a base open set in the actual subfamily. -/
def familyOpen (U : TopologicalSpace.Opens TriangleRegularQuotient) :
    TopologicalSpace.Opens (Space D) :=
  ⟨(projection D) ⁻¹' (U : Set TriangleRegularQuotient),
    U.isOpen.preimage (projection D).continuous⟩

@[simp] theorem mem_familyOpen (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (x : Space D) : x ∈ familyOpen D U ↔ D.projection x.val ∈ U := Iff.rfl

/-- The literal restriction of the subfamily inclusion over an unchanged base open set. -/
def inclusionOnOpen (U : TopologicalSpace.Opens TriangleRegularQuotient) :
    C(familyOpen D U, Homology.familyOpen D U) :=
  ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem inclusionOnOpen_val (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (x : familyOpen D U) : (inclusionOnOpen D U x).val = x.val.val := rfl

variable (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (s : C(U, TriangleRegularPoint)) (hs : ∀ x, triangleRegularProject (s x) = x.val)

/-- The old product chart reads precisely the original descended γ coordinate. -/
theorem oldSectionChart_gamma (x : Homology.familyOpen D U) :
    fibreGamma (Homology.sectionChart D U s hs x).2 = familyGamma D x.val := by
  obtain ⟨y, rfl⟩ := (Homology.sectionChart D U s hs).symm.surjective x
  rw [Homeomorph.apply_symm_apply, Homology.sectionChart_symm_coe, familyGamma_quotient]

/-- Restriction of the original full product chart to the actual zero-coordinate subspace. -/
def sectionChart (D : Data ℂ TriangleRegularPoint)
    (U : TopologicalSpace.Opens TriangleRegularQuotient)
    (s : C(U, TriangleRegularPoint)) (hs : ∀ x, triangleRegularProject (s x) = x.val) :
    familyOpen D U ≃ₜ U × Fibre where
  toFun x :=
    ((Homology.sectionChart D U s hs (inclusionOnOpen D U x)).1,
      ⟨(Homology.sectionChart D U s hs (inclusionOnOpen D U x)).2,
        (oldSectionChart_gamma D U s hs (inclusionOnOpen D U x)).trans x.val.property⟩)
  invFun y := ⟨quotient D (s y.1, y.2),
    show triangleRegularProject (s y.1) ∈ U from (hs y.1).symm ▸ y.1.property⟩
  left_inv x := by
    have h := congrArg (fun z : Homology.familyOpen D U => z.val)
      ((Homology.sectionChart D U s hs).symm_apply_apply (inclusionOnOpen D U x))
    exact Subtype.ext (Subtype.ext h)
  right_inv y := by
    have h := Homology.sectionChart_apply_quotient D U s hs y.1 y.2.val
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext
    · exact h₁
    · exact Subtype.ext h₂
  continuous_toFun := by
    have h := (Homology.sectionChart D U s hs).continuous.comp
      (inclusionOnOpen D U).continuous
    exact h.fst.prodMk (h.snd.subtype_mk _)
  continuous_invFun := ((quotient D).continuous.comp
    ((s.continuous.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

/-- The inverse restricted chart is still the original quotient parametrization. -/
@[simp] theorem sectionChart_symm_inclusion (y : U × Fibre) :
    inclusion D ((sectionChart D U s hs).symm y).val =
      D.quotient (s y.1, y.2.val) := rfl

/-- The original and restricted product charts intertwine the actual fibre inclusion. -/
theorem sectionChart_inclusionOnOpen (x : familyOpen D U) :
    Homology.sectionChart D U s hs (inclusionOnOpen D U x) =
      ((sectionChart D U s hs x).1, (sectionChart D U s hs x).2.val) := rfl

theorem sectionChart_projection (x : familyOpen D U) :
    ((sectionChart D U s hs x).1 : TriangleRegularQuotient) = projection D x.val :=
  Homology.sectionChart_projection D U s hs (inclusionOnOpen D U x)

@[simp] theorem sectionChart_symm_projection (y : U × Fibre) :
    projection D ((sectionChart D U s hs).symm y).val = y.1.val := hs y.1

/-- Setting the first fibre coordinate to zero in the original section chart. -/
def sectionRetraction : C(Homology.familyOpen D U, familyOpen D U) :=
  ((sectionChart D U s hs).symm : C(_, _)).comp
    ⟨fun x => ((Homology.sectionChart D U s hs x).1,
      fibreRetraction (Homology.sectionChart D U s hs x).2),
      (Homology.sectionChart D U s hs).continuous.fst.prodMk
        (fibreRetraction.continuous.comp (Homology.sectionChart D U s hs).continuous.snd)⟩

/-- The local retraction does not change the actual base point. -/
@[simp] theorem sectionRetraction_projection (x : Homology.familyOpen D U) :
    projection D (sectionRetraction D U s hs x).val = D.projection x.val := by
  change projection D
    ((sectionChart D U s hs).symm
      ((Homology.sectionChart D U s hs x).1,
        fibreRetraction (Homology.sectionChart D U s hs x).2)).val = _
  rw [sectionChart_symm_projection]
  exact Homology.sectionChart_projection D U s hs x

/-- It fixes every point of the actual zero-γ part of the open set. -/
@[simp] theorem sectionRetraction_inclusionOnOpen (x : familyOpen D U) :
    sectionRetraction D U s hs (inclusionOnOpen D U x) = x := by
  apply (sectionChart D U s hs).injective
  change sectionChart D U s hs
    ((sectionChart D U s hs).symm
      ((Homology.sectionChart D U s hs (inclusionOnOpen D U x)).1,
        fibreRetraction (Homology.sectionChart D U s hs (inclusionOnOpen D U x)).2)) = _
  rw [Homeomorph.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact fibreRetraction_inclusion (sectionChart D U s hs x).2

theorem sectionRetraction_comp_inclusionOnOpen :
    (sectionRetraction D U s hs).comp (inclusionOnOpen D U) =
      ContinuousMap.id (familyOpen D U) :=
  ContinuousMap.ext (sectionRetraction_inclusionOnOpen D U s hs)

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
