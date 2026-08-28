import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroFamily

/-!
# Literal fibres of the zero-γ regular subfamily

The original diagonal-quotient fibre homeomorphism preserves the descended
γ coordinate.  Restricting it therefore identifies the literal fibre of
the zero-γ subfamily with the actual zero-coordinate subtorus.  Its inverse
is the original quotient inclusion over the specified base lift.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SpecialPeriods PeriodTorusHigherHomology Set Topology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

variable (D : Data ℂ TriangleRegularPoint) (b : TriangleRegularPoint)

/-- The literal fibre in the original unrestricted quotient family. -/
abbrev OriginalFibreAt :=
  {x : D.Space // Data.projection D x = triangleRegularProject b}

/-- The existing diagonal-quotient fibre coordinates, in the original real torus. -/
def originalFibreHomeomorphAt : OriginalFibreAt D b ≃ₜ RealTorus₄ :=
  DiagonalQuotient.fibreHomeomorphOver (F := RealTorus₄) triangleRegularProject_covering b

@[simp] theorem originalFibreHomeomorphAt_symm_val (x : RealTorus₄) :
    ((originalFibreHomeomorphAt D b).symm x).val = Data.quotient D (b, x) :=
  DiagonalQuotient.fibreHomeomorphOver_symm_coe triangleRegularProject_covering b x

/-- These original coordinates read exactly the actual descended γ coordinate. -/
theorem originalFibreHomeomorphAt_gamma (x : OriginalFibreAt D b) :
    fibreGamma (originalFibreHomeomorphAt D b x) = familyGamma D x.val := by
  obtain ⟨y, rfl⟩ := (originalFibreHomeomorphAt D b).symm.surjective x
  rw [Homeomorph.apply_symm_apply, originalFibreHomeomorphAt_symm_val,
    familyGamma_quotient]

/-- The actual inverse image of the specified base point in the zero-γ family. -/
abbrev FibreAt := {x : Space D // projection D x = triangleRegularProject b}

/-- The literal inclusion into the full original fibre; it only forgets the γ equation. -/
def fibreAtToOriginal : C(FibreAt D b, OriginalFibreAt D b) :=
  ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem fibreAtToOriginal_val (x : FibreAt D b) :
    (fibreAtToOriginal D b x).val = x.val.val := rfl

/-- The original fixed-base quotient inclusion, codrestricted to its literal fibre. -/
def fibrePointAt (x : Fibre) : FibreAt D b :=
  ⟨fibreInclusionAt D b x, projection_fibreInclusionAt D b x⟩

@[simp] theorem fibrePointAt_val (x : Fibre) :
    (fibrePointAt D b x).val = fibreInclusionAt D b x := rfl

theorem fibrePointAt_continuous : Continuous (fibrePointAt D b) :=
  (fibreInclusionAt D b).continuous.subtype_mk _

/-- The codrestricted inclusion is the inverse of the original full-fibre chart. -/
theorem fibreAtToOriginal_pointAt (x : Fibre) :
    fibreAtToOriginal D b (fibrePointAt D b x) =
      (originalFibreHomeomorphAt D b).symm x.val := by
  apply Subtype.ext
  exact (originalFibreHomeomorphAt_symm_val D b x.val).symm

/-- Restriction of the actual quotient fibre homeomorphism to the literal zero locus. -/
def fibreHomeomorphAt : FibreAt D b ≃ₜ Fibre where
  toFun x :=
    ⟨originalFibreHomeomorphAt D b (fibreAtToOriginal D b x),
      (originalFibreHomeomorphAt_gamma D b (fibreAtToOriginal D b x)).trans x.val.property⟩
  invFun := fibrePointAt D b
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (originalFibreHomeomorphAt_symm_val D b
      (originalFibreHomeomorphAt D b (fibreAtToOriginal D b x))).symm.trans
      (congrArg Subtype.val
        ((originalFibreHomeomorphAt D b).symm_apply_apply (fibreAtToOriginal D b x)))
  right_inv x := by
    apply Subtype.ext
    change originalFibreHomeomorphAt D b
      (fibreAtToOriginal D b (fibrePointAt D b x)) = x.val
    rw [fibreAtToOriginal_pointAt, Homeomorph.apply_symm_apply]
  continuous_toFun := ((originalFibreHomeomorphAt D b).continuous.comp
    (fibreAtToOriginal D b).continuous).subtype_mk _
  continuous_invFun := fibrePointAt_continuous D b

/-- The restricted coordinates are the original real quotient coordinates. -/
@[simp] theorem fibreHomeomorphAt_apply_val (x : FibreAt D b) :
    (fibreHomeomorphAt D b x).val =
      originalFibreHomeomorphAt D b (fibreAtToOriginal D b x) := rfl

/-- The inverse is exactly the literal fibre inclusion in the zero-γ family. -/
@[simp] theorem fibreHomeomorphAt_symm_apply (x : Fibre) :
    ((fibreHomeomorphAt D b).symm x).val = fibreInclusionAt D b x := rfl

/-- Its ambient value is the original quotient representative, with the same base lift. -/
@[simp] theorem fibreHomeomorphAt_symm_ambient (x : Fibre) :
    inclusion D ((fibreHomeomorphAt D b).symm x).val = Data.quotient D (b, x.val) := rfl

@[simp] theorem fibreHomeomorphAt_pointAt (x : Fibre) :
    fibreHomeomorphAt D b (fibrePointAt D b x) = x :=
  (fibreHomeomorphAt D b).apply_symm_apply x

/-- Every point of the literal fibre has the original fixed-base quotient representative. -/
theorem fibreHomeomorphAt_quotient (x : FibreAt D b) :
    Data.quotient D (b, (fibreHomeomorphAt D b x).val) = x.val.val := by
  have h := congrArg (fun z : FibreAt D b => z.val.val)
    ((fibreHomeomorphAt D b).symm_apply_apply x)
  exact h

/-- The original fixed-base inclusion is injective, before taking any homology. -/
theorem fibreInclusionAt_injective : Function.Injective (fibreInclusionAt D b) := by
  intro x y h
  apply (fibreHomeomorphAt D b).symm.injective
  exact Subtype.ext h

/-- Its range is the entire actual fibre of the restricted projection. -/
theorem fibreInclusionAt_range :
    Set.range (fibreInclusionAt D b) = (projection D) ⁻¹' {triangleRegularProject b} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact projection_fibreInclusionAt D b y
  · intro hx
    refine ⟨fibreHomeomorphAt D b ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((fibreHomeomorphAt D b).symm_apply_apply ⟨x, hx⟩)

/-- The literal fibre inclusion has the inherited subspace topology. -/
theorem fibreInclusionAt_isEmbedding : IsEmbedding (fibreInclusionAt D b) := by
  exact IsEmbedding.subtypeVal.comp (fibreHomeomorphAt D b).symm.isEmbedding

/-- Each actual zero-γ family fibre is a genuine product of three circles. -/
def fibreTorusHomeomorphAt : FibreAt D b ≃ₜ ProductTorus 3 :=
  (fibreHomeomorphAt D b).trans fibreHomeomorph

@[simp] theorem fibreTorusHomeomorphAt_symm_apply (x : ProductTorus 3) :
    ((fibreTorusHomeomorphAt D b).symm x).val =
      fibreInclusionAt D b (fibreHomeomorph.symm x) := rfl

/-- The three-circle coordinates retain the native zero-head lattice representatives. -/
theorem fibreTorusHomeomorphAt_symm_mkQ (x : Fin 3 → ℝ) :
    inclusion D ((fibreTorusHomeomorphAt D b).symm (coordinateProjection 3 x)).val =
      Data.quotient D (b, standardLattice.mkQ (Fin.cons 0 x)) := by
  change Data.quotient D (b, (fibreHomeomorph.symm (coordinateProjection 3 x)).val) = _
  rw [fibreHomeomorph_symm_coordinateProjection]

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
