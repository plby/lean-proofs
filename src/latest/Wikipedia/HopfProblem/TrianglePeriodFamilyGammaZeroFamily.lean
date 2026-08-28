import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroLinear
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroTorusTopology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyCharts

/-!
# The literal zero-γ regular subfamily

The invariant first circle coordinate descends through the original
triangle quotient.  Its zero fibre is a subspace of the actual regular
family, with the inherited topology and literal inclusion.  All formulas
use the original real period coordinates and quotient maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SpecialPeriods PeriodTorusHigherHomology
open Set Topology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- The original triangle action preserves the actual first circle coordinate. -/
@[simp] theorem fibreGamma_triangleTorusHomeomorph (g : TriangleGroup) (x : RealTorus₄) :
    fibreGamma (triangleTorusHomeomorph g x) = fibreGamma x := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, fibreGamma_mkQ, fibreGamma_mkQ,
    triangleRealEquiv_gamma]

variable (D : Data ℂ TriangleRegularPoint)

/-- The invariant γ circle coordinate on the original regular quotient family. -/
def familyGamma : C(D.Space, AddCircle (1 : ℝ)) where
  toFun := Quotient.lift (fun x : TriangleRegularPoint × RealTorus₄ => fibreGamma x.2) (by
    rintro x y ⟨g, hg⟩
    have he : triangleTorusHomeomorph g y.2 = x.2 := congrArg Prod.snd hg
    rw [← he, fibreGamma_triangleTorusHomeomorph])
  continuous_toFun := D.quotient_isQuotientMap.continuous_iff.mpr
    (fibreGamma.continuous.comp continuous_snd)

/-- On every actual quotient representative, γ is precisely the original fibre coordinate. -/
@[simp] theorem familyGamma_quotient (b : TriangleRegularPoint) (x : RealTorus₄) :
    familyGamma D (D.quotient (b, x)) = fibreGamma x := rfl

/-- The exact original real-coordinate formula used by boundary factorizations. -/
@[simp] theorem familyGamma_quotient_mkQ (b : TriangleRegularPoint) (x : RealPlane₄) :
    familyGamma D (D.quotient (b, standardLattice.mkQ x)) =
      (x 0 : AddCircle (1 : ℝ)) := fibreGamma_mkQ x

/-- The native zero-γ subfamily, as a literal subspace of the original family. -/
abbrev Space := {x : D.Space // familyGamma D x = 0}

theorem zeroLocus_isClosed : IsClosed {x : D.Space | familyGamma D x = 0} :=
  isClosed_eq (familyGamma D).continuous continuous_const

/-- The literal inclusion of the rank-three torus subfamily. -/
def inclusion : C(Space D, D.Space) := ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem inclusion_apply (x : Space D) : inclusion D x = x.val := rfl

theorem inclusion_injective : Function.Injective (inclusion D) := Subtype.val_injective

/-- Its base map is the restriction of the original regular-family projection. -/
def projection : C(Space D, TriangleRegularQuotient) :=
  ⟨fun x => D.projection x.val, D.projection_continuous.comp continuous_subtype_val⟩

@[simp] theorem projection_apply (x : Space D) : projection D x = D.projection x.val := rfl

/-- The original quotient on the zero-coordinate real family, codrestricted to its actual image. -/
def quotient : C(TriangleRegularPoint × Fibre, Space D) where
  toFun x := ⟨Data.quotient D (x.1, x.2.val),
    (familyGamma_quotient D x.1 x.2.val).trans x.2.property⟩
  continuous_toFun := ((Data.quotient_continuous D).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp] theorem inclusion_quotient (x : TriangleRegularPoint × Fibre) :
    inclusion D (quotient D x) = D.quotient (x.1, x.2.val) := rfl

@[simp] theorem projection_quotient (x : TriangleRegularPoint × Fibre) :
    projection D (quotient D x) = triangleRegularProject x.1 := rfl

/-- Every point of the literal subfamily has an original representative with γ zero. -/
theorem quotient_surjective : Function.Surjective (quotient D) := by
  intro x
  obtain ⟨⟨b, y⟩, hy⟩ := Data.quotient_surjective D x.val
  have hγ : fibreGamma y = 0 := by
    rw [← familyGamma_quotient D b y, hy]
    exact x.property
  exact ⟨(b, ⟨y, hγ⟩), Subtype.ext hy⟩

/-- The actual fibre map over a specified lift of the base point. -/
def fibreInclusionAt (b : TriangleRegularPoint) : C(Fibre, Space D) :=
  (quotient D).comp ((ContinuousMap.const Fibre b).prodMk (ContinuousMap.id Fibre))

@[simp] theorem inclusion_fibreInclusionAt (b : TriangleRegularPoint) (x : Fibre) :
    inclusion D (fibreInclusionAt D b x) = D.quotient (b, x.val) := rfl

@[simp] theorem projection_fibreInclusionAt (b : TriangleRegularPoint) (x : Fibre) :
    projection D (fibreInclusionAt D b x) = triangleRegularProject b := rfl

/-- The exact native zero-head real representative used in the boundary cylinders. -/
@[simp] theorem inclusion_quotient_fibreMkQ (b : TriangleRegularPoint) (x : Fin 3 → ℝ) :
    inclusion D (quotient D (b, fibreMkQ x)) =
      D.quotient (b, standardLattice.mkQ (Fin.cons 0 x)) := rfl

/-- Codrestriction of any genuine map whose original γ coordinate vanishes. -/
def lift {X : Type*} [TopologicalSpace X] (f : C(X, D.Space))
    (hf : ∀ x, familyGamma D (f x) = 0) : C(X, Space D) :=
  ⟨fun x => ⟨f x, hf x⟩, f.continuous.subtype_mk _⟩

@[simp] theorem inclusion_comp_lift {X : Type*} [TopologicalSpace X]
    (f : C(X, D.Space)) (hf : ∀ x, familyGamma D (f x) = 0) :
    (inclusion D).comp (lift D f hf) = f := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
