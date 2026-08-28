import Wikipedia.HopfProblem.DegreeCollapseRoundedTraceRetractionParameters

/-!
# A global deformation of the actual rounded trace

The compact closed cover by the original attachment and the added collar
is a genuine quotient, also after multiplying by the time interval. The
parameter deformation descends because it is fixed on the exact overlap.
Its endpoint lies in the original attachment, which stays pointwise fixed.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

abbrev CoverPieces := (UnroundedTrace.ambientSet A) ⊕ addedParameters A

def oldInclusion : C(UnroundedTrace.ambientSet A, ambientSet A) :=
  ⟨fun x ↦ ⟨x.val, unrounded_subset A x.property⟩, continuous_subtype_val.subtype_mk _⟩

def addedPoint : C(addedParameters A, ambientSet A) :=
  ⟨fun p ↦ ⟨A.collarSheet p.val, Or.inr ⟨p.val, p.property, rfl⟩⟩,
    (A.contMDiffOn_collarSheet.continuousOn.comp_continuous continuous_subtype_val
      (fun p ↦ addedParameters_subset_source A p.property)).subtype_mk _⟩

def coverMap : C(CoverPieces A, ambientSet A) :=
  ⟨Sum.elim (oldInclusion A) (addedPoint A),
    (oldInclusion A).continuous.sumElim (addedPoint A).continuous⟩

theorem coverMap_surjective : Surjective (coverMap A) := by
  intro x
  rcases x.property with hx | ⟨p, hp, he⟩
  · exact ⟨Sum.inl ⟨x.val, hx⟩, Subtype.ext rfl⟩
  · exact ⟨Sum.inr ⟨p, hp⟩, Subtype.ext he⟩

def coverCylinder : C(I × CoverPieces A, I × ambientSet A) :=
  (ContinuousMap.id I).prodMap (coverMap A)

theorem coverCylinder_isQuotientMap : IsQuotientMap (coverCylinder A) := by
  let : CompactSpace (UnroundedTrace.ambientSet A) :=
    isCompact_iff_compactSpace.mp (UnroundedTrace.isCompact_ambientSet A)
  let : CompactSpace (addedParameters A) := isCompact_iff_compactSpace.mp (isCompact_addedParameters A)
  have hs : Surjective (coverCylinder A) := by
    rintro ⟨t, x⟩
    obtain ⟨p, hp⟩ := coverMap_surjective A x
    exact ⟨(t, p), Prod.ext rfl hp⟩
  exact .of_surjective_continuous hs (coverCylinder A).continuous

def addedMotion : C(I × addedParameters A, ambientSet A) := by
  have hcoords : Continuous (fun z : I × addedParameters A ↦ ((z.1 : ℝ), z.2.val)) := by
    fun_prop
  have hc := (continuous_parameterDeform A).comp hcoords
  let P : C(I × addedParameters A, (Sphere 3 × Vector 3) × ℝ) :=
    ⟨fun z ↦ parameterDeform A (z.1 : ℝ) z.2.val, hc⟩
  have hmem (z : I × addedParameters A) : P z ∈ addedParameters A :=
    parameterDeform_mem A z.1.property z.2.property
  exact ⟨fun z ↦ ⟨A.collarSheet (P z), Or.inr ⟨P z, hmem z, rfl⟩⟩,
    (A.contMDiffOn_collarSheet.continuousOn.comp_continuous P.continuous
      (fun z ↦ addedParameters_subset_source A (hmem z))).subtype_mk _⟩

def pieceMotion : C(I × CoverPieces A, ambientSet A) := by
  let L : C(I × UnroundedTrace.ambientSet A, ambientSet A) :=
    (oldInclusion A).comp ⟨Prod.snd, continuous_snd⟩
  let S : C((I × UnroundedTrace.ambientSet A) ⊕ (I × addedParameters A), ambientSet A) :=
    ⟨Sum.elim L (addedMotion A), L.continuous.sumElim (addedMotion A).continuous⟩
  let D : I × CoverPieces A ≃ₜ (I × UnroundedTrace.ambientSet A) ⊕ (I × addedParameters A) :=
    Homeomorph.prodSumDistrib
  exact S.comp ⟨D, D.continuous⟩

theorem pieceMotion_inl (t : I) (x : UnroundedTrace.ambientSet A) :
    pieceMotion A (t, Sum.inl x) = oldInclusion A x := rfl

theorem pieceMotion_inr (t : I) (p : addedParameters A) :
    pieceMotion A (t, Sum.inr p) = addedMotion A (t, p) := rfl

theorem pieceMotion_fibers (q r : I × CoverPieces A) (he : coverCylinder A q = coverCylinder A r) :
    pieceMotion A q = pieceMotion A r := by
  rcases q with ⟨t, x⟩
  rcases r with ⟨u, y⟩
  have htu : t = u := congrArg Prod.fst he
  subst u
  have hxy : coverMap A x = coverMap A y := congrArg Prod.snd he
  rcases x with x | x <;> rcases y with y | y
  · exact hxy
  · have hval : x.val = A.collarSheet y.val := congrArg Subtype.val hxy
    have hold : A.collarSheet y.val ∈ UnroundedTrace.ambientSet A := hval ▸ x.property
    apply Subtype.ext
    change x.val = A.collarSheet (parameterDeform A (t : ℝ) y.val)
    rw [parameterDeform_fixed_on_overlap A y.property hold]
    exact hval
  · have hval : A.collarSheet x.val = y.val := congrArg Subtype.val hxy
    have hold : A.collarSheet x.val ∈ UnroundedTrace.ambientSet A := hval.symm ▸ y.property
    apply Subtype.ext
    change A.collarSheet (parameterDeform A (t : ℝ) x.val) = y.val
    rw [parameterDeform_fixed_on_overlap A x.property hold]
    exact hval
  · have hval : A.collarSheet x.val = A.collarSheet y.val := congrArg Subtype.val hxy
    have hp : x = y := Subtype.ext (A.injOn_collarSheet
      (addedParameters_subset_source A x.property) (addedParameters_subset_source A y.property) hval)
    subst y
    rfl

def deformation : C(I × ambientSet A, ambientSet A) :=
  (coverCylinder_isQuotientMap A).lift (pieceMotion A) (pieceMotion_fibers A)

theorem deformation_cover (t : I) (p : CoverPieces A) :
    deformation A (t, coverMap A p) = pieceMotion A (t, p) :=
  ContinuousMap.congr_fun ((coverCylinder_isQuotientMap A).lift_comp
    (pieceMotion A) (pieceMotion_fibers A)) (t, p)

theorem deformation_zero (x : ambientSet A) : deformation A (0, x) = x := by
  obtain ⟨p, rfl⟩ := coverMap_surjective A x
  rw [deformation_cover]
  rcases p with p | p
  · rfl
  · apply Subtype.ext
    change A.collarSheet (parameterDeform A (0 : ℝ) p.val) = A.collarSheet p.val
    rw [parameterDeform_zero]

theorem deformation_fixed (t : I) (x : UnroundedTrace.ambientSet A) :
    deformation A (t, oldInclusion A x) = oldInclusion A x :=
  deformation_cover A t (Sum.inl x)

theorem deformation_one_mem (x : ambientSet A) :
    (deformation A (1, x)).val ∈ UnroundedTrace.ambientSet A := by
  obtain ⟨p, rfl⟩ := coverMap_surjective A x
  rw [deformation_cover]
  rcases p with p | p
  · exact p.property
  · exact parameterDeform_one_mem_unrounded A p.property

end Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction
