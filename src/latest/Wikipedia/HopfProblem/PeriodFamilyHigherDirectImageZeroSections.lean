import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroBasic

/-!
# Actual all-open holomorphic descent for a varying period family

Pullback along the original projection and evaluation along the original
holomorphic zero section are mutually inverse algebra homomorphisms on
every base open set. Fibrewise constancy proves the nontrivial inverse
identity. Both maps commute with the literal section restrictions.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- Literal holomorphic pullback on every base open set. -/
def pullbackSection (P : HolomorphicPeriodMap V B) (U : Opens B) :
    BaseSection P U →ₐ[ℂ] PreimageSection P U := by
  letI := P.totalChartedSpace
  exact
    { toFun f := ⟨f ∘ baseProjection P U,
        f.contMDiff.comp (baseProjection_holomorphic P U)⟩
      map_one' := by ext; rfl
      map_mul' _ _ := by ext; rfl
      map_zero' := by ext; rfl
      map_add' _ _ := by ext; rfl
      commutes' _ := by ext; rfl }

@[simp] theorem pullbackSection_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (f : BaseSection P U) (x : basePreimage P U) :
    pullbackSection P U f x = f (baseProjection P U x) := rfl

/-- Descent is actual evaluation along the original holomorphic zero section. -/
def descendedSection (P : HolomorphicPeriodMap V B) (U : Opens B) :
    PreimageSection P U →ₐ[ℂ] BaseSection P U := by
  letI := P.totalChartedSpace
  exact
    { toFun s := ⟨s ∘ zeroSectionOn P U,
        s.contMDiff.comp (zeroSectionOn_holomorphic P U)⟩
      map_one' := by ext; rfl
      map_mul' _ _ := by ext; rfl
      map_zero' := by ext; rfl
      map_add' _ _ := by ext; rfl
      commutes' _ := by ext; rfl }

@[simp] theorem descendedSection_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (s : PreimageSection P U) (b : U) :
    descendedSection P U s b = s (zeroSectionOn P U b) := rfl

/-- The zero section is an actual section of the original projection. -/
@[simp] theorem descendedSection_pullbackSection (P : HolomorphicPeriodMap V B)
    (U : Opens B) (f : BaseSection P U) :
    descendedSection P U (pullbackSection P U f) = f := by
  apply ContMDiffMap.ext
  intro b
  rfl

/-- Constancy on each original compact fibre proves the other inverse identity. -/
@[simp] theorem pullbackSection_descendedSection (P : HolomorphicPeriodMap V B)
    (U : Opens B) (s : PreimageSection P U) :
    pullbackSection P U (descendedSection P U s) = s := by
  let := P.totalChartedSpace
  apply ContMDiffMap.ext
  intro x
  exact (section_apply_eq_zeroSection P U s x).symm

/-- The genuine holomorphic section algebras are identified by literal
pullback, with literal zero-section evaluation as inverse. -/
def pullbackSectionEquiv (P : HolomorphicPeriodMap V B) (U : Opens B) :
    BaseSection P U ≃ₐ[ℂ] PreimageSection P U where
  __ := pullbackSection P U
  invFun := descendedSection P U
  left_inv := descendedSection_pullbackSection P U
  right_inv := pullbackSection_descendedSection P U

@[simp] theorem pullbackSectionEquiv_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (f : BaseSection P U) : pullbackSectionEquiv P U f = pullbackSection P U f := rfl

@[simp] theorem pullbackSectionEquiv_symm_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (s : PreimageSection P U) :
    (pullbackSectionEquiv P U).symm s = descendedSection P U s := rfl

theorem pullbackSection_bijective (P : HolomorphicPeriodMap V B) (U : Opens B) :
    Function.Bijective (pullbackSection P U) := (pullbackSectionEquiv P U).bijective

/-- Each actual holomorphic section over a full preimage has unique
holomorphic descent to its original base open set. -/
theorem exists_unique_descent (P : HolomorphicPeriodMap V B) (U : Opens B)
    (s : PreimageSection P U) : ∃! f : BaseSection P U, pullbackSection P U f = s := by
  refine ⟨descendedSection P U s, pullbackSection_descendedSection P U s, ?_⟩
  intro f hf
  exact (pullbackSectionEquiv P U).injective
    (hf.trans (pullbackSection_descendedSection P U s).symm)

/-- The original base restriction, with its pointwise complex algebra structure. -/
abbrev baseRestriction (P : HolomorphicPeriodMap V B) {U W : Opens B} (h : U ≤ W) :
    BaseSection P W →ₐ[ℂ] BaseSection P U :=
  HolomorphicFunctionSheaf.restrictionAlgHom IB B h

/-- The literal restriction on the full preimages in the unchanged native atlas. -/
def preimageRestriction (P : HolomorphicPeriodMap V B) {U W : Opens B} (h : U ≤ W) :
    PreimageSection P W →ₐ[ℂ] PreimageSection P U := by
  letI := P.totalChartedSpace
  exact HolomorphicFunctionSheaf.restrictionAlgHom IT P.TotalSpace (basePreimage_mono P h)

omit [IsManifold (modelWithCornersSelf ℂ V) ω B] in
@[simp] theorem preimageRestriction_apply (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (s : PreimageSection P W) (x : basePreimage P U) :
    preimageRestriction P h s x = s ⟨x, h x.property⟩ := rfl

/-- Pullback commutes with all actual restriction maps. -/
theorem pullbackSection_restrict (P : HolomorphicPeriodMap V B) {U W : Opens B}
    (h : U ≤ W) (f : BaseSection P W) :
    pullbackSection P U (baseRestriction P h f) =
      preimageRestriction P h (pullbackSection P W f) := by
  let := P.totalChartedSpace
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Zero-section descent commutes with every actual restriction map. -/
theorem descendedSection_restrict (P : HolomorphicPeriodMap V B) {U W : Opens B}
    (h : U ≤ W) (s : PreimageSection P W) :
    descendedSection P U (preimageRestriction P h s) =
      baseRestriction P h (descendedSection P W s) := by
  apply ContMDiffMap.ext
  intro b
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero
