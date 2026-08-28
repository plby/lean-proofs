import Wikipedia.HopfProblem.CuspNormalizationSheafReducedStalkImage
import Wikipedia.HopfProblem.CuspNormalizationSheafManifoldStalkTranslation

/-!
# Centering the actual restricted analytic-germ image

Translation by the base point is an equivalence on actual germs along a
subset. Its restriction to the actual image of ambient analytic germs
agrees with analytic translation of those ambient germs.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual subset expressed in coordinates centered at `a`. -/
def centeredSubset (S : Set E) (a : E) : Set E := {z | a + z ∈ S}

/-- The original base point becomes the origin of the centered subset. -/
abbrev centeredPoint (S : Set E) (x : S) : centeredSubset S x.val :=
  ⟨0, by
    change x.val + 0 ∈ S
    simpa only [add_zero] using x.property⟩

/-- Addition of the base point transports the actual centered relative
neighbourhood filter to the original relative neighbourhood filter. -/
theorem centeredAdd_tendsto (S : Set E) (x : S) :
    Tendsto (fun z : E => x.val + z)
      (𝓝[centeredSubset S x.val] (0 : E)) (𝓝[S] x.val) := by
  have h : Tendsto (fun z : E => x.val + z) (𝓝 (0 : E)) (𝓝 x.val) := by
    simpa only [ContinuousAt, add_zero] using
      (SheafManifoldStalk.addTranslation_analyticAt x.val 0).continuousAt
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h.mono_left nhdsWithin_le_nhds) ?_
  exact self_mem_nhdsWithin

/-- Subtraction of the base point transports the actual original
relative neighbourhood filter back to the centered one. -/
theorem centeredSub_tendsto (S : Set E) (x : S) :
    Tendsto (fun z : E => z - x.val) (𝓝[S] x.val)
      (𝓝[centeredSubset S x.val] (0 : E)) := by
  have h : Tendsto (fun z : E => z - x.val) (𝓝 x.val) (𝓝 (0 : E)) := by
    simpa only [ContinuousAt, sub_self] using
      (SheafManifoldStalk.subTranslation_analyticAt x.val x.val).continuousAt
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  change x.val + (z - x.val) ∈ S
  rw [← add_sub_assoc, add_sub_cancel_left]
  exact hz

/-- Literal composition of within-germs with the centering translation. -/
def withinTranslateToZeroHom (S : Set E) (x : S) :
    Filter.Germ (𝓝[S] x.val) ℂ →+*
      Filter.Germ (𝓝[centeredSubset S x.val] (0 : E)) ℂ :=
  Germs.compTendstoRingHom (fun z => x.val + z) (centeredAdd_tendsto S x)

/-- Literal composition of within-germs with the inverse translation. -/
def withinTranslateFromZeroHom (S : Set E) (x : S) :
    Filter.Germ (𝓝[centeredSubset S x.val] (0 : E)) ℂ →+*
      Filter.Germ (𝓝[S] x.val) ℂ :=
  Germs.compTendstoRingHom (fun z => z - x.val) (centeredSub_tendsto S x)

theorem withinTranslateToZero_restrictAnalyticGerm (S : Set E) (x : S)
    (φ : Germs.AnalyticGerm x.val) :
    withinTranslateToZeroHom S x (restrictAnalyticGerm S x φ) =
      restrictAnalyticGerm (centeredSubset S x.val) (centeredPoint S x)
        (SheafManifoldStalk.translateToZero x.val φ) := by
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  rw [SheafManifoldStalk.translateToZero_ofAnalytic]
  rfl

theorem withinTranslateFromZero_restrictAnalyticGerm (S : Set E) (x : S)
    (φ : Germs.AnalyticGerm (0 : E)) :
    withinTranslateFromZeroHom S x
      (restrictAnalyticGerm (centeredSubset S x.val) (centeredPoint S x) φ) =
      restrictAnalyticGerm S x ((SheafManifoldStalk.translateToZero x.val).symm φ) := by
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  rw [SheafManifoldStalk.translateToZero_symm_ofAnalytic]
  rfl

/-- Actual translation preserves the actual restricted analytic image. -/
def restrictedTranslateToZeroHom (S : Set E) (x : S) :
    RestrictedAnalyticGermImage S x →+*
      RestrictedAnalyticGermImage (centeredSubset S x.val) (centeredPoint S x) :=
  ((withinTranslateToZeroHom S x).comp (restrictAnalyticGerm S x).range.subtype).codRestrict
    (restrictAnalyticGerm (centeredSubset S x.val) (centeredPoint S x)).range (by
      intro ψ
      obtain ⟨φ, hφ⟩ := ψ.property
      refine ⟨SheafManifoldStalk.translateToZero x.val φ, ?_⟩
      change _ = withinTranslateToZeroHom S x ψ.val
      rw [← hφ, withinTranslateToZero_restrictAnalyticGerm])

/-- The inverse actual translation also preserves the restricted analytic image. -/
def restrictedTranslateFromZeroHom (S : Set E) (x : S) :
    RestrictedAnalyticGermImage (centeredSubset S x.val) (centeredPoint S x) →+*
      RestrictedAnalyticGermImage S x :=
  ((withinTranslateFromZeroHom S x).comp
    (restrictAnalyticGerm (centeredSubset S x.val) (centeredPoint S x)).range.subtype).codRestrict
      (restrictAnalyticGerm S x).range (by
        intro ψ
        obtain ⟨φ, hφ⟩ := ψ.property
        refine ⟨(SheafManifoldStalk.translateToZero x.val).symm φ, ?_⟩
        change _ = withinTranslateFromZeroHom S x ψ.val
        rw [← hφ, withinTranslateFromZero_restrictAnalyticGerm])

@[simp] theorem restrictedTranslateToZeroHom_rangeRestrict (S : Set E) (x : S)
    (φ : Germs.AnalyticGerm x.val) :
    restrictedTranslateToZeroHom S x ((restrictAnalyticGerm S x).rangeRestrict φ) =
      (restrictAnalyticGerm (centeredSubset S x.val) (centeredPoint S x)).rangeRestrict
        (SheafManifoldStalk.translateToZero x.val φ) := by
  apply Subtype.ext
  exact withinTranslateToZero_restrictAnalyticGerm S x φ

@[simp] theorem restrictedTranslateFromZeroHom_rangeRestrict (S : Set E) (x : S)
    (φ : Germs.AnalyticGerm (0 : E)) :
    restrictedTranslateFromZeroHom S x
      ((restrictAnalyticGerm (centeredSubset S x.val) (centeredPoint S x)).rangeRestrict φ) =
      (restrictAnalyticGerm S x).rangeRestrict
        ((SheafManifoldStalk.translateToZero x.val).symm φ) := by
  apply Subtype.ext
  exact withinTranslateFromZero_restrictAnalyticGerm S x φ

/-- Actual centering identifies the original and centered restricted
analytic-germ images by literal composition in both directions. -/
def restrictedTranslateToZero (S : Set E) (x : S) :
    RestrictedAnalyticGermImage S x ≃+*
      RestrictedAnalyticGermImage (centeredSubset S x.val) (centeredPoint S x) :=
  { restrictedTranslateToZeroHom S x with
    invFun := restrictedTranslateFromZeroHom S x
    left_inv := by
      intro ψ
      change restrictedTranslateFromZeroHom S x (restrictedTranslateToZeroHom S x ψ) = ψ
      obtain ⟨φ, rfl⟩ := (restrictAnalyticGerm S x).rangeRestrict_surjective ψ
      rw [restrictedTranslateToZeroHom_rangeRestrict,
        restrictedTranslateFromZeroHom_rangeRestrict, RingEquiv.symm_apply_apply]
    right_inv := by
      intro ψ
      change restrictedTranslateToZeroHom S x (restrictedTranslateFromZeroHom S x ψ) = ψ
      obtain ⟨φ, rfl⟩ :=
        (restrictAnalyticGerm (centeredSubset S x.val)
          (centeredPoint S x)).rangeRestrict_surjective ψ
      rw [restrictedTranslateFromZeroHom_rangeRestrict,
        restrictedTranslateToZeroHom_rangeRestrict, RingEquiv.apply_symm_apply] }

/-- Centering the actual restriction of an ambient analytic germ equals
the actual restriction of its centered ambient analytic germ. -/
@[simp] theorem restrictedTranslateToZero_rangeRestrict (S : Set E) (x : S)
    (φ : Germs.AnalyticGerm x.val) :
    restrictedTranslateToZero S x ((restrictAnalyticGerm S x).rangeRestrict φ) =
      (restrictAnalyticGerm (centeredSubset S x.val) (centeredPoint S x)).rangeRestrict
        (SheafManifoldStalk.translateToZero x.val φ) :=
  restrictedTranslateToZeroHom_rangeRestrict S x φ

/-- On an actual analytic representative, the translated within-germ is
literally represented by `z ↦ f (x + z)`. -/
@[simp] theorem restrictedTranslateToZero_ofAnalytic_coe (S : Set E) (x : S)
    (f : E → ℂ) (hf : AnalyticAt ℂ f x.val) :
    (restrictedTranslateToZero S x
      ((restrictAnalyticGerm S x).rangeRestrict (Germs.ofAnalytic f hf)) :
        Filter.Germ (𝓝[centeredSubset S x.val] (0 : E)) ℂ) =
      (fun z => f (x.val + z) : E → ℂ) := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
