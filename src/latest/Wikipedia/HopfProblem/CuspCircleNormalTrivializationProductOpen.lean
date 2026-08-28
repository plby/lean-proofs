import Wikipedia.HopfProblem.CuspCircleNormalTrivializationOpenRestriction

/-!
# Splitting a native product over an open factor

The subtype of the product over an open second factor has the same
native manifold structure as the product with that open submanifold.
Both directions below are the literal tuple and subtype maps.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.ProductOpen

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K) (n : ℕ∞ω)

/-- The literal open product domain, written without a redundant first-factor condition. -/
def domain (U : TopologicalSpace.Opens N) : TopologicalSpace.Opens (M × N) :=
  ⟨Prod.snd ⁻¹' (U : Set N), U.isOpen.preimage continuous_snd⟩

/-- Native product/subtype reassociation, at any differentiability order. -/
def diffeomorph (U : TopologicalSpace.Opens N) :
    Diffeomorph (I.prod J) (I.prod J) (domain (M := M) U) (M × U) n where
  toFun := fun p => (p.val.1, ⟨p.val.2, p.property⟩)
  invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl
  contMDiff_toFun := by
    have hf : ContMDiff (I.prod J) I n (fun p : domain (M := M) U => p.val.1) :=
      contMDiff_fst.comp contMDiff_subtype_val
    have hs : ContMDiff (I.prod J) J n (fun p : domain (M := M) U => p.val.2) :=
      contMDiff_snd.comp contMDiff_subtype_val
    have ht : ContMDiff (I.prod J) J n
        (fun p : domain (M := M) U => (⟨p.val.2, p.property⟩ : U)) := by
      intro p
      apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
      exact hs p
    exact hf.prodMk ht
  contMDiff_invFun := by
    have h : ContMDiff (I.prod J) (I.prod J) n
        (fun p : M × U => (p.1, p.2.val)) :=
      contMDiff_id.prodMap contMDiff_subtype_val
    intro p
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact h p

@[simp] theorem diffeomorph_apply (U : TopologicalSpace.Opens N)
    (p : domain (M := M) U) :
    diffeomorph I J n U p = (p.val.1, ⟨p.val.2, p.property⟩) := rfl

@[simp] theorem diffeomorph_symm_apply (U : TopologicalSpace.Opens N) (p : M × U) :
    (diffeomorph I J n U).symm p = (⟨(p.1, p.2.val), p.2.property⟩ : domain (M := M) U) := rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.ProductOpen
