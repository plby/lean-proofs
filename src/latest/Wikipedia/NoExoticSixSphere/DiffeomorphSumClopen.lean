import Wikipedia.NoExoticSixSphere.OpenPreimageDiffeomorph

/-!
# Native clopen pieces of a manifold diffeomorphic to a disjoint union

The two summands have their original atlases. The images carry the
target manifold's inherited open-subset atlases, and the actual inverse
of the given diffeomorphism identifies both pieces and their complements.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiffeomorphSumClopen

variable (M₁ M₂ : Type*) [TopologicalSpace M₁] [TopologicalSpace M₂]

def leftOpen : Opens (M₁ ⊕ M₂) := ⟨range Sum.inl, isOpen_range_inl⟩

def rightOpen : Opens (M₁ ⊕ M₂) := ⟨range Sum.inr, isOpen_range_inr⟩

variable {M₁ M₂}
  {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [ChartedSpace H M₁] [ChartedSpace H M₂]

def leftDiffeomorph : M₁ ≃ₘ⟮I, I⟯ leftOpen M₁ M₂ := by
  let e : M₁ ≃ leftOpen M₁ M₂ := Equiv.ofInjective Sum.inl Sum.inl_injective
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact (ContMDiff.subtypeVal_comp_iff (leftOpen M₁ M₂) e).mp ContMDiff.inl
  · apply contMDiff_of_contMDiff_inl (N' := M₂)
    have he : Sum.inl ∘ e.symm = (Subtype.val : leftOpen M₁ M₂ → M₁ ⊕ M₂) := by
      funext p
      exact congrArg Subtype.val (e.apply_symm_apply p)
    rw [he]
    exact contMDiff_subtype_val

def rightDiffeomorph : M₂ ≃ₘ⟮I, I⟯ rightOpen M₁ M₂ := by
  let e : M₂ ≃ rightOpen M₁ M₂ := Equiv.ofInjective Sum.inr Sum.inr_injective
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact (ContMDiff.subtypeVal_comp_iff (rightOpen M₁ M₂) e).mp ContMDiff.inr
  · apply contMDiff_of_contMDiff_inr (N := M₁)
    have he : Sum.inr ∘ e.symm = (Subtype.val : rightOpen M₁ M₂ → M₁ ⊕ M₂) := by
      funext p
      exact congrArg Subtype.val (e.apply_symm_apply p)
    rw [he]
    exact contMDiff_subtype_val

theorem leftDiffeomorph_val (x : M₁) :
    (leftDiffeomorph (I := I) (M₂ := M₂) x).val = Sum.inl x := rfl

theorem rightDiffeomorph_val (x : M₂) :
    (rightDiffeomorph (I := I) (M₁ := M₁) x).val = Sum.inr x := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (D : (M₁ ⊕ M₂) ≃ₘ⟮I, I⟯ M)

def leftImage : Opens M := openDiffeomorphPreimage D.symm (leftOpen M₁ M₂)

def rightImage : Opens M := openDiffeomorphPreimage D.symm (rightOpen M₁ M₂)

theorem leftImage_closed : IsClosed (leftImage D : Set M) :=
  isClosed_range_inl.preimage D.symm.continuous

theorem rightImage_closed : IsClosed (rightImage D : Set M) :=
  isClosed_range_inr.preimage D.symm.continuous

def leftImageDiffeomorph : M₁ ≃ₘ⟮I, I⟯ leftImage D :=
  (leftDiffeomorph (I := I)).trans (openPreimageDiffeomorph D.symm (leftOpen M₁ M₂)).symm

def rightImageDiffeomorph : M₂ ≃ₘ⟮I, I⟯ rightImage D :=
  (rightDiffeomorph (I := I)).trans (openPreimageDiffeomorph D.symm (rightOpen M₁ M₂)).symm

theorem leftImageDiffeomorph_val (x : M₁) :
    (leftImageDiffeomorph D x).val = D (Sum.inl x) := rfl

theorem rightImageDiffeomorph_val (x : M₂) :
    (rightImageDiffeomorph D x).val = D (Sum.inr x) := rfl

theorem leftImage_compl : (leftImage D : Set M)ᶜ = rightImage D := by
  ext p
  change D.symm p ∉ range Sum.inl ↔ D.symm p ∈ range Sum.inr
  cases D.symm p <;> simp

def leftComplementHomeomorph : ↥((leftImage D : Set M)ᶜ) ≃ₜ M₂ :=
  (Homeomorph.setCongr (leftImage_compl D)).trans (rightImageDiffeomorph D).symm.toHomeomorph

end NoExoticSixSphere.DiffeomorphSumClopen
