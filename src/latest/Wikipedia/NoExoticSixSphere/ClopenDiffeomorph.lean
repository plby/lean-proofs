import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential
import Wikipedia.NoExoticSixSphere.LocalDiffeomorphSmoothMaps

/-! # Splitting a smooth manifold along an open-and-closed subset -/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

def clopenComplement (U : Opens M) (hU : IsClosed (U : Set M)) : Opens M :=
  ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩

def clopenDiffeomorph (U : Opens M) (hU : IsClosed (U : Set M)) :
    (U ⊕ clopenComplement U hU) ≃ₘ⟮I, I⟯ M := by
  classical
  let e : (U ⊕ clopenComplement U hU) ≃ M := Equiv.Set.sumCompl (U : Set M)
  refine
    { toEquiv := e
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (_root_.contMDiff_subtype_val (I := I) (U := U)).sumElim
      (_root_.contMDiff_subtype_val (I := I) (U := clopenComplement U hU))
  · intro x
    by_cases hx : x ∈ U
    · let y : U := ⟨x, hx⟩
      apply (contMDiffAt_comp_localDiffeomorph_iff
        (isLocalDiffeomorphAt_openSubset_val (I := I) U y) e.symm).mp
      have he : e.symm ∘ (Subtype.val : U → M) = Sum.inl :=
        funext (fun p ↦ Equiv.Set.sumCompl_symm_apply p)
      rw [he]
      exact ContMDiff.inl.contMDiffAt
    · let V := clopenComplement U hU
      let y : V := ⟨x, hx⟩
      apply (contMDiffAt_comp_localDiffeomorph_iff
        (isLocalDiffeomorphAt_openSubset_val (I := I) V y) e.symm).mp
      have he : e.symm ∘ (Subtype.val : V → M) = Sum.inr :=
        funext (fun p ↦ Equiv.Set.sumCompl_symm_apply_compl p)
      rw [he]
      exact ContMDiff.inr.contMDiffAt

theorem clopenDiffeomorph_inl (U : Opens M) (hU : IsClosed (U : Set M)) (x : U) :
    clopenDiffeomorph (I := I) U hU (Sum.inl x) = x.val := rfl

theorem clopenDiffeomorph_inr (U : Opens M) (hU : IsClosed (U : Set M))
    (x : clopenComplement U hU) :
    clopenDiffeomorph (I := I) U hU (Sum.inr x) = x.val := rfl

end NoExoticSixSphere
