import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-! # Products of native partial diffeomorphisms -/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PartialChart

section VectorProduct

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Identity identifies the vector-space chart with the native product atlas. -/
def vectorProduct : Diffeomorph 𝓘(ℝ, E × F) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
    (E × F) (E × F) ∞ where
  toEquiv := Equiv.refl (E × F)
  contMDiff_toFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  contMDiff_invFun := contMDiff_fst.prodMk_space contMDiff_snd

end VectorProduct

variable {E₁ E₂ F₁ F₂ H₁ H₂ G₁ G₂ X₁ X₂ Y₁ Y₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  {J₁ : ModelWithCorners ℝ F₁ G₁} {J₂ : ModelWithCorners ℝ F₂ G₂}
  [TopologicalSpace X₁] [ChartedSpace H₁ X₁]
  [TopologicalSpace X₂] [ChartedSpace H₂ X₂]
  [TopologicalSpace Y₁] [ChartedSpace G₁ Y₁]
  [TopologicalSpace Y₂] [ChartedSpace G₂ Y₂]

/-- The product retains the actual maps, inverse maps, and product domains. -/
def prod (Φ : PartialDiffeomorph I₁ J₁ X₁ Y₁ ∞)
    (Ψ : PartialDiffeomorph I₂ J₂ X₂ Y₂ ∞) :
    PartialDiffeomorph (I₁.prod I₂) (J₁.prod J₂) (X₁ × X₂) (Y₁ × Y₂) ∞ where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.prodMap Ψ.contMDiffOn_toFun
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.prodMap Ψ.contMDiffOn_invFun

theorem prod_apply (Φ : PartialDiffeomorph I₁ J₁ X₁ Y₁ ∞)
    (Ψ : PartialDiffeomorph I₂ J₂ X₂ Y₂ ∞) (p : X₁ × X₂) :
    prod Φ Ψ p = (Φ p.1, Ψ p.2) := rfl

theorem prod_source (Φ : PartialDiffeomorph I₁ J₁ X₁ Y₁ ∞)
    (Ψ : PartialDiffeomorph I₂ J₂ X₂ Y₂ ∞) :
    (prod Φ Ψ).source = Φ.source ×ˢ Ψ.source := rfl

end Wikipedia.SmoothSixDPoincare.PartialChart
