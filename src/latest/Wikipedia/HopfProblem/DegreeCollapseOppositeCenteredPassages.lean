import Wikipedia.HopfProblem.DegreeCollapseCenteredNormalFactors

/-!
# Choose two actual centered passages with opposite normal determinant

Use the identity and a constructed determinant-minus-one terminal change.
The common factors are promoted to actual equivalences using the first
passage's native transverse derivative. No orientation normalization is
assumed, and both ambient isotopies retain their protected support.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {E M Y N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

theorem opposite_centered_passages_of_normal_factors
    {f : S₂ → M} {g : Y → M} {x : S₂} {y : Y} {O : Set M}
    (n : M → N) (hdim : Module.finrank ℝ N = 3)
    (P : P₃ →L[ℝ] (ℝ × D₂)) (B : (ℝ × D₂) →L[ℝ] N)
    (hchoices : ∀ C : D₂ ≃L[ℝ] D₂, ∃ (c : ℝ) (hc : 0 < c),
      ∃ A : CenteredSheetPassage E f g x y O,
        HasFDerivAt (fun z : P₃ => n (A.family
          ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
          (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
        Bijective (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P))) :
    ∃ A₀ A₁ : CenteredSheetPassage E f g x y O,
      ∃ L₀ L₁ : P₃ ≃L[ℝ] N,
        HasFDerivAt (fun z : P₃ => n (A₀.family
          ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
          L₀.toContinuousLinearMap 0 ∧
        HasFDerivAt (fun z : P₃ => n (A₁.family
          ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
          L₁.toContinuousLinearMap 0 ∧
        (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  obtain ⟨C, hC⟩ := SupportedGerms.exists_linearEquiv_with_det
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (0 : Fin 2)
    (show (-1 : ℝ) ≠ 0 by norm_num)
  have hCneg : C.toLinearMap.det < 0 := by rw [hC]; norm_num
  obtain ⟨c₀, hc₀, A₀, hA₀, hbij₀⟩ := hchoices (ContinuousLinearEquiv.refl ℝ D₂)
  obtain ⟨c₁, hc₁, A₁, hA₁, _⟩ := hchoices C
  let Q₀ := passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ D₂)
  let Q₁ := passageNormalProduct c₁ hc₁.ne' C
  obtain ⟨P', B', hP, hB⟩ := exists_shared_passage_frames P B Q₀ hdim hbij₀
  let L₀ := (P'.trans Q₀).trans B'
  let L₁ := (P'.trans Q₁).trans B'
  have hL₀ : L₀.toContinuousLinearMap = B.comp (Q₀.toContinuousLinearMap.comp P) := by
    change B'.toContinuousLinearMap.comp (Q₀.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  have hL₁ : L₁.toContinuousLinearMap = B.comp (Q₁.toContinuousLinearMap.comp P) := by
    change B'.toContinuousLinearMap.comp (Q₁.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  refine ⟨A₀, A₁, L₀, L₁, ?_, ?_, ?_⟩
  · rw [hL₀]
    exact hA₀
  · rw [hL₁]
    exact hA₁
  · exact passage_normal_relative_det_neg P' B' hc₀ hc₁ C hCneg

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
