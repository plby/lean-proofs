import Wikipedia.HopfProblem.DegreeCollapseNormalProjectionTrace

/-!
# Shared actual normal factors for all terminal sheet choices

Construct the same source and target linear maps before choosing a terminal
normal change. Every choice is realized by a centered supported passage;
its actual radial normal derivative has the stated factorization and is
bijective by native transversality.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2
local notation "W₅" => ℝ × (D₂ × D₂)

variable {E M Y Z N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]
  [TopologicalSpace Z] [ChartedSpace D₂ Z] [IsManifold (𝓡 2) ∞ Z]
  [SecondCountableTopology Z]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

theorem exists_centered_passage_normal_factors
    {f : S₂ → M} {g : Y → M} {b : Z → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (range f) (range g))
    (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b) (hbc : IsClosed (range b))
    (hdim : Module.finrank ℝ E = 5) (x : S₂) (y : Y)
    (hbx : f x ∉ range b) (hby : g y ∉ range b) (γ : Path (f x) (g y))
    (n : M → N) (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (g y))
    (hsurj : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp
      (mfderiv (𝓡 2) 𝓘(ℝ, E) g y) = 0)
    (hdimN : Module.finrank ℝ N = 3) :
    ∃ (P : P₃ →L[ℝ] (ℝ × D₂)) (B : (ℝ × D₂) →L[ℝ] N),
      ∀ C : D₂ ≃L[ℝ] D₂, ∃ (c : ℝ) (hc : 0 < c),
        ∃ A : CenteredSheetPassage E f g x y (range b),
          HasFDerivAt (fun z : P₃ => n (A.family
            ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
            (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
          Bijective (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) := by
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, _, hchoices⟩ :=
    exists_relative_sheet_passages_with_normal_change hf hg hfe hge hfi hgi hdisj
      hb hbc hdim x y hbx hby γ
  let Ψ := radialParameterChart (1 / 2) x
  have hΨ0 : (0 : P₃) ∈ Ψ.source := radialParameterChart_zero_mem_source (1 / 2) x
  have hΨpoint : Ψ 0 = ((1 / 2 : ℝ), x) := radialParameterChart_zero (1 / 2) x
  let J : P₃ →L[ℝ] (ℝ × D₂) := mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Ψ 0
  let K : D₂ →L[ℝ] D₂ :=
    mfderiv (𝓡 2) 𝓘(ℝ, D₂) (fun q : S₂ => (Φ₀.symm (f q)).2.1) x
  let P : P₃ →L[ℝ] (ℝ × D₂) := ((ContinuousLinearMap.id ℝ ℝ).prodMap K).comp J
  let G : (ℝ × D₂) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  let B : (ℝ × D₂) →L[ℝ] N := fderiv ℝ G 0
  have hnΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ₁ (1, 0)) := by rw [hΦy]; exact hn
  have hB : HasFDerivAt G B 0 := hasFDerivAt_terminal_normal_factor Φ₁ hΦ₁ hnΦ
  refine ⟨P, B, ?_⟩
  intro C
  obtain ⟨R, ε, hε, Φ, A, hprod, _, _, hleft, hright, _, _, havoid, _, hcross, htrans⟩ :=
    hchoices C
  have h0 : (0 : W₅) ∈ Φ.source :=
    hprod ⟨⟨le_rfl, zero_le_one⟩, mem_closedBall_self hε.le⟩
  obtain ⟨D, hD0, _, hDpoint, _, hDinterval, _, hDder⟩ :=
    exists_centered_passage_clock A.time_mem
  let T := A.centeredSheetPassage D hD0 hDpoint hDinterval havoid hcross
  let c : ℝ := deriv Real.smoothTransition A.time * A.destination
  have hc : 0 < c := A.time_rate
  let F : ℝ × S₂ → M := fun p => A.family (p.1, f p.2)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ F :=
    A.smooth.comp (contMDiff_fst.prodMk (hf.comp contMDiff_snd))
  have hpoint : F (A.time, x) = g y :=
    (hcross A.time ⟨A.time_mem.1.le, A.time_mem.2.le⟩ x y).mpr ⟨rfl, rfl, rfl⟩
  have hnF : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (F (A.time, x)) := by rw [hpoint]; exact hn
  let NF : ℝ × S₂ → N := n ∘ F
  have hNF : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :=
    (hnF.comp (A.time, x) hF.contMDiffAt).mdifferentiableAt (by simp)
  have hNFbij : Bijective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x)) :=
    bijective_trace_normal_of_native_transverse (hF.mdifferentiable (by simp) (A.time, x))
      (hn.mdifferentiableAt (by simp)) hpoint.symm htrans hsurj hzero
      (by simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdimN])
  have hret : fderiv ℝ (fun z : P₃ => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) : (ℝ × D₂) →L[ℝ] N).comp J :=
    fderiv_retimed_trace_parameter hNF hDder hDpoint Ψ hΨ0 hΨpoint
  have hfactor : (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :
      (ℝ × D₂) →L[ℝ] N) = B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).prodMap
          (C.toContinuousLinearMap.comp K)) :=
    A.normal_trace_mfderiv Φ₀ Φ₁ C R (hf.mdifferentiable (by simp) x)
      h0 hΦ₀ hΦx hrec₀ hleft hright n B hB
  have heq : fderiv ℝ (fun z : P₃ => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P) := by
    rw [hret, hfactor]
    apply ContinuousLinearMap.ext
    intro z
    change B ((J z).1 * c, C (K (J z).2)) = B (c * (J z).1, C (K (J z).2))
    rw [mul_comm]
  let H : ℝ × S₂ → N := fun p => NF (D p.1, p.2)
  have hNF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (D (1 / 2), x) := by
    rw [hDpoint]
    exact hNF
  have hH : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (1 / 2, x) :=
    MDifferentiableAt.comp (g := NF) (f := fun p : ℝ × S₂ => (D p.1, p.2))
      (1 / 2, x) hNF' ((hDder.differentiableAt.mdifferentiableAt.comp
      (1 / 2, x) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have hH' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (Ψ 0) := by
    rw [hΨpoint]
    exact hH
  have hdiff : DifferentiableAt ℝ (fun z : P₃ => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 :=
    (hH'.comp 0 (Ψ.mdifferentiableAt (by simp) hΨ0)).differentiableAt
  have hder : HasFDerivAt (fun z : P₃ => n (T.family ((Ψ z).1, f (Ψ z).2)))
      (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 := by
    rw [← heq]
    exact hdiff.hasFDerivAt
  have hbij : Bijective (fderiv ℝ (fun z : P₃ => n (T.family ((Ψ z).1, f (Ψ z).2))) 0) := by
    rw [hret]
    exact hNFbij.comp (PartialChart.bijective_mfderiv Ψ hΨ0)
  exact ⟨c, hc, T, hder, heq ▸ hbij⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
