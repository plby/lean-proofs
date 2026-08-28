import Wikipedia.HopfProblem.DegreeCollapseNativeLevelWeights
import Wikipedia.HopfProblem.DegreeCollapseNativeSeparatedHeightProfiles

/-!
# Actual stationary cylinder weights with full plateau neighborhoods

Smoothly separating two disjoint closed sets on the original compact level
and composing with the actual inverse cylinder gives full zero and one
germs at every basin point with the corresponding label. These are ambient
germs on the original manifold, not merely germs within the level.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {Z H N E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [CompactSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_native_cylinder_plateau_weight
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = univ) (F : Flow ℝ M) (ι : N → M)
    (hformula : ∀ u, A u = F u.2 (ι u.1))
    {S₀ S₁ : Set N} (hS₀ : IsClosed S₀) (hS₁ : IsClosed S₁) (hdisj : Disjoint S₀ S₁) :
    ∃ w : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w A.target ∧
      (∀ x, w x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ A.target, ∀ t, w (F t x) = w x) ∧
      (∀ x ∈ A.target, (A.symm x).1 ∈ S₀ → w =ᶠ[𝓝 x] fun _ => 0) ∧
      (∀ x ∈ A.target, (A.symm x).1 ∈ S₁ → w =ᶠ[𝓝 x] fun _ => 1) := by
  obtain ⟨θ, hθ₀, hθ₁, hθrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I hS₀ hS₁ hdisj (n := ⊤)
  refine ⟨nativeCylinderWeight A θ, contMDiffOn_nativeCylinderWeight A θ.contMDiff,
    nativeCylinderWeight_mem_Icc A hθrange,
    fun x hx t => nativeCylinderWeight_flow A hsource F ι hformula θ hx t, ?_, ?_⟩
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 0 :=
      hθ₀.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 1 :=
      hθ₁.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
