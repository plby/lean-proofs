import Wikipedia.HopfProblem.DegreeCollapseMutualSheetBigon
import Wikipedia.HopfProblem.DegreeCollapseMutualSheetSigns
import Wikipedia.SmoothSixDPoincare.NativeWhitneyCancellation
import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-!
# Actual cancellation of two opposite mutual intersections

The original compact embedded sheets lie in a simply connected smooth
six-manifold. Opposite intrinsic ordered signs construct a clean Whitney
bigon, its compatible framing and chart, and a smooth ambient isotopy
moving only the first sheet. Exactly the selected two intersection points
are removed. One compact support misses every surviving crossing.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare WhitneyPairModel
open OrbitPair.DeterminantSignCover

variable {D E M N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [T2Space N] [CompactSpace N] [PathConnectedSpace N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  [T2Space P] [CompactSpace P] [PathConnectedSpace P]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, D) N))
  (oP : Orientation (tangentBundleCore 𝓘(ℝ, D) P))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (K : (D × D) ≃L[ℝ] E)

theorem exists_opposite_pair_cancellation
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G)
    (hinjF : Injective F) (hinjG : Injective G)
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (ht : ∀ x y, G y = F x → Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hc₀ : G y₀ = F x₀) (hc₁ : G y₁ = F x₁)
    (hsign : intersectionSign oN oP oM K F G x₀ y₀ ≠
      intersectionSign oN oP oM K F G x₁ y₁) :
    ∃ C : Set M, IsCompact C ∧ Disjoint C ((range F ∩ range G) \ {F x₀, F x₁}) ∧
      ∃ ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
        SupportedDiffeomorph.IsotopicToIdentity ψ ∧
        (∀ z, z ∉ C → ψ z = z) ∧
        (ψ '' range F) ∩ range G = (range F ∩ range G) \ {F x₀, F x₁} := by
  have hne : x₀ ≠ x₁ := by
    intro he
    have hy : y₀ = y₁ := hinjG (hc₀.trans ((congrArg F he).trans hc₁.symm))
    exact hsign (by rw [he, hy])
  let J : Sheet ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Sheet, Plane, Module.finrank_prod, hsheet])
  letI : Nontrivial D := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : D)
  obtain ⟨B⟩ := nonempty_bigonData hdim hsheet hF hG hinjF hinjG hiF hiG ht hc₀ hc₁ hne
    (PathConnectedSpace.somePath x₀ x₁) (PathConnectedSpace.somePath y₀ y₁) hu hu hu hu
  have ht' (x : N) (y : P) (hc : G y = F x) : Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x)) := by
    let A : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x
    let B : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y
    exact TransverseCoordinates.surjective_coprod_swap A B (ht x y hc)
  have hends : ∀ t : ℝ, t = 0 ∨ t = 1 → Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G (B.rightArc t)).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (B.leftArc t))) := by
    intro t htI
    change Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G (B.rightArc t) : D →L[ℝ] E).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (B.leftArc t) : D →L[ℝ] E))
    rcases htI with rfl | rfl
    · rw [B.left_zero, B.right_zero]
      exact ht' x₀ y₀ hc₀
    · rw [B.left_one, B.right_one]
      exact ht' x₁ y₁ hc₁
  have hs : intersectionSign oN oP oM K F G (B.leftArc 0) (B.rightArc 0) ≠
      intersectionSign oN oP oM K F G (B.leftArc 1) (B.rightArc 1) := by
    simpa only [B.left_zero, B.left_one, B.right_zero, B.right_one] using hsign
  have hcorner := opposite_signs_imply_opposite_corner_determinants oN oP oM J K
    B.tube B.lowerNormal B.upperNormal hF hG hiF hiG hends hs
  obtain ⟨c⟩ := B.tube.nonempty_compatibleChart_of_opposite_corner_signs
    B.lowerNormal B.upperNormal (isCompact_range hF.continuous).isClosed
      (isCompact_range hG.continuous).isClosed hcorner
  obtain ⟨C, hC, hCt, A, hA, hA0, hAt, hfix, hcancel⟩ := c.exists_cancellation
  obtain ⟨ψ, hψ⟩ := hAt 1
  have hdis : Disjoint C ((range F ∩ range G) \ {F x₀, F x₁}) := by
    apply Set.disjoint_left.mpr
    intro z hzC hz
    have hz' : z ∈ (range F ∩ range G) ∩ c.chart.target := ⟨hz.1, hCt hzC⟩
    rw [c.intersection_in_target_eq] at hz'
    apply hz.2
    simpa only [Function.comp_apply, B.left_zero, B.left_one] using hz'
  refine ⟨C, hC, hdis, ψ, ⟨A, hA, hA0, hψ, hAt⟩, ?_, ?_⟩
  · intro z hz
    exact (hψ z).symm.trans (hfix 1 z hz)
  · rw [funext hψ] at hcancel
    simpa only [Function.comp_apply, B.left_zero, B.left_one] using hcancel

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets
