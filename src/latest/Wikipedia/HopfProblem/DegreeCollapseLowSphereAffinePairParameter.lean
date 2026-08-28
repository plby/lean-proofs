import Wikipedia.HopfProblem.DegreeCollapseLowSphereAffinePairDomain

/-!

# Parameter submersivity of the actual off-diagonal chart difference

The actual two-point parameter map is submersive. Valid target charts and
subtraction preserve the required surjectivity, so the coordinate difference
has a surjective parameter derivative on each genuine two-source-chart
domain in every source dimension.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere d → M)

theorem surjective_fderiv_chartDifference_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f))
    (s z : (SourceChart d)) (c : TargetChart n M)
    (q : Parameters e d × (ℝ × (Vector d × Vector d))) (hq : q ∈ pairDomain e r f hf s z c) :
    Surjective (fderiv ℝ (fun p : Parameters e d ↦ chartDifference e r f s z c (p, q.2)) q.1) := by
  have hleft := hq.1.1
  have hright := hq.1.2
  let u : Parameters e d → M := fun p ↦ map e r f p q.2.1 (s.symm q.2.2.1)
  let v : Parameters e d → M := fun p ↦ map e r f p q.2.1 (z.symm q.2.2.2)
  have hu₀ := contMDiffAt_map_parameter e r f q.1 q.2.1 (s.symm q.2.2.1) hleft.1.2
  have hv₀ := contMDiffAt_map_parameter e r f q.1 q.2.1 (z.symm q.2.2.2) hright.1.2
  have hu : MDifferentiableAt 𝓘(ℝ, Parameters e d) (𝓡 n) u q.1 :=
    hu₀.mdifferentiableAt (by simp)
  have hv : MDifferentiableAt 𝓘(ℝ, Parameters e d) (𝓡 n) v q.1 :=
    hv₀.mdifferentiableAt (by simp)
  have hcu : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (u q.1) :=
    ⟨c, hleft.2, fun _ _ ↦ rfl⟩
  have hcv : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (v q.1) :=
    ⟨c, hright.2, fun _ _ ↦ rfl⟩
  let D₁ : Parameters e d →L[ℝ] Vector n := mfderiv 𝓘(ℝ, Parameters e d) (𝓡 n) u q.1
  let D₂ : Parameters e d →L[ℝ] Vector n := mfderiv 𝓘(ℝ, Parameters e d) (𝓡 n) v q.1
  let C₁ : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) c (u q.1)
  let C₂ : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) c (v q.1)
  have he : fderiv ℝ (fun p : Parameters e d ↦ chartDifference e r f s z c (p, q.2)) q.1 =
      C₁.comp D₁ - C₂.comp D₂ := by
    have hu' := (hcu.mdifferentiableAt (by simp)).comp q.1 hu
    have hv' := (hcv.mdifferentiableAt (by simp)).comp q.1 hv
    have h₁ : fderiv ℝ (c ∘ u) q.1 = C₁.comp D₁ := by
      have h := mfderiv_comp q.1 (hcu.mdifferentiableAt (by simp)) hu
      rw [mfderiv_eq_fderiv] at h
      exact h
    have h₂ : fderiv ℝ (c ∘ v) q.1 = C₂.comp D₂ := by
      have h := mfderiv_comp q.1 (hcv.mdifferentiableAt (by simp)) hv
      rw [mfderiv_eq_fderiv] at h
      exact h
    change fderiv ℝ ((c ∘ u) - (c ∘ v)) q.1 = _
    rw [fderiv_sub hu'.differentiableAt hv'.differentiableAt, h₁, h₂]
  have hpair := surjective_mfderiv_pair_parameter e r f q.1 q.2.1
    (s.symm q.2.2.1) (z.symm q.2.2.2) hq.2 hleft.1.1.2 hleft.1.2 hright.1.2
  change Surjective (mfderiv 𝓘(ℝ, Parameters e d) ((𝓡 n).prod (𝓡 n))
    (fun p ↦ (u p, v p)) q.1) at hpair
  rw [mfderiv_prodMk hu hv] at hpair
  change Surjective (D₁.prod D₂) at hpair
  have hc₁ : Surjective C₁ := (hcu.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [he]
  intro w
  obtain ⟨a, ha⟩ := hc₁ w
  obtain ⟨b, hb⟩ := hpair (a, 0)
  have hb₁ : D₁ b = a := congrArg Prod.fst hb
  have hb₂ : D₂ b = 0 := congrArg Prod.snd hb
  refine ⟨b, ?_⟩
  change C₁ (D₁ b) - C₂ (D₂ b) = w
  rw [hb₁, hb₂, map_zero, sub_zero, ha]


end Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine
