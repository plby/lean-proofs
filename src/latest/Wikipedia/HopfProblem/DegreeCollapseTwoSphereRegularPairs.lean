import Wikipedia.HopfProblem.DegreeCollapseTwoSpherePairDomain
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Almost-everywhere regular double points for the actual manifold perturbation

The actual two-point parameter map is submersive. Valid target charts and
subtraction preserve the required surjectivity, so parametric Sard gives
regular zeros on each genuine two-source-chart domain.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation

open NoExoticSixSphere
open GLOrthonormalization EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 2 → M)

theorem surjective_fderiv_chartDifference_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2))) (hq : q ∈ pairDomain e r f hf s z c) :
    Surjective (fderiv ℝ (fun p : Parameters e ↦ chartDifference e r f s z c (p, q.2)) q.1) := by
  have hleft := hq.1.1
  have hright := hq.1.2
  let u : Parameters e → M := fun p ↦ map e r f p q.2.1 (s.symm q.2.2.1)
  let v : Parameters e → M := fun p ↦ map e r f p q.2.1 (z.symm q.2.2.2)
  have hu₀ := contMDiffAt_map_parameter e r f q.1 q.2.1 (s.symm q.2.2.1) hleft.1.2
  have hv₀ := contMDiffAt_map_parameter e r f q.1 q.2.1 (z.symm q.2.2.2) hright.1.2
  have hu : MDifferentiableAt 𝓘(ℝ, Parameters e) (𝓡 n) u q.1 :=
    hu₀.mdifferentiableAt (by simp)
  have hv : MDifferentiableAt 𝓘(ℝ, Parameters e) (𝓡 n) v q.1 :=
    hv₀.mdifferentiableAt (by simp)
  have hcu : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (u q.1) :=
    ⟨c, hleft.2, fun _ _ ↦ rfl⟩
  have hcv : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (v q.1) :=
    ⟨c, hright.2, fun _ _ ↦ rfl⟩
  let D₁ : Parameters e →L[ℝ] Vector n := mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) u q.1
  let D₂ : Parameters e →L[ℝ] Vector n := mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) v q.1
  let C₁ : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) c (u q.1)
  let C₂ : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) c (v q.1)
  have he : fderiv ℝ (fun p : Parameters e ↦ chartDifference e r f s z c (p, q.2)) q.1 =
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
  change Surjective (mfderiv 𝓘(ℝ, Parameters e) ((𝓡 n).prod (𝓡 n))
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

theorem surjective_fderiv_chartDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2))) (hq : q ∈ pairDomain e r f hf s z c) :
    Surjective (fderiv ℝ (chartDifference e r f s z c) q) := by
  have hp := surjective_fderiv_chartDifference_parameter e r f hf s z c q hq
  have hD := ((contDiffOn_chartDifference e r f hf s z c).contDiffAt
    ((pairDomain e r f hf s z c).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × (Vector 2 × Vector 2))) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ chartDifference e r f s z c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro w
  obtain ⟨v, hv⟩ := hp w
  exact ⟨(v, 0), hv⟩

theorem ae_regular_chart_double_points
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s z : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 2 × Vector 2), (p, x) ∈ pairDomain e r f hf s z c →
      chartDifference e r f s z c (p, x) = 0 →
        Surjective (fderiv ℝ (fun y ↦ chartDifference e r f s z c (p, y)) x) :=
  ParametricRegular.ae_parameters_on μ (chartDifference e r f s z c)
    (pairDomain e r f hf s z c) (contDiffOn_chartDifference e r f hf s z c)
    (fun q hq _ ↦ surjective_fderiv_chartDifference e r f hf s z c q hq)

end Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation
