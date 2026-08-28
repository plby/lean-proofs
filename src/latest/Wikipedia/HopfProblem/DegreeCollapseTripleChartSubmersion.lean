import Wikipedia.HopfProblem.DegreeCollapseTripleParameterSubmersion
import Wikipedia.HopfProblem.DegreeCollapseTripleChartDomain

/-!
# Submersivity of the two actual triple-coincidence equations

Independent variations at the three manifold points survive the common
target chart. Prescribe a zero variation at the first point and independent
variations at the other two. Both target differences can then be prescribed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

theorem hasFDerivAt_chart_parameter (p : Parameters e) (t : ℝ) (x : Sphere 3)
    (hx : ambient e f p t x ∈ r.domain) (d : TargetChart n M)
    (hd : map e r f p t x ∈ d.source) :
    HasFDerivAt (fun q : Parameters e ↦ d (map e r f q t x))
      ((mfderiv (𝓡 n) (𝓡 n) d (map e r f p t x)).comp
        (mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) (fun q ↦ map e r f q t x) p)) p := by
  have hx' := (contMDiffAt_map_parameter e r f p t x hx).mdifferentiableAt (by simp)
  have hloc : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ d (map e r f p t x) :=
    ⟨d, hd, fun _ _ ↦ rfl⟩
  have hd' := hloc.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp p hd' hx'
  rw [mfderiv_eq_fderiv] at hchain
  have H := (hd'.comp p hx').differentiableAt.hasFDerivAt
  exact hchain ▸ H

theorem surjective_fderiv_tripleChartDifference_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (a b c : SourceChart) (d : TargetChart n M) (q : Parameters e × TripleCoordinates)
    (hq : q ∈ tripleDomain e r f hf a b c d) :
    Surjective (fderiv ℝ (fun p : Parameters e ↦ tripleChartDifference e r f a b c d (p, q.2))
      q.1) := by
  let x : Sphere 3 := a.symm q.2.2.1
  let y : Sphere 3 := b.symm q.2.2.2.1
  let z : Sphere 3 := c.symm q.2.2.2.2
  have hx : ambient e f q.1 q.2.1 x ∈ r.domain := hq.1.1.1.1.2
  have hy : ambient e f q.1 q.2.1 y ∈ r.domain := hq.1.1.2.1.2
  have hz : ambient e f q.1 q.2.1 z ∈ r.domain := hq.2.1.1.2.1.2
  have hdx : map e r f q.1 q.2.1 x ∈ d.source := hq.1.1.1.2
  have hdy : map e r f q.1 q.2.1 y ∈ d.source := hq.1.1.2.2
  have hdz : map e r f q.1 q.2.1 z ∈ d.source := hq.2.1.1.2.2
  let u : Parameters e → M := fun p ↦ map e r f p q.2.1 x
  let v : Parameters e → M := fun p ↦ map e r f p q.2.1 y
  let w : Parameters e → M := fun p ↦ map e r f p q.2.1 z
  let D₁ : Parameters e →L[ℝ] Vector n := mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) u q.1
  let D₂ : Parameters e →L[ℝ] Vector n := mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) v q.1
  let D₃ : Parameters e →L[ℝ] Vector n := mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) w q.1
  let C₁ : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) d (u q.1)
  let C₂ : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) d (v q.1)
  let C₃ : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) d (w q.1)
  have h₁ : HasFDerivAt (d ∘ u) (C₁.comp D₁) q.1 :=
    hasFDerivAt_chart_parameter e r f q.1 q.2.1 x hx d hdx
  have h₂ : HasFDerivAt (d ∘ v) (C₂.comp D₂) q.1 :=
    hasFDerivAt_chart_parameter e r f q.1 q.2.1 y hy d hdy
  have h₃ : HasFDerivAt (d ∘ w) (C₃.comp D₃) q.1 :=
    hasFDerivAt_chart_parameter e r f q.1 q.2.1 z hz d hdz
  have he : fderiv ℝ (fun p : Parameters e ↦ tripleChartDifference e r f a b c d (p, q.2))
      q.1 = (C₁.comp D₁ - C₂.comp D₂).prod (C₁.comp D₁ - C₃.comp D₃) :=
    ((h₁.sub h₂).prodMk (h₁.sub h₃)).fderiv
  have hu := (contMDiffAt_map_parameter e r f q.1 q.2.1 x hx).mdifferentiableAt (by simp)
  have hv := (contMDiffAt_map_parameter e r f q.1 q.2.1 y hy).mdifferentiableAt (by simp)
  have hw := (contMDiffAt_map_parameter e r f q.1 q.2.1 z hz).mdifferentiableAt (by simp)
  have htriple := surjective_mfderiv_triple_parameter e r f q.1 q.2.1 x y z
    hq.1.2 hq.2.1.2 hq.2.2.2 hq.1.1.1.1.1.2 hx hy hz
  rw [mfderiv_prodMk hu (hv.prodMk hw), mfderiv_prodMk hv hw] at htriple
  change Surjective (D₁.prod (D₂.prod D₃)) at htriple
  have hloc₂ : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ d (v q.1) :=
    ⟨d, hdy, fun _ _ ↦ rfl⟩
  have hloc₃ : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ d (w q.1) :=
    ⟨d, hdz, fun _ _ ↦ rfl⟩
  have hc₂ : Surjective C₂ := (hloc₂.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hc₃ : Surjective C₃ := (hloc₃.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [he]
  rintro ⟨v₂, v₃⟩
  obtain ⟨a₂, ha₂⟩ := hc₂ (-v₂)
  obtain ⟨a₃, ha₃⟩ := hc₃ (-v₃)
  obtain ⟨p, hp⟩ := htriple (0, a₂, a₃)
  have hp₁ : D₁ p = 0 := congrArg Prod.fst hp
  have hp₂ : D₂ p = a₂ := congrArg (fun v : Vector n × Vector n × Vector n ↦ v.2.1) hp
  have hp₃ : D₃ p = a₃ := congrArg (fun v : Vector n × Vector n × Vector n ↦ v.2.2) hp
  refine ⟨p, Prod.ext ?_ ?_⟩
  · change C₁ (D₁ p) - C₂ (D₂ p) = v₂
    rw [hp₁, hp₂, map_zero, ha₂, zero_sub, neg_neg]
  · change C₁ (D₁ p) - C₃ (D₃ p) = v₃
    rw [hp₁, hp₃, map_zero, ha₃, zero_sub, neg_neg]

theorem surjective_fderiv_tripleChartDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (a b c : SourceChart) (d : TargetChart n M) (q : Parameters e × TripleCoordinates)
    (hq : q ∈ tripleDomain e r f hf a b c d) :
    Surjective (fderiv ℝ (tripleChartDifference e r f a b c d) q) := by
  have hp := surjective_fderiv_tripleChartDifference_parameter e r f hf a b c d q hq
  have hD := ((contDiffOn_tripleChartDifference e r f hf a b c d).contDiffAt
    ((tripleDomain e r f hf a b c d).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) TripleCoordinates) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ tripleChartDifference e r f a b c d (p, q.2))
    q.1 = _ at he
  rw [he] at hp
  intro v
  obtain ⟨p, hp⟩ := hp v
  exact ⟨(p, 0), hp⟩

end Wikipedia.HopfProblem.DegreeCollapse.TripleParameters
