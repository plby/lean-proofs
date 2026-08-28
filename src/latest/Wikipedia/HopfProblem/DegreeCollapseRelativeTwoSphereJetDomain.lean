import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereChartDomain

/-!
# Generic spatial jets away from the protected region

The actual native-chart spatial jet is smooth on its coupled open domain.
Its parameter derivative is surjective, hence so is its full derivative.
The full derivative remains surjective on the active domain.
Avoidance of nonzero derivative kernels is a separate step.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere

open GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

def chartJet (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 2)) : Vector 2 →L[ℝ] Vector n :=
  fderiv ℝ (fun x ↦ chartCoordinates e r f χ s c (q.1, q.2.1, x)) q.2.2

theorem contDiffOn_chartJet
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartJet e r f χ s c) (chartDomain e r f χ hf hχ s c) := by
  intro q hq
  have hF := (contDiffOn_chartCoordinates e r f χ hf hχ s c).contDiffAt
    ((chartDomain e r f χ hf hχ s c).isOpen.mem_nhds hq)
  have hLift : ContDiff ℝ ∞
      (fun z : (Parameters e × (ℝ × Vector 2)) × Vector 2 ↦ (z.1.1, z.1.2.1, z.2)) := by
    fun_prop
  have hH := hF.comp (q, q.2.2) hLift.contDiffAt
  have hJ : ContDiffAt ℝ ∞ (chartJet e r f χ s c) q :=
    hH.fderiv (contDiff_snd.comp contDiff_snd).contDiffAt (by simp)
  exact hJ.contDiffWithinAt

theorem surjective_fderiv_chartJet
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 2)) (hq : q ∈ chartDomain e r f χ hf hχ s c)
    (hχq : χ (s.symm q.2.2) ≠ 0) :
    Surjective (fderiv ℝ (chartJet e r f χ s c) q) := by
  have hp : Surjective (fderiv ℝ
      (fun p : Parameters e ↦ chartJet e r f χ s c (p, q.2)) q.1) :=
    surjective_fderiv_chart_spatial_parameter e r f χ hf hχ s c q.1 q.2.1 q.2.2
      hq.1.1.2 hq.1.1.1 hχq hq.1.2 hq.2
  have hJ := ((contDiffOn_chartJet e r f χ hf hχ s c).contDiffAt
    ((chartDomain e r f χ hf hχ s c).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × Vector 2)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hJ.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ chartJet e r f χ s c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro L
  obtain ⟨v, hv⟩ := hp L
  exact ⟨(v, 0), hv⟩

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
