import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereChartDomain
import Wikipedia.NoExoticSixSphere.GenericThreeSixSubmersion

/-!
# Generic spatial jets away from the protected region

The actual native-chart spatial jet is smooth on its coupled open domain.
Its parameter derivative is surjective, hence so is its full derivative.
The established parametric rank theorem therefore gives almost-everywhere
regular three-to-six jets without perturbing the cutoff zero set.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SpatiallyRelativeSphereFamily

open GLOrthonormalization EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)

def chartJet (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 3)) : Vector 3 →L[ℝ] Vector n :=
  fderiv ℝ (fun x ↦ chartCoordinates e r f χ s c (q.1, q.2.1, x)) q.2.2

theorem contDiffOn_chartJet
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartJet e r f χ s c) (chartDomain e r f χ hf hχ s c) := by
  intro q hq
  have hF := (contDiffOn_chartCoordinates e r f χ hf hχ s c).contDiffAt
    ((chartDomain e r f χ hf hχ s c).isOpen.mem_nhds hq)
  have hLift : ContDiff ℝ ∞
      (fun z : (Parameters e × (ℝ × Vector 3)) × Vector 3 ↦ (z.1.1, z.1.2.1, z.2)) := by
    fun_prop
  have hH := hF.comp (q, q.2.2) hLift.contDiffAt
  have hJ : ContDiffAt ℝ ∞ (chartJet e r f χ s c) q :=
    hH.fderiv (contDiff_snd.comp contDiff_snd).contDiffAt (by simp)
  exact hJ.contDiffWithinAt

theorem surjective_fderiv_chartJet
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 3)) (hq : q ∈ chartDomain e r f χ hf hχ s c)
    (hχq : χ (s.symm q.2.2) ≠ 0) :
    Surjective (fderiv ℝ (chartJet e r f χ s c) q) := by
  have hp : Surjective (fderiv ℝ
      (fun p : Parameters e ↦ chartJet e r f χ s c (p, q.2)) q.1) :=
    surjective_fderiv_chart_spatial_parameter e r f χ hf hχ s c q.1 q.2.1 q.2.2
      hq.1.1.2 hq.1.1.1 hχq hq.1.2 hq.2
  have hJ := ((contDiffOn_chartJet e r f χ hf hχ s c).contDiffAt
    ((chartDomain e r f χ hf hχ s c).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × Vector 3)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hJ.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ chartJet e r f χ s c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro L
  obtain ⟨v, hv⟩ := hp L
  exact ⟨(v, 0), hv⟩

theorem ae_regular_chart_jets [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hn : n = 6) (s : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, OperatorRank.RegularThreeSixOn
      (fun z : ℝ × Vector 3 ↦ chartJet e r f χ s c (p, z))
      {z | (p, z) ∈ activeChartDomain e r f χ hf hχ s c} :=
  OperatorRank.ae_regular_three_six_of_submersion μ (chartJet e r f χ s c)
    (activeChartDomain e r f χ hf hχ s c)
    ((contDiffOn_chartJet e r f χ hf hχ s c).mono inter_subset_left)
    (fun q hq ↦ surjective_fderiv_chartJet e r f χ hf hχ s c q hq.1 hq.2)
    (by simp [GLOrthonormalization.Vector]) (by simp [GLOrthonormalization.Vector])
    (by simp [GLOrthonormalization.Vector, hn])

end NoExoticSixSphere.SpatiallyRelativeSphereFamily
