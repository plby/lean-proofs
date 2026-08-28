import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereJetDomain
import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereRegularPairs
import Wikipedia.HopfProblem.DegreeCollapseParametricAvoidance

/-!
# Relative two-sphere families avoid active collisions and derivative kernels

The time, source, and nonzero tangent-vector test has dimension five.
The active distinct-pair test also has dimension five, including pairs
with one protected point. Their actual parameter derivatives are onto.
Parametric Sard excludes every zero in target dimension above five.
-/

noncomputable section

open Set Function TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters SourceChart TargetChart pairLeft contDiff_pairLeft)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

def kernelDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (ℝ × (Vector 2 × Vector 2))) :=
  ⟨pairLeft e ⁻¹' (activeChartDomain e r f χ hf hχ s c : Set _) ∩ {q | q.2.2.2 ≠ 0},
    ((activeChartDomain e r f χ hf hχ s c).isOpen.preimage (contDiff_pairLeft e).continuous).inter
      (isClosed_eq (by fun_prop) continuous_const).isOpen_compl⟩

def kernelTest (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2))) : Vector n :=
  chartJet e r f χ s c (pairLeft e q) q.2.2.2

theorem contDiffOn_kernelTest
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (kernelTest e r f χ s c) (kernelDomain e r f χ hf hχ s c) := by
  have hJ : ContDiffOn ℝ ∞
      (fun q => chartJet e r f χ s c (pairLeft e q)) (kernelDomain e r f χ hf hχ s c) :=
    (contDiffOn_chartJet e r f χ hf hχ s c).comp
      (contDiff_pairLeft e).contDiffOn (fun _ hq => hq.1.1)
  have hv : ContDiff ℝ ∞
      (fun q : Parameters e × (ℝ × (Vector 2 × Vector 2)) => q.2.2.2) := by fun_prop
  exact hJ.clm_apply hv.contDiffOn

theorem surjective_fderiv_kernelTest_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2)))
    (hq : q ∈ kernelDomain e r f χ hf hχ s c) :
    Surjective (fderiv ℝ (fun p : Parameters e => kernelTest e r f χ s c (p, q.2)) q.1) := by
  have hbase := hq.1.1
  have hJ : Surjective (fderiv ℝ
      (fun p : Parameters e => chartJet e r f χ s c (p, q.2.1, q.2.2.1)) q.1) :=
    surjective_fderiv_chart_spatial_parameter e r f χ hf hχ s c q.1 q.2.1 q.2.2.1
      hbase.1.1.2 hbase.1.1.1 hq.1.2 hbase.1.2 hbase.2
  have hs := (contDiffOn_chartJet e r f χ hf hχ s c).contDiffAt
    ((chartDomain e r f χ hf hχ s c).isOpen.mem_nhds hbase)
  have hparam : DifferentiableAt ℝ
      (fun p : Parameters e => chartJet e r f χ s c (p, q.2.1, q.2.2.1)) q.1 :=
    (hs.comp q.1 (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
  let L := ContinuousLinearMap.apply ℝ (Vector n) q.2.2.2
  have hL : Surjective L := ParametricRegular.operator_evaluation_surjective q.2.2.2 hq.2
  change Surjective (fderiv ℝ
    (L ∘ fun p : Parameters e => chartJet e r f χ s c (p, q.2.1, q.2.2.1)) q.1)
  rw [fderiv_comp q.1 L.differentiableAt hparam, L.fderiv]
  exact hL.comp hJ

theorem ae_no_chart_kernel
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (hdim : 5 < n) (s : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 2 × Vector 2),
      (p, x) ∈ kernelDomain e r f χ hf hχ s c → kernelTest e r f χ s c (p, x) ≠ 0 := by
  apply ParametricAvoidance.ae_avoid_zero_of_parameter μ (kernelTest e r f χ s c)
    (kernelDomain e r f χ hf hχ s c) (contDiffOn_kernelTest e r f χ hf hχ s c)
    (surjective_fderiv_kernelTest_parameter e r f χ hf hχ s c)
  simpa only [GLOrthonormalization.Vector, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace_fin] using hdim

theorem ae_injective_chart_jets
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (hdim : 5 < n) (s : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × Vector 2, (p, x) ∈ activeChartDomain e r f χ hf hχ s c →
      Injective (chartJet e r f χ s c (p, x)) := by
  filter_upwards [ae_no_chart_kernel e r f χ μ hf hχ hdim s c] with p hp
  intro x hx
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  by_contra hne
  exact hp (x.1, x.2, v) ⟨hx, hne⟩ hv

theorem ae_no_chart_double_points
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (hdim : 5 < n) (s z : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 2 × Vector 2),
      (p, x) ∈ activePairDomain e r f χ hf hχ s z c →
        chartDifference e r f χ s z c (p, x) ≠ 0 := by
  apply ParametricAvoidance.ae_avoid_zero_of_parameter μ (chartDifference e r f χ s z c)
    (activePairDomain e r f χ hf hχ s z c)
    ((contDiffOn_chartDifference e r f χ hf hχ s z c).mono inter_subset_left)
    (surjective_fderiv_chartDifference_parameter e r f χ hf hχ s z c)
  simpa only [GLOrthonormalization.Vector, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace_fin] using hdim

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
