import Wikipedia.HopfProblem.DegreeCollapseTwoSphereJetDomain
import Wikipedia.HopfProblem.DegreeCollapseTwoSphereRegularPairs
import Wikipedia.HopfProblem.DegreeCollapseParametricAvoidance

/-!
# Two-sphere families avoid both collisions and spatial derivative kernels

The same-time distinct-pair domain has dimension five. The spatial kernel
test has time, a two-dimensional source coordinate, and a nonzero
two-dimensional tangent vector, again dimension five. The actual affine
parameter derivatives are submersive in both tests. Parametric Sard
therefore excludes their zeros when the target dimension exceeds five.
The zero tangent vector is explicitly excluded from the open kernel domain.
-/

noncomputable section

open Set Function TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 2 → M)

def kernelDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (ℝ × (Vector 2 × Vector 2))) :=
  ⟨pairLeft e ⁻¹' (chartDomain e r f hf s c : Set _) ∩ {q | q.2.2.2 ≠ 0},
    ((chartDomain e r f hf s c).isOpen.preimage (contDiff_pairLeft e).continuous).inter
      (isClosed_eq (by fun_prop) continuous_const).isOpen_compl⟩

def kernelTest (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2))) : Vector n :=
  chartJet e r f s c (pairLeft e q) q.2.2.2

theorem contDiffOn_kernelTest
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (kernelTest e r f s c) (kernelDomain e r f hf s c) := by
  have hJ : ContDiffOn ℝ ∞
      (fun q => chartJet e r f s c (pairLeft e q)) (kernelDomain e r f hf s c) :=
    (contDiffOn_chartJet e r f hf s c).comp
    (contDiff_pairLeft e).contDiffOn (fun _ hq => hq.1)
  have hv : ContDiff ℝ ∞
      (fun q : Parameters e × (ℝ × (Vector 2 × Vector 2)) => q.2.2.2) := by fun_prop
  exact hJ.clm_apply hv.contDiffOn

theorem surjective_fderiv_kernelTest_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2)))
    (hq : q ∈ kernelDomain e r f hf s c) :
    Surjective (fderiv ℝ (fun p : Parameters e => kernelTest e r f s c (p, q.2)) q.1) := by
  have hbase := hq.1
  have hJ : Surjective (fderiv ℝ
      (fun p : Parameters e => chartJet e r f s c (p, q.2.1, q.2.2.1)) q.1) :=
    surjective_fderiv_chart_spatial_parameter e r f hf s c q.1 q.2.1 q.2.2.1
      hbase.1.1.2 hbase.1.1.1 hbase.1.2 hbase.2
  have hs := (contDiffOn_chartJet e r f hf s c).contDiffAt
    ((chartDomain e r f hf s c).isOpen.mem_nhds hbase)
  have hparam : DifferentiableAt ℝ
      (fun p : Parameters e => chartJet e r f s c (p, q.2.1, q.2.2.1)) q.1 :=
    (hs.comp q.1 (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
  let L := ContinuousLinearMap.apply ℝ (Vector n) q.2.2.2
  have hL : Surjective L := ParametricRegular.operator_evaluation_surjective q.2.2.2 hq.2
  change Surjective (fderiv ℝ
    (L ∘ fun p : Parameters e => chartJet e r f s c (p, q.2.1, q.2.2.1)) q.1)
  rw [fderiv_comp q.1 L.differentiableAt hparam, L.fderiv]
  exact hL.comp hJ

theorem ae_no_chart_kernel
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hdim : 5 < n) (s : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 2 × Vector 2),
      (p, x) ∈ kernelDomain e r f hf s c → kernelTest e r f s c (p, x) ≠ 0 := by
  apply ParametricAvoidance.ae_avoid_zero_of_parameter μ (kernelTest e r f s c)
    (kernelDomain e r f hf s c) (contDiffOn_kernelTest e r f hf s c)
    (surjective_fderiv_kernelTest_parameter e r f hf s c)
  simpa only [GLOrthonormalization.Vector, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace_fin] using hdim

theorem ae_injective_chart_jets
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hdim : 5 < n) (s : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × Vector 2, (p, x) ∈ chartDomain e r f hf s c →
      Injective (chartJet e r f s c (p, x)) := by
  filter_upwards [ae_no_chart_kernel e r f μ hf hdim s c] with p hp
  intro x hx
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  by_contra hne
  exact hp (x.1, x.2, v) ⟨hx, hne⟩ hv

theorem ae_no_chart_double_points
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hdim : 5 < n) (s z : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 2 × Vector 2),
      (p, x) ∈ pairDomain e r f hf s z c → chartDifference e r f s z c (p, x) ≠ 0 := by
  apply ParametricAvoidance.ae_avoid_zero_of_parameter μ (chartDifference e r f s z c)
    (pairDomain e r f hf s z c) (contDiffOn_chartDifference e r f hf s z c)
    (surjective_fderiv_chartDifference_parameter e r f hf s z c)
  simpa only [GLOrthonormalization.Vector, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace_fin] using hdim

end Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation
