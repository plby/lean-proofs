import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereJetSubmersion
import Wikipedia.HopfProblem.DegreeCollapseTwoSphereChartDomain

/-!
# Coupled chart domains away from the protected source region

The open domain retains the actual source chart, nonzero spatial cutoff,
interior time, tubular domain, and target chart. Smoothness and openness use
only the valid domains of the chart inverses and tubular retraction.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere

open GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

theorem contMDiffOn_chartCutoff (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) :
    ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) 𝓘(ℝ, ℝ) ∞
      (fun q : Parameters e × (ℝ × Vector 2) ↦ χ (s.symm q.2.2))
      (TwoSpherePerturbation.sourceDomain e s) :=
  hχ.comp_contMDiffOn (s.contMDiffOn_invFun.comp
    (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn (fun _ hq ↦ hq.1))

def chartAmbient (s : SourceChart) (q : Parameters e × (ℝ × Vector 2)) :
    Vector e.ambientDimension := ambient e f χ q.1 q.2.1 (s.symm q.2.2)

def chartMap (s : SourceChart) (q : Parameters e × (ℝ × Vector 2)) : M :=
  map e r f χ q.1 q.2.1 (s.symm q.2.2)

def chartCoordinates (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 2)) : Vector n := c (chartMap e r f χ s q)

theorem contDiffOn_chartAmbient
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (s : SourceChart) :
    ContDiffOn ℝ ∞ (chartAmbient e f χ s)
      (TwoSpherePerturbation.sourceDomain e s) := by
  have hp : ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) 𝓘(ℝ, Parameters e) ∞
      (fun q : Parameters e × (ℝ × Vector 2) ↦ q.1)
      (TwoSpherePerturbation.sourceDomain e s) :=
    contDiff_fst.contMDiff.contMDiffOn
  have ht : ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) 𝓘(ℝ, ℝ) ∞
      (fun q : Parameters e × (ℝ × Vector 2) ↦ q.2.1)
      (TwoSpherePerturbation.sourceDomain e s) :=
    (contDiff_fst.comp contDiff_snd).contMDiff.contMDiffOn
  have hs : ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) (𝓡 2) ∞
      (fun q : Parameters e × (ℝ × Vector 2) ↦ s.symm q.2.2)
      (TwoSpherePerturbation.sourceDomain e s) :=
    s.contMDiffOn_invFun.comp
      (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn (fun _ hq ↦ hq.1)
  exact ((contMDiff_ambient e f χ hf hχ).comp_contMDiffOn
    (hp.prodMk (ht.prodMk hs))).contDiffOn

def tubularDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (s : SourceChart) :
    Opens (Parameters e × (ℝ × Vector 2)) :=
  ⟨(TwoSpherePerturbation.sourceDomain e s : Set (Parameters e × (ℝ × Vector 2))) ∩
      chartAmbient e f χ s ⁻¹' r.domain,
    (contDiffOn_chartAmbient e f χ hf hχ s).continuousOn.isOpen_inter_preimage
      (TwoSpherePerturbation.sourceDomain e s).isOpen r.domain.isOpen⟩

theorem contMDiffOn_chartMap
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (s : SourceChart) :
    ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) (𝓡 n) ∞ (chartMap e r f χ s)
      (tubularDomain e r f χ hf hχ s) :=
  r.smooth.comp ((contDiffOn_chartAmbient e f χ hf hχ s).mono inter_subset_left).contMDiffOn
    (fun _ hq ↦ hq.2)

def chartDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) : Opens (Parameters e × (ℝ × Vector 2)) :=
  ⟨(tubularDomain e r f χ hf hχ s : Set (Parameters e × (ℝ × Vector 2))) ∩
      chartMap e r f χ s ⁻¹' c.source,
    (contMDiffOn_chartMap e r f χ hf hχ s).continuousOn.isOpen_inter_preimage
      (tubularDomain e r f χ hf hχ s).isOpen c.open_source⟩

theorem contDiffOn_chartCoordinates
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartCoordinates e r f χ s c) (chartDomain e r f χ hf hχ s c) :=
  (c.contMDiffOn_toFun.comp
    ((contMDiffOn_chartMap e r f χ hf hχ s).mono inter_subset_left)
    (fun _ hq ↦ hq.2)).contDiffOn

def activeChartDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : SourceChart) (c : TargetChart n M) : Opens (Parameters e × (ℝ × Vector 2)) :=
  ⟨(chartDomain e r f χ hf hχ s c : Set _) ∩
      (fun q : Parameters e × (ℝ × Vector 2) ↦ χ (s.symm q.2.2)) ⁻¹' {0}ᶜ,
    by
      have hcut : ContinuousOn
          (fun q : Parameters e × (ℝ × Vector 2) ↦ χ (s.symm q.2.2))
          (chartDomain e r f χ hf hχ s c) :=
        (contMDiffOn_chartCutoff e χ hχ s).continuousOn.mono (fun _ hq ↦ hq.1.1)
      exact hcut.isOpen_inter_preimage (chartDomain e r f χ hf hχ s c).isOpen
        isClosed_singleton.isOpen_compl⟩

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
