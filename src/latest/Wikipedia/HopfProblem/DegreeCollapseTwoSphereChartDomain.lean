import Wikipedia.HopfProblem.DegreeCollapseTwoSphereJetSubmersion

/-!
# Genuine coupled chart domains for the manifold perturbation

The domain records the source chart, interior time, tubular-retraction domain,
and target chart. Openness is proved in stages using continuity on the preceding
domain; no global continuity of chart inverses or of the total retraction is used.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation

open NoExoticSixSphere
open GLOrthonormalization EuclideanEmbedding

abbrev SourceChart := PartialDiffeomorph (𝓡 2) (𝓡 2) (Sphere 2) (Vector 2) ∞

abbrev TargetChart (n : ℕ) (M : Type*) [TopologicalSpace M] [ChartedSpace (Vector n) M] :=
  PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 2 → M)

def sourceDomain (s : SourceChart) : Opens (Parameters e × (ℝ × Vector 2)) :=
  ⟨{q | q.2.2 ∈ s.target ∧ q.2.1 ∈ Ioo (0 : ℝ) 1},
    (s.open_target.preimage (continuous_snd.comp continuous_snd)).inter
      (isOpen_Ioo.preimage (continuous_fst.comp continuous_snd))⟩

def chartAmbient (s : SourceChart) (q : Parameters e × (ℝ × Vector 2)) :
    Vector e.ambientDimension := ambient e f q.1 q.2.1 (s.symm q.2.2)

def chartMap (s : SourceChart) (q : Parameters e × (ℝ × Vector 2)) : M :=
  map e r f q.1 q.2.1 (s.symm q.2.2)

def chartCoordinates (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 2)) : Vector n := c (chartMap e r f s q)

theorem contDiffOn_chartAmbient
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f)) (s : SourceChart) :
    ContDiffOn ℝ ∞ (chartAmbient e f s) (sourceDomain e s) := by
  have hp : ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) 𝓘(ℝ, Parameters e) ∞
      (fun q : Parameters e × (ℝ × Vector 2) ↦ q.1) (sourceDomain e s) :=
    contDiff_fst.contMDiff.contMDiffOn
  have ht : ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) 𝓘(ℝ, ℝ) ∞
      (fun q : Parameters e × (ℝ × Vector 2) ↦ q.2.1) (sourceDomain e s) :=
    (contDiff_fst.comp contDiff_snd).contMDiff.contMDiffOn
  have hs : ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) (𝓡 2) ∞
      (fun q : Parameters e × (ℝ × Vector 2) ↦ s.symm q.2.2) (sourceDomain e s) :=
    s.contMDiffOn_invFun.comp
      (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn (fun _ hq ↦ hq.1)
  exact ((contMDiff_ambient e f hf).comp_contMDiffOn (hp.prodMk (ht.prodMk hs))).contDiffOn

def tubularDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f)) (s : SourceChart) :
    Opens (Parameters e × (ℝ × Vector 2)) :=
  ⟨(sourceDomain e s : Set (Parameters e × (ℝ × Vector 2))) ∩
      chartAmbient e f s ⁻¹' r.domain,
    (contDiffOn_chartAmbient e f hf s).continuousOn.isOpen_inter_preimage
      (sourceDomain e s).isOpen r.domain.isOpen⟩

theorem contMDiffOn_chartMap
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f)) (s : SourceChart) :
    ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × Vector 2)) (𝓡 n) ∞ (chartMap e r f s)
      (tubularDomain e r f hf s) :=
  r.smooth.comp ((contDiffOn_chartAmbient e f hf s).mono inter_subset_left).contMDiffOn
    (fun _ hq ↦ hq.2)

def chartDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart) (c : TargetChart n M) : Opens (Parameters e × (ℝ × Vector 2)) :=
  ⟨(tubularDomain e r f hf s : Set (Parameters e × (ℝ × Vector 2))) ∩
      chartMap e r f s ⁻¹' c.source,
    (contMDiffOn_chartMap e r f hf s).continuousOn.isOpen_inter_preimage
      (tubularDomain e r f hf s).isOpen c.open_source⟩

theorem contDiffOn_chartCoordinates
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartCoordinates e r f s c) (chartDomain e r f hf s c) :=
  (c.contMDiffOn_toFun.comp
    ((contMDiffOn_chartMap e r f hf s).mono inter_subset_left) (fun _ hq ↦ hq.2)).contDiffOn

end Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation
