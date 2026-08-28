import Wikipedia.NoExoticSixSphere.CompactTubularRetraction
import Wikipedia.NoExoticSixSphere.WeightedAffineJetSubmersion
import Wikipedia.NoExoticSixSphere.GLOrthonormalization

/-!
# Protected affine perturbations through a compact-image tubular retraction

The original target manifold and its atlas are retained. The source map only
needs to be smooth on a specified open region. The actual perturbation fixes
every protected point whose original value belongs to the retraction's base.
In a valid target chart, its spatial-jet parameter derivative is surjective
where the cutoff is nonzero. No compactness of the entire target is assumed.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)

abbrev Parameters (d : ℕ) (e : EuclideanEmbedding n M) :=
  AffinePerturbation.Parameters (Vector d) (Vector e.ambientDimension)

def ambient (p : Parameters d e) (x : Vector d) : Vector e.ambientDimension :=
  WeightedAffineComposite.ambient (e.toFun ∘ f) id χ p x

def map (p : Parameters d e) (x : Vector d) : M := r.toFun (ambient e f χ p x)

theorem map_eq_of_cutoff_zero (p : Parameters d e) (x : Vector d)
    (hx : f x ∈ r.base) (hχ : χ x = 0) : map e r f χ p x = f x := by
  simp only [map, ambient, WeightedAffineComposite.ambient, hχ, zero_smul, add_zero,
    comp_apply, r.fixes _ hx]

theorem map_zero (x : Vector d) (hx : f x ∈ r.base) : map e r f χ 0 x = f x := by
  simp only [map, ambient, WeightedAffineComposite.ambient, AffinePerturbation.value,
    Prod.fst_zero, Prod.snd_zero, zero_apply, add_zero, smul_zero,
    comp_apply, r.fixes _ hx]

theorem contDiffAt_ambient (p : Parameters d e) (x : Vector d)
    (hf : ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x) (hχ : ContDiffAt ℝ ∞ χ x) :
    ContDiffAt ℝ ∞ (uncurry (ambient e f χ)) (p, x) :=
  WeightedAffineComposite.contDiffAt_composite (e.toFun ∘ f) id id χ p x
    (e.smooth.contMDiffAt.comp x hf).contDiffAt contDiffAt_id hχ contDiffAt_id

theorem contMDiffAt_map (p : Parameters d e) (x : Vector d)
    (hf : ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x) (hχ : ContDiffAt ℝ ∞ χ x)
    (hp : ambient e f χ p x ∈ r.domain) :
    ContMDiffAt 𝓘(ℝ, Parameters d e × Vector d) (𝓡 n) ∞
      (uncurry (map e r f χ)) (p, x) :=
  (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)).comp (p, x)
    (contDiffAt_ambient e f χ p x hf hχ).contMDiffAt

variable (U : Opens (Vector d)) (hf : ContMDiffOn (𝓡 d) (𝓡 n) ∞ f U)
  (hχ : ContDiff ℝ ∞ χ)

def sourceDomain : Opens (Parameters d e × Vector d) :=
  ⟨Prod.snd ⁻¹' U, U.isOpen.preimage continuous_snd⟩

include hf hχ in
theorem contDiffOn_ambient : ContDiffOn ℝ ∞ (uncurry (ambient e f χ))
    (sourceDomain e U) := by
  intro q hq
  exact (contDiffAt_ambient e f χ q.1 q.2
    (hf.contMDiffAt (U.isOpen.mem_nhds hq)) hχ.contDiffAt).contDiffWithinAt

def tubularDomain : Opens (Parameters d e × Vector d) :=
  ⟨(sourceDomain e U : Set _) ∩ uncurry (ambient e f χ) ⁻¹' r.domain,
    (contDiffOn_ambient e f χ U hf hχ).continuousOn.isOpen_inter_preimage
      (sourceDomain e U).isOpen r.domain.isOpen⟩

theorem contMDiffOn_map :
    ContMDiffOn 𝓘(ℝ, Parameters d e × Vector d) (𝓡 n) ∞ (uncurry (map e r f χ))
      (tubularDomain e r f χ U hf hχ) :=
  r.smooth.comp ((contDiffOn_ambient e f χ U hf hχ).mono inter_subset_left).contMDiffOn
    (fun _ hq ↦ hq.2)

variable (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)

def chartDomain : Opens (Parameters d e × Vector d) :=
  ⟨(tubularDomain e r f χ U hf hχ : Set _) ∩ uncurry (map e r f χ) ⁻¹' c.source,
    (contMDiffOn_map e r f χ U hf hχ).continuousOn.isOpen_inter_preimage
      (tubularDomain e r f χ U hf hχ).isOpen c.open_source⟩

def chartCoordinates (q : Parameters d e × Vector d) : Vector n := c (map e r f χ q.1 q.2)

theorem contDiffOn_chartCoordinates : ContDiffOn ℝ ∞ (chartCoordinates e r f χ c)
    (chartDomain e r f χ U hf hχ c) :=
  (c.contMDiffOn_toFun.comp
    ((contMDiffOn_map e r f χ U hf hχ).mono inter_subset_left)
    (fun _ hq ↦ hq.2)).contDiffOn

def activeChartDomain : Opens (Parameters d e × Vector d) :=
  ⟨(chartDomain e r f χ U hf hχ c : Set _) ∩
      (fun q : Parameters d e × Vector d ↦ χ q.2) ⁻¹' {0}ᶜ,
    (chartDomain e r f χ U hf hχ c).isOpen.inter
      (isClosed_singleton.isOpen_compl.preimage (hχ.continuous.comp continuous_snd))⟩

include hf hχ in
theorem surjective_fderiv_chart_spatial_parameter (p : Parameters d e) (x : Vector d)
    (hx : x ∈ U) (hχx : χ x ≠ 0)
    (hp : ambient e f χ p x ∈ r.domain) (hc : map e r f χ p x ∈ c.source) :
    Surjective (fderiv ℝ (fun q : Parameters d e ↦
      fderiv ℝ (fun z ↦ c (map e r f χ q z)) x) p) := by
  let g : Vector d → Vector e.ambientDimension := e.toFun ∘ f
  let R : Vector e.ambientDimension → Vector n := c ∘ r.toFun
  let y := ambient e f χ p x
  have hg : ContDiffAt ℝ ∞ g x :=
    (e.smooth.contMDiffAt.comp x (hf.contMDiffAt (U.isOpen.mem_nhds hx))).contDiffAt
  have hrs : ContMDiffAt (𝓡 e.ambientDimension) (𝓡 n) ∞ r.toFun y :=
    r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)
  have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (r.toFun y) :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc)
  have hR : ContDiffAt ℝ ∞ R y := (hcs.comp y hrs).contDiffAt
  have hlocal : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (r.toFun y) :=
    ⟨c, hc, fun _ _ ↦ rfl⟩
  have hsurj := (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  change Surjective (mfderiv (𝓡 n) (𝓡 n) c (r.toFun y)) at hsurj
  have hRs : Surjective (fderiv ℝ R y) := by
    change Surjective (fderiv ℝ (c ∘ r.toFun) y)
    rw [← mfderiv_eq_fderiv, mfderiv_comp y (hcs.mdifferentiableAt (by simp))
      (hrs.mdifferentiableAt (by simp))]
    exact hsurj.comp (r.submersive y hp)
  have hi : Injective (fderiv ℝ (id : Vector d → Vector d) x) := by
    rw [fderiv_id]
    exact injective_id
  exact WeightedAffineComposite.surjective_fderiv_spatial_parameter
    g id R χ p x hχx hg contDiffAt_id hχ.contDiffAt hR hi hRs

end NoExoticSixSphere.CompactRetractionAffineFamily
