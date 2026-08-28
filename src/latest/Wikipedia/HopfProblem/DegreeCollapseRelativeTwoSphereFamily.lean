import Wikipedia.HopfProblem.DegreeCollapseTwoSphereAffineFamily
import Wikipedia.NoExoticSixSphere.AffineParameterEvaluation

/-!
# Actual affine sphere perturbations with a protected spatial region

Multiplying the affine parameter by a smooth source cutoff preserves its
zero set exactly. A bounded cutoff retains the same genuine tubular-radius
control. Joint smoothness and parameter scaling give actual homotopies
relative to the protected set. Relative genericity is a further obligation.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere

open GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

def ambient (p : Parameters e) (t : ℝ) (s : Sphere 2) : Vector e.ambientDimension :=
  TwoSpherePerturbation.ambient e f (χ s • p) t s

def map (p : Parameters e) (t : ℝ) (s : Sphere 2) : M := r.toFun (ambient e f χ p t s)

theorem ambient_apply (p : Parameters e) (t : ℝ) (s : Sphere 2) :
    ambient e f χ p t s = e.toFun (f t s) +
      (RelativeDoublePointPerturbation.cutoff t * χ s) •
        AffinePerturbation.value p (s : Vector 3) := by
  have he : AffinePerturbation.value (χ s • p) (s : Vector 3) =
      χ s • AffinePerturbation.value p (s : Vector 3) :=
    (AffinePerturbation.evaluation (F := Vector e.ambientDimension) (s : Vector 3)).map_smul
      (χ s) p
  unfold ambient TwoSpherePerturbation.ambient
  rw [he, smul_smul]

theorem map_eq_zero_cutoff (p : Parameters e) (t : ℝ) (s : Sphere 2) (hs : χ s = 0) :
    map e r f χ p t s = f t s := by
  change TwoSpherePerturbation.map e r f (χ s • p) t s = _
  rw [hs, zero_smul, TwoSpherePerturbation.map_zero_parameter]

theorem map_zero_parameter (t : ℝ) (s : Sphere 2) : map e r f χ 0 t s = f t s := by
  change TwoSpherePerturbation.map e r f (χ s • 0) t s = _
  rw [smul_zero, TwoSpherePerturbation.map_zero_parameter]

theorem map_eq_outside (p : Parameters e) {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (s : Sphere 2) :
    map e r f χ p t s = f t s :=
  TwoSpherePerturbation.map_eq_outside e r f (χ s • p) ht s

theorem contMDiff_ambient
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) :
    ContMDiff (𝓘(ℝ, Parameters e).prod (𝓘(ℝ, ℝ).prod (𝓡 2)))
      (𝓡 e.ambientDimension) ∞
      (fun q : Parameters e × (ℝ × Sphere 2) ↦ ambient e f χ q.1 q.2.1 q.2.2) := by
  have hs : ContMDiff (𝓘(ℝ, Parameters e).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) 𝓘(ℝ, ℝ) ∞
      (fun q : Parameters e × (ℝ × Sphere 2) ↦ χ q.2.2) :=
    hχ.comp (contMDiff_snd.comp contMDiff_snd)
  exact (TwoSpherePerturbation.contMDiff_ambient e f hf).comp
    ((hs.smul contMDiff_fst).prodMk contMDiff_snd)

theorem exists_smooth_parameter_ball [CompactSpace M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (hbound : ∀ s, ‖χ s‖ ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ p : Parameters e, ‖p‖ < ε → ∀ t s, ambient e f χ p t s ∈ r.domain) ∧
      ContMDiffOn (𝓘(ℝ, Parameters e).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓡 n) ∞
        (fun q : Parameters e × (ℝ × Sphere 2) ↦ map e r f χ q.1 q.2.1 q.2.2)
        {q | ‖q.1‖ < ε} := by
  obtain ⟨ε, hε, hmem⟩ := TwoSpherePerturbation.exists_parameter_radius e r
  have ha : ∀ p : Parameters e, ‖p‖ < ε → ∀ t s, ambient e f χ p t s ∈ r.domain := by
    intro p hp t s
    apply hmem (χ s • p) _ (f t s) t s
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg p) (hbound s)).trans_lt hp
  refine ⟨ε, hε, ha, ?_⟩
  exact r.smooth.comp (contMDiff_ambient e f χ hf hχ).contMDiffOn
    (fun q hq ↦ ha q.1 hq q.2.1 q.2.2)

def slice (p : Parameters e) (t : ℝ)
    (hp : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry (map e r f χ p))) :
    C(Sphere 2, M) :=
  ⟨map e r f χ p t, (hp.comp (contMDiff_const.prodMk contMDiff_id)).continuous⟩

def parameterHomotopy (ε : ℝ)
    (hsmooth : ContMDiffOn (𝓘(ℝ, Parameters e).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓡 n) ∞
      (fun q : Parameters e × (ℝ × Sphere 2) ↦ map e r f χ q.1 q.2.1 q.2.2)
      {q | ‖q.1‖ < ε})
    (p : Parameters e) (hp : ‖p‖ < ε) (t : ℝ)
    (ht : Continuous (f t)) :
    (⟨f t, ht⟩ : C(Sphere 2, M)).HomotopyRel
      (slice e r f χ p t
        (hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hp)))
      {s | χ s = 0} where
  toFun q := map e r f χ ((q.1 : ℝ) • p) t q.2
  continuous_toFun := by
    have hsmall (u : unitInterval) : ‖(u : ℝ) • p‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg u.property.1]
      exact (mul_le_of_le_one_left (norm_nonneg p) u.property.2).trans_lt hp
    exact hsmooth.continuousOn.comp_continuous
      (((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk
        (continuous_const.prodMk continuous_snd)) (fun q ↦ hsmall q.1)
  map_zero_left s := by
    change map e r f χ ((0 : ℝ) • p) t s = f t s
    rw [zero_smul, map_zero_parameter]
  map_one_left s := by
    change map e r f χ ((1 : ℝ) • p) t s = map e r f χ p t s
    rw [one_smul]
  prop' u s hs := map_eq_zero_cutoff e r f χ ((u : ℝ) • p) t s hs

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
