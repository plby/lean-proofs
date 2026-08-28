import Wikipedia.NoExoticSixSphere.SmoothTubularRetraction
import Wikipedia.NoExoticSixSphere.CutoffAffinePerturbation
import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Mathlib.Topology.MetricSpace.Thickening

/-!

# Endpoint-relative sphere families in the original manifold

In every source dimension, an affine perturbation of the actual ambient
representative is projected
through the constructed smooth tubular retraction. Compactness supplies one
positive parameter radius valid for every time and every sphere point.
The resulting family is jointly smooth on that parameter ball and fixes
both endpoint maps exactly. No jet or double-point genericity is asserted yet.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine

open NoExoticSixSphere GLOrthonormalization RelativeDoublePointPerturbation EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Vector n) M] (e : EuclideanEmbedding n M)

abbrev Parameters (d : ℕ) :=
  AffinePerturbation.Parameters (Vector (d + 1)) (Vector e.ambientDimension)

variable {d : ℕ}

def ambient (f : ℝ → Sphere d → M) (p : Parameters e d) (t : ℝ) (s : Sphere d) :
    Vector e.ambientDimension :=
  e.toFun (f t s) + cutoff t • AffinePerturbation.value p (s : Vector (d + 1))

def map (r : TubularRetraction e) (f : ℝ → Sphere d → M)
    (p : Parameters e d) (t : ℝ) (s : Sphere d) : M := r.toFun (ambient e f p t s)

theorem map_eq_outside (r : TubularRetraction e) (f : ℝ → Sphere d → M)
    (p : Parameters e d) {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (s : Sphere d) :
    map e r f p t s = f t s := by
  rw [map, ambient, cutoff_zero ht, zero_smul, add_zero, r.fixes]

theorem map_zero_parameter (r : TubularRetraction e) (f : ℝ → Sphere d → M)
    (t : ℝ) (s : Sphere d) : map e r f 0 t s = f t s := by
  simp only [map, ambient, AffinePerturbation.value, Prod.fst_zero, Prod.snd_zero,
    zero_apply, add_zero, smul_zero, r.fixes]

theorem contMDiff_ambient (f : ℝ → Sphere d → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f)) :
    ContMDiff (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d)))
      (𝓡 e.ambientDimension) ∞
      (fun q : Parameters e d × (ℝ × Sphere d) ↦ ambient e f q.1 q.2.1 q.2.2) := by
  let : Fact (Module.finrank ℝ (Vector (d + 1)) = d + 1) :=
    ⟨by simp [GLOrthonormalization.Vector]⟩
  have hbase : ContMDiff (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d)))
      (𝓡 e.ambientDimension) ∞
      (fun q : Parameters e d × (ℝ × Sphere d) ↦ e.toFun (f q.2.1 q.2.2)) :=
    e.smooth.comp (hf.comp contMDiff_snd)
  have ht : ContMDiff (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d))) 𝓘(ℝ, ℝ) ∞
      (fun q : Parameters e d × (ℝ × Sphere d) ↦ cutoff q.2.1) :=
    contDiff_cutoff.contMDiff.comp (contMDiff_fst.comp contMDiff_snd)
  have hs : ContMDiff (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d)))
      (𝓡 (d + 1)) ∞ (fun q : Parameters e d × (ℝ × Sphere d) ↦ (q.2.2 : Vector (d + 1))) :=
    (contMDiff_coe_sphere (E := Vector (d + 1)) (n := d) (m := ∞)).comp
      (contMDiff_snd.comp contMDiff_snd)
  have hval : ContMDiff (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d)))
      (𝓡 e.ambientDimension) ∞
      (fun q : Parameters e d × (ℝ × Sphere d) ↦
        AffinePerturbation.value q.1 (q.2.2 : Vector (d + 1))) := by
    have hA : ContMDiff (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d)))
        𝓘(ℝ, Vector (d + 1) →L[ℝ] Vector e.ambientDimension) ∞
        (fun q : Parameters e d × (ℝ × Sphere d) ↦ q.1.1) :=
      (contDiff_fst : ContDiff ℝ ∞ (fun p : Parameters e d ↦ p.1)).contMDiff.comp
        contMDiff_fst
    have hb : ContMDiff (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d)))
        (𝓡 e.ambientDimension) ∞ (fun q : Parameters e d × (ℝ × Sphere d) ↦ q.1.2) :=
      (contDiff_snd : ContDiff ℝ ∞ (fun p : Parameters e d ↦ p.2)).contMDiff.comp
        contMDiff_fst
    exact (hA.clm_apply hs).add hb
  exact hbase.add (ht.smul hval)

theorem exists_parameter_radius [CompactSpace M] (r : TubularRetraction e) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : Parameters e d, ‖p‖ < ε → ∀ x : M, ∀ t : ℝ, ∀ s : Sphere d,
      e.toFun x + cutoff t • AffinePerturbation.value p (s : Vector (d + 1)) ∈ r.domain := by
  have hcompact : IsCompact (range e.toFun) := isCompact_range e.closedEmbedding.continuous
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_thickening_subset_open r.domain.isOpen r.contains
  refine ⟨δ / 2, by positivity, ?_⟩
  intro p hp x t s
  apply hδU
  apply mem_thickening_iff.mpr
  refine ⟨e.toFun x, mem_range_self x, ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left]
  have hs : ‖(s : Vector (d + 1))‖ ≤ 1 := by
    exact le_of_eq (by simpa only [Metric.mem_sphere, dist_zero_right] using s.property)
  have hbound := AffinePerturbation.norm_weighted_value_le p t hs
  linarith

theorem exists_smooth_parameter_ball [CompactSpace M] (r : TubularRetraction e)
    (f : ℝ → Sphere d → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f)) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ p : Parameters e d, ‖p‖ < ε → ∀ t s, ambient e f p t s ∈ r.domain) ∧
      ContMDiffOn (𝓘(ℝ, Parameters e d).prod (𝓘(ℝ, ℝ).prod (𝓡 d))) (𝓡 n) ∞
        (fun q : Parameters e d × (ℝ × Sphere d) ↦ map e r f q.1 q.2.1 q.2.2)
        {q | ‖q.1‖ < ε} := by
  obtain ⟨ε, hε, hmem⟩ := exists_parameter_radius (d := d) e r
  have ha : ∀ p : Parameters e d, ‖p‖ < ε → ∀ t s, ambient e f p t s ∈ r.domain :=
    fun p hp t s ↦ hmem p hp (f t s) t s
  refine ⟨ε, hε, ha, ?_⟩
  exact r.smooth.comp (contMDiff_ambient e f hf).contMDiffOn
    (fun q hq ↦ ha q.1 hq q.2.1 q.2.2)

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine

