import Wikipedia.NoExoticSixSphere.Hemisphere
import Wikipedia.NoExoticSixSphere.Definitions
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth representatives of continuous sphere-valued maps

Approximate the ambient vector-valued map and normalize it. A uniform error
strictly less than one prevents the joining segments from passing through zero,
giving an actual homotopy on the sphere to the smooth representative.
-/

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section ContinuousSphere

open unitInterval

/-- Normalize a continuous nonzero vector family into the actual unit sphere. -/
noncomputable def normalizedSphereMap (g : C(X, E)) (hg : ∀ x, g x ≠ 0) : C(X, UnitSphere E) := by
  let gN : X → E := fun x ↦ NormedSpace.normalize (g x)
  have hm : ∀ x, gN x ∈ UnitSphere E := by
    intro x
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (hg x)
  have hc : Continuous gN :=
    (g.continuous.norm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hg x))).smul g.continuous
  exact ⟨fun x ↦ ⟨gN x, hm x⟩, hc.subtype_mk hm⟩

omit [InnerProductSpace ℝ E] in
/-- A vector within distance one of a unit vector cannot be zero. -/
theorem nearby_unit_ne_zero (a : UnitSphere E) (b : E) (h : dist b (a : E) < 1) : b ≠ 0 := by
  intro hb
  rw [hb, dist_zero_left, ClosedHemisphere.unit_norm] at h
  exact (lt_irrefl 1) h

/-- The joining segment remains within distance one of its initial unit vector. -/
theorem nearby_segment_dist_lt (a : UnitSphere E) (b : E) (h : dist b (a : E) < 1) (t : I) :
    dist ((a : E) + (t : ℝ) • (b - (a : E))) (a : E) < 1 := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖b - (a : E)‖ ≤ ‖b - (a : E)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ < 1 := by simpa only [dist_eq_norm] using h

/-- A segment from a unit vector to a point within distance one stays nonzero. -/
theorem nearby_segment_ne_zero (a : UnitSphere E) (b : E) (h : dist b (a : E) < 1) (t : I) :
    (a : E) + (t : ℝ) • (b - (a : E)) ≠ 0 :=
  nearby_unit_ne_zero a _ (nearby_segment_dist_lt a b h t)

/-- A vector within distance one of a unit vector cannot be its antipode. -/
theorem nearby_sum_ne_zero (a : UnitSphere E) (b : E) (h : dist b (a : E) < 1) :
    (a : E) + b ≠ 0 := by
  intro hsum
  have hb : b = -(a : E) := by
    apply add_left_cancel (a := (a : E))
    simpa only [add_neg_cancel] using hsum
  have hd : dist b (a : E) = 2 := by
    rw [hb, dist_eq_norm]
    have hv : -(a : E) - (a : E) = -((2 : ℝ) • (a : E)) := by
      rw [two_smul]
      abel
    rw [hv, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos zero_lt_two,
      ClosedHemisphere.unit_norm, mul_one]
  rw [hd] at h
  norm_num at h

/-- Nearby ambient approximation gives a genuine sphere homotopy after normalization. -/
noncomputable def nearbyNormalizationHomotopy (f : C(X, UnitSphere E)) (g : C(X, E))
    (h : ∀ x, dist (g x) (f x : E) < 1) :
    f.Homotopy (normalizedSphereMap g (fun x ↦ nearby_unit_ne_zero (f x) (g x) (h x))) where
  toFun p := ⟨NormedSpace.normalize ((f p.2 : E) + (p.1 : ℝ) • (g p.2 - (f p.2 : E))), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1)⟩
  continuous_toFun := by
    have hf : Continuous (fun p : I × X ↦ (f p.2 : E)) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hg := g.continuous.comp (continuous_snd : Continuous (Prod.snd : I × X → X))
    have ht : Continuous (fun p : I × X ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hb := hf.add (ht.smul (hg.sub hf))
    exact ((hb.norm.inv₀ (fun p ↦ norm_ne_zero_iff.mpr
      (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1))).smul hb).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change NormedSpace.normalize ((f x : E) + (0 : ℝ) • (g x - (f x : E))) = (f x : E)
    simpa only [zero_smul, add_zero] using
      NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (f x))
  map_one_left x := by
    apply Subtype.ext
    change NormedSpace.normalize ((f x : E) + (1 : ℝ) • (g x - (f x : E))) =
      NormedSpace.normalize (g x)
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]

end ContinuousSphere

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Ambient normalization is smooth along any smooth nonzero vector-valued family. -/
theorem contMDiff_normalize {g : M → E} (hg : ContMDiff I 𝓘(ℝ, E) ∞ g)
    (hn : ∀ x, g x ≠ 0) : ContMDiff I 𝓘(ℝ, E) ∞ (fun x ↦ NormedSpace.normalize (g x)) := by
  intro x
  have hN : ContDiffAt ℝ ∞ (NormedSpace.normalize : E → E) (g x) :=
    ((contDiffAt_norm ℝ (hn x)).inv (norm_ne_zero_iff.mpr (hn x))).smul contDiffAt_id
  exact hN.comp_contMDiffAt (f := g) (x := x) (hg x)

/-- Every continuous sphere-valued map on a sigma-compact smooth manifold has a homotopic smooth
representative, without assuming smoothness of the initial map. -/
theorem exists_smoothSphereRepresentative [FiniteDimensional ℝ B] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] (n : ℕ) (f : C(M, Sphere n)) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ f.Homotopic g := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hf : Continuous (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val.comp f.continuous
  obtain ⟨g, hg, _⟩ := hf.exists_contMDiff_approx I (⊤ : ℕ∞)
    (ε := fun _ ↦ 1) continuous_const (fun _ ↦ zero_lt_one)
  let gC : C(M, EuclideanSpace ℝ (Fin (n + 1))) := ⟨g, g.contMDiff.continuous⟩
  have hn : ∀ x, gC x ≠ 0 := fun x ↦ nearby_unit_ne_zero (f x) (gC x) (hg x)
  refine ⟨normalizedSphereMap gC hn, ?_, ⟨nearbyNormalizationHomotopy f gC hg⟩⟩
  exact (contMDiff_normalize g.contMDiff hn).codRestrict_sphere (n := n)
    (fun x ↦ (normalizedSphereMap gC hn x).2)

end NoExoticSixSphere
