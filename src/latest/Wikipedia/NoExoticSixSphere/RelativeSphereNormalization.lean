import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Relative smooth approximation of sphere-valued maps

Normalize a close smooth ambient approximation while retaining exact values
on a protected closed set. The same set is fixed throughout the normalization
homotopy, and an explicit error bound controls the normalized approximation.
-/

open scoped Manifold ContDiff Topology
open Set

namespace NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dist_normalize_unit_le (a : UnitSphere E) {b : E} (hb : b ≠ 0) :
    dist (NormedSpace.normalize b) (a : E) ≤ 2 * dist b (a : E) := by
  have hsplit : NormedSpace.normalize b - b =
      (1 - ‖b‖) • NormedSpace.normalize b := by
    rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
  have hnorm : dist (NormedSpace.normalize b) b ≤ dist b (a : E) := by
    rw [dist_eq_norm, hsplit, norm_smul, NormedSpace.norm_normalize hb,
      mul_one, Real.norm_eq_abs, abs_sub_comm]
    simpa only [ClosedHemisphere.unit_norm, dist_eq_norm] using abs_norm_sub_norm_le b (a : E)
  calc
    dist (NormedSpace.normalize b) (a : E) ≤
        dist (NormedSpace.normalize b) b + dist b (a : E) := dist_triangle _ _ _
    _ ≤ 2 * dist b (a : E) := by linarith

variable {X : Type*} [TopologicalSpace X]

noncomputable def nearbyNormalizationHomotopyRel (f : C(X, UnitSphere E)) (g : C(X, E))
    (h : ∀ x, dist (g x) (f x : E) < 1) (S : Set X)
    (heq : EqOn g (fun x ↦ (f x : E)) S) :
    f.HomotopyRel (normalizedSphereMap g (fun x ↦ nearby_unit_ne_zero (f x) (g x) (h x))) S where
  toHomotopy := nearbyNormalizationHomotopy f g h
  prop' := by
    intro t x hx
    apply Subtype.ext
    change NormedSpace.normalize ((f x : E) + (t : ℝ) • (g x - (f x : E))) = (f x : E)
    rw [heq hx, sub_self, smul_zero, add_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (f x))

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem exists_smoothSphereApproximation_rel (n : ℕ) (f : C(M, Sphere n))
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContMDiffOn I (𝓡 n) ∞ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ f.HomotopicRel g S ∧
      ∀ x, dist (g x) (f x) < ε := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let δ : ℝ := min (1 / 2) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hf : Continuous (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val.comp f.continuous
  have hfs : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) U :=
    contMDiff_coe_sphere.comp_contMDiffOn hfU
  obtain ⟨g, hg, heq, _⟩ := hf.exists_contMDiff_approx_and_eqOn I (⊤ : ℕ∞)
    continuous_const (fun _ ↦ hδ) hS hU hfs
  let gC : C(M, EuclideanSpace ℝ (Fin (n + 1))) := ⟨g, g.contMDiff.continuous⟩
  have hclose (x : M) : dist (gC x) (f x : EuclideanSpace ℝ (Fin (n + 1))) < 1 :=
    lt_of_lt_of_le (hg x) (le_trans (min_le_left _ _) (by norm_num))
  have hn : ∀ x, gC x ≠ 0 := fun x ↦ nearby_unit_ne_zero (f x) (gC x) (hclose x)
  refine ⟨normalizedSphereMap gC hn, ?_, ⟨nearbyNormalizationHomotopyRel f gC hclose S heq⟩, ?_⟩
  · exact (contMDiff_normalize g.contMDiff hn).codRestrict_sphere (n := n)
      (fun x ↦ (normalizedSphereMap gC hn x).2)
  · intro x
    have hdist := dist_normalize_unit_le (f x) (hn x)
    have hsmall : dist (gC x) (f x : EuclideanSpace ℝ (Fin (n + 1))) < ε / 4 :=
      lt_of_lt_of_le (hg x) (min_le_right _ _)
    change dist (NormedSpace.normalize (gC x)) (f x : EuclideanSpace ℝ (Fin (n + 1))) < ε
    linarith

end NoExoticSixSphere
