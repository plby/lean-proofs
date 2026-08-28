import Wikipedia.NoExoticSixSphere.SkewAntipodalSpectrum

/-!
# Spectral coordinates on the complement of a rotation plane

The complement is an actual ambient submodule of codimension two. Restricting
the Gram operator preserves symmetry, so the real spectral theorem supplies
orthonormal eigenvectors inside the complement.
-/

namespace NoExoticSixSphere.SkewRotationComplement

open GLOrthonormalization CayleyTransform SkewSpectralPlane

variable {n : ℕ}

def plane (x y : Vector n) : Submodule ℝ (Vector n) := Submodule.span ℝ {x, y}

noncomputable def complement (x y : Vector n) : Submodule ℝ (Vector n) := (plane x y)ᗮ

theorem mem_complement (x y z : Vector n) :
    z ∈ complement x y ↔ inner ℝ x z = 0 ∧ inner ℝ y z = 0 := by
  rw [complement, Submodule.mem_orthogonal]
  constructor
  · intro h
    exact ⟨h x (Submodule.subset_span (by simp)), h y (Submodule.subset_span (by simp))⟩
  · rintro ⟨hx, hy⟩ z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hx, hy, mul_zero, add_zero]

theorem finrank_plane {x y : Vector n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) : Module.finrank ℝ (plane x y) = 2 := by
  have hON : Orthonormal ℝ (![x, y] : Fin 2 → Vector n) := by
    simp [orthonormal_vecCons_iff, hx, hy, hxy]
  have hrange : Set.range (![x, y] : Fin 2 → Vector n) = {x, y} := by
    ext z
    simp [or_comm]
  change Module.finrank ℝ (Submodule.span ℝ {x, y}) = 2
  rw [← hrange]
  simpa only [Fintype.card_fin] using! finrank_span_eq_card hON.linearIndependent

theorem finrank_complement {x y : Vector n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) : Module.finrank ℝ (complement x y) + 2 = n := by
  have h := (plane x y).finrank_add_finrank_orthogonal
  rw [finrank_plane hx hy hxy, finrank_euclideanSpace_fin] at h
  change 2 + Module.finrank ℝ (complement x y) = n at h
  omega

variable (K : SkewOperators n) {α : ℝ} {x y : Vector n}
  (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
  (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)

include hx hy

theorem map_mem_complement {z : Vector n} (hz : z ∈ complement x y) :
    (K : Vector n →L[ℝ] Vector n) z ∈ complement x y :=
  (mem_complement x y _).mpr
    (rotationPlane_complement_invariant K hx hy
      ((mem_complement x y z).mp hz).1 ((mem_complement x y z).mp hz).2)

theorem gram_mem_complement {z : Vector n} (hz : z ∈ complement x y) :
    gram K z ∈ complement x y := by
  have hh := (complement x y).neg_mem (map_mem_complement K hx hy (map_mem_complement K hx hy hz))
  simpa only [gram, adjoint_eq_neg, ContinuousLinearMap.comp_apply, neg_apply] using hh

noncomputable def restrictedGram : complement x y →L[ℝ] complement x y :=
  (gram K).restrict (fun _ hz ↦ gram_mem_complement K hx hy hz)

theorem restrictedGram_isSymmetric : (restrictedGram K hx hy).toLinearMap.IsSymmetric := by
  intro u v
  exact gram_isSymmetric K (u : Vector n) (v : Vector n)

noncomputable def basis :
    OrthonormalBasis (Fin (Module.finrank ℝ (complement x y))) ℝ (complement x y) :=
  (restrictedGram_isSymmetric K hx hy).eigenvectorBasis rfl

noncomputable def eigenvalue : Fin (Module.finrank ℝ (complement x y)) → ℝ :=
  (restrictedGram_isSymmetric K hx hy).eigenvalues rfl

theorem gram_basis (i : Fin (Module.finrank ℝ (complement x y))) :
    gram K (basis K hx hy i : Vector n) = eigenvalue K hx hy i •
      (basis K hx hy i : Vector n) :=
  congrArg Subtype.val ((restrictedGram_isSymmetric K hx hy).apply_eigenvectorBasis rfl i)

end NoExoticSixSphere.SkewRotationComplement
