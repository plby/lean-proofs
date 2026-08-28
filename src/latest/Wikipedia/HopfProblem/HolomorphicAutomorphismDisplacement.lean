import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacementBasic
import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacementSup
import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacementHolomorphic

/-!
# Sup-normalization of genuine automorphism displacements

A nonidentity automorphism in the actual chart-valid neighborhood has positive
displacement norm. This norm is attained on one of the finitely many closed
outer coordinate balls. Dividing the literal coordinate differences by that
norm gives holomorphic functions bounded by one, with an actual unit-norm
witness. Every quantity is constructed from the original automorphism.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [LocallyCompactSpace M] (A : CompactAtlas E M)

/-- The actual sup norm is attained by an original-chart displacement. -/
theorem exists_norm_expression_sub_eq_delta {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (hne : f ≠ 1) :
    ∃ i : A.Index, ∃ z ∈ coordinateBall A i,
      ‖Coordinates.expression (A.chart i) f z - z‖ = delta A f := by
  obtain ⟨i, z, hz⟩ := exists_norm_apply_eq_norm (family A f) (family_ne_zero A hf hne)
  exact ⟨i, z, z.property, by simpa only [family_apply A hf, delta] using hz⟩

/-- The literal native coordinate displacement, divided by its actual finite sup norm. -/
def normalized (f : HolomorphicAutomorphism 𝓘(ℂ, E) M) (i : A.Index) (z : E) : E :=
  (delta A f : ℂ)⁻¹ • (Coordinates.expression (A.chart i) f z - z)

theorem normalized_eq_smul_family {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (i : A.Index) (z : coordinateBall A i) :
    normalized A f i z = (delta A f : ℂ)⁻¹ • family A f i z := by
  rw [family_apply A hf]
  rfl

omit [LocallyCompactSpace M] in
theorem normalized_norm_eq_div (f : HolomorphicAutomorphism 𝓘(ℂ, E) M)
    (i : A.Index) (z : E) :
    ‖normalized A f i z‖ = ‖Coordinates.expression (A.chart i) f z - z‖ / delta A f := by
  simp [normalized, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (delta_nonneg A f), div_eq_mul_inv, mul_comm]

@[simp] theorem normalized_one (i : A.Index) (z : E) :
    normalized A (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M) i z = 0 := by
  simp [normalized]

/-- The normalized coordinate functions have norm at most one throughout every closed
outer control ball. The assertion also holds at the identity, where normalization is zero. -/
theorem normalized_norm_le_one {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (i : A.Index) {z : E} (hz : z ∈ coordinateBall A i) :
    ‖normalized A f i z‖ ≤ 1 := by
  by_cases hne : f = 1
  · simp [hne]
  · rw [normalized_norm_eq_div]
    exact (div_le_one (delta_pos A hf hne)).mpr (norm_expression_sub_le_delta A hf i hz)

theorem normalized_norm_le_one_on_outer {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (i : A.Index) {z : E} (hz : z ∈ A.outerCoordinates i) :
    ‖normalized A f i z‖ ≤ 1 :=
  normalized_norm_le_one A hf i (outerCoordinates_subset_coordinateBall A i hz)

/-- A genuine unit-norm witness survives in the normalization of every nonidentity map. -/
theorem exists_normalized_norm_eq_one {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (hne : f ≠ 1) :
    ∃ i : A.Index, ∃ z ∈ coordinateBall A i, ‖normalized A f i z‖ = 1 := by
  obtain ⟨i, z, hz, he⟩ := exists_norm_expression_sub_eq_delta A hf hne
  refine ⟨i, z, hz, ?_⟩
  rw [normalized_norm_eq_div, he, div_self (ne_of_gt (delta_pos A hf hne))]

/-- Reconstructing a genuine coordinate difference from its normalization. -/
theorem expression_sub_eq_delta_smul_normalized {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (hne : f ≠ 1) (i : A.Index) (z : E) :
    Coordinates.expression (A.chart i) f z - z = (delta A f : ℂ) • normalized A f i z := by
  have hdelta : (delta A f : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (delta_pos A hf hne)
  simp only [normalized, smul_smul, mul_inv_cancel₀ hdelta, one_smul]

variable [IsManifold 𝓘(ℂ, E) ω M]

omit [LocallyCompactSpace M] in
/-- Holomorphy follows from the actual original charts and the native automorphism. -/
theorem normalized_holomorphic {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (i : A.Index) :
    ContDiffOn ℂ ω (normalized A f i) (A.outerCoordinates i : Set E) :=
  contDiffOn_const.smul ((expression_holomorphic A i f (hf i)).sub contDiffOn_id)

omit [LocallyCompactSpace M] in
theorem normalized_differentiableOn {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (i : A.Index) :
    DifferentiableOn ℂ (normalized A f i) (A.outerCoordinates i : Set E) :=
  (normalized_holomorphic A hf i).differentiableOn (by simp)

omit [LocallyCompactSpace M] in
theorem normalized_analyticAt {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (i : A.Index) {z : E} (hz : z ∈ A.outerCoordinates i) :
    AnalyticAt ℂ (normalized A f i) z :=
  analyticAt_const.smul ((expression_analyticAt A i f (hf i) hz).sub analyticAt_id)

end Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement
