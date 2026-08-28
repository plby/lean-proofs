import Wikipedia.NoExoticSixSphere.OrthogonalPolygonStationarity
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonEnergy

/-!
# Stationary polygons are single exponential paths

Equality of adjacent body velocities makes the generators scalar multiples
of one skew operator. The actual ordered polygon realization is consequently
one exponential throughout its time interval, including the vertices.
-/

open Set
open scoped Manifold

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  OrthogonalPathEnergy

variable {n m : ℕ}

theorem edgeVelocity_eq_first_of_stationary (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) (i : Fin (m + 1)) :
    edgeVelocity a b τ v i = edgeVelocity a b τ v 0 := by
  induction i using Fin.inductionOn with
  | zero => rfl
  | succ j ih => exact (adjacent_edgeVelocity_eq_of_stationary a b τ v hv hstat j).symm.trans ih

theorem generator_eq_time_smul_of_stationary (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v) (i : Fin (m + 1)) :
    generator a b v i = (τ i.succ - τ i.castSucc) • edgeVelocity a b τ v 0 := by
  have hδ : τ i.succ - τ i.castSucc ≠ 0 :=
    sub_ne_zero.mpr (hτ (show i.castSucc < i.succ by simp)).ne'
  rw [← edgeVelocity_eq_first_of_stationary a b τ v hv hstat i, edgeVelocity, smul_smul]
  simp [hδ]

theorem vertices_eq_exponential_of_stationary (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v) (j : Fin (m + 2)) :
    vertices a b v j = a * exp ((τ j - τ 0) • edgeVelocity a b τ v 0) := by
  induction j using Fin.inductionOn with
  | zero => simp only [vertices_zero, sub_self, zero_smul, exp_zero, mul_one]
  | succ i ih =>
    rw [← generator_endpoint a b hv i, ih,
      generator_eq_time_smul_of_stationary a b τ hτ v hv hstat i,
      _root_.mul_assoc, ← exp_add_smul]
    congr 2
    congr 1
    ring

/-- The realized stationary broken path is smooth across all subdivision points. -/
theorem path_eq_exponential_of_stationary (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v)
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b τ v t = a * exp ((t - τ 0) • edgeVelocity a b τ v 0) := by
  obtain ⟨i, hi⟩ := IntervalPartition.exists_mem_adjacent τ ht
  have hδ : τ i.succ - τ i.castSucc ≠ 0 :=
    sub_ne_zero.mpr (hτ (show i.castSucc < i.succ by simp)).ne'
  rw [path_eq_segment a b τ hτ hv i hi, rescaledSegment,
    vertices_eq_exponential_of_stationary a b τ hτ v hv hstat i.castSucc,
    generator_eq_time_smul_of_stationary a b τ hτ v hv hstat i, smul_smul,
    div_mul_cancel₀ _ hδ, _root_.mul_assoc, ← exp_add_smul]
  congr 2
  congr 1
  ring

theorem stationary_is_exponential (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v) :
    ∃ K : SkewOperators n,
      a * exp ((τ (Fin.last (m + 1)) - τ 0) • K) = b ∧
      ∀ t ∈ Icc (τ 0) (τ (Fin.last (m + 1))), path a b τ v t = a * exp ((t - τ 0) • K) := by
  refine ⟨edgeVelocity a b τ v 0, ?_, fun _ ht ↦
    path_eq_exponential_of_stationary a b τ hτ v hv hstat ht⟩
  have h := vertices_eq_exponential_of_stationary a b τ hτ v hv hstat (Fin.last (m + 1))
  rw [vertices_last] at h
  exact h.symm

/-- Every critical point of the finite-dimensional smooth energy is a single exponential. -/
theorem critical_is_exponential (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    ∃ K : SkewOperators n,
      a * exp ((τ (Fin.last (m + 1)) - τ 0) • K) = b ∧
      ∀ t ∈ Icc (τ 0) (τ (Fin.last (m + 1))), path a b τ v t = a * exp ((t - τ 0) • K) :=
  stationary_is_exponential a b τ hτ v hv (isStationary_of_mfderiv_eq_zero a b τ v hv hcrit)

end NoExoticSixSphere.OrthogonalPolygon
