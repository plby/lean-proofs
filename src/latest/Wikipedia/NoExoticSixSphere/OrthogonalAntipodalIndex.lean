import Wikipedia.NoExoticSixSphere.SkewPlaneMixingFamily
import Wikipedia.NoExoticSixSphere.OrthogonalIndexEstimate
import Wikipedia.NoExoticSixSphere.OrthogonalIndexFieldLinear

/-!
# Negative directions at antipodal exponential paths

Outside the locus `K†K = π² I`, an actual antipodal generator has a linear
family of `n - 2` independent skew operators, every nonzero combination of
which gives a negative second energy derivative via the rotating sine field.

This is a pointwise negative-subspace estimate. It does not assert a global
Morse deformation, a path-space homotopy comparison, or Bott periodicity.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalAntipodalIndex

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalCommutator
  OrthogonalExponential SkewSpectralPlane SkewAntipodalSpectrum SkewRotationComplement
  SkewPlaneMixing OrthogonalIndexTestField

variable {n : ℕ}

theorem commutator_bound_mixingMap (K : SkewOperators n) {α : ℝ} {x y : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
    (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)
    (D : RotationData K hx hy) (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (hα : 3 * Real.pi ≤ α)
    (c : Fin (Module.finrank ℝ (complement x y)) → ℝ) :
    16 * Real.pi ^ 2 * squareNorm (mixingMap K hx hy D c : Vector n →L[ℝ] Vector n) ≤
      squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
        (mixingMap K hx hy D c : Vector n →L[ℝ] Vector n)) := by
  have hterm (i : Fin (Module.finrank ℝ (complement x y))) :
      16 * Real.pi ^ 2 * c i ^ 2 ≤ (c i * (α + D.speed i)) ^ 2 := by
    have hs : 4 * Real.pi ≤ α + D.speed i := by linarith [D.speed_ge_pi i]
    have hsq : (4 * Real.pi) ^ 2 ≤ (α + D.speed i) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith [Real.pi_pos])).mpr hs
    calc
      _ = (4 * Real.pi) ^ 2 * c i ^ 2 := by ring
      _ ≤ (α + D.speed i) ^ 2 * c i ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)
  rw [← Finset.mul_sum] at hsum
  rw [squareNorm_mixingMap K hx hy D hnx hny hxy,
    squareNorm_commutator_mixingMap K hx hy D hnx hny hxy]
  linarith

/-- A nonminimal antipodal generator has a codimension-two linear family
with a uniform, strict commutator bound on every nonzero member. -/
theorem exists_negativeFamily (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hnot : gram K ≠ Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)) :
    ∃ (m : ℕ) (T : (Fin m → ℝ) →ₗ[ℝ] SkewOperators n),
      m + 2 = n ∧ Function.Injective T ∧ ∀ c, c ≠ 0 →
        4 * Real.pi ^ 2 * squareNorm (T c : Vector n →L[ℝ] Vector n) <
          squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
            (T c : Vector n →L[ℝ] Vector n)) := by
  obtain ⟨α, x, y, hα, hnx, hny, hxy, hx, hy⟩ := exists_fast_rotationPlane K hexp hnot
  obtain ⟨D⟩ := exists_rotationData K hx hy hexp
  let T := mixingMap K hx hy D
  have hT : Function.Injective T := mixingMap_injective K hx hy D hnx hny hxy
  refine ⟨Module.finrank ℝ (complement x y), T, finrank_complement hnx hny hxy, hT, ?_⟩
  intro c hc
  have hne : T c ≠ 0 := fun h ↦ hc (hT (h.trans T.map_zero.symm))
  have hpos : 0 < squareNorm (T c : Vector n →L[ℝ] Vector n) := by
    apply lt_of_le_of_ne (squareNorm_nonneg _)
    intro h
    exact hne (Subtype.ext ((squareNorm_eq_zero_iff _).mp h.symm))
  have hb := commutator_bound_mixingMap K hx hy D hnx hny hxy hα c
  have hp := mul_pos (sq_pos_of_pos Real.pi_pos) hpos
  change 16 * Real.pi ^ 2 * squareNorm (T c : Vector n →L[ℝ] Vector n) ≤ _ at hb
  linarith

/-- The negative family is realized by actual fixed-endpoint exponential
variations, with a negative second energy derivative for every nonzero parameter. -/
theorem exists_negative_energy_family (b : OrthogonalOperators n) (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hnot : gram K ≠ Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)) :
    ∃ (m : ℕ) (T : (Fin m → ℝ) →ₗ[ℝ] SkewOperators n),
      m + 2 = n ∧ Function.Injective T ∧ ∀ c, c ≠ 0 →
        deriv (deriv (fun s ↦ OrthogonalPathEnergy.energy
          (fun t ↦ (OrthogonalExponentialVariation.family
            (fun r ↦ b * exp (r • K)) (field K (T c)) (s, t)).1.1) 0 1)) 0 < 0 := by
  obtain ⟨m, T, hm, hT, hneg⟩ := exists_negativeFamily K hexp hnot
  exact ⟨m, T, hm, hT, fun c hc ↦ negative_secondDerivative b K (T c) (hneg c hc)⟩

/-- The estimate holds on a genuine linear space of independent smooth,
endpoint-zero variation fields, not just on independent operator labels. -/
theorem exists_negative_fieldFamily (b : OrthogonalOperators n) (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hnot : gram K ≠ Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)) :
    ∃ (m : ℕ) (F : (Fin m → ℝ) →ₗ[ℝ] (ℝ → SkewOperators n)),
      m + 2 = n ∧ Function.Injective F ∧ ∀ c,
        ContDiff ℝ ∞ (F c) ∧ F c 0 = 0 ∧ F c 1 = 0 ∧ (c ≠ 0 →
          deriv (deriv (fun s ↦ OrthogonalPathEnergy.energy
            (fun t ↦ (OrthogonalExponentialVariation.family
              (fun r ↦ b * exp (r • K)) (F c) (s, t)).1.1) 0 1)) 0 < 0) := by
  obtain ⟨m, T, hm, hT, hneg⟩ := exists_negativeFamily K hexp hnot
  let F := (fieldLinear K).comp T
  refine ⟨m, F, hm, (fieldLinear_injective K).comp hT, ?_⟩
  intro c
  exact ⟨contDiff_field K (T c), field_zero K (T c), field_one K (T c),
    fun hc ↦ negative_secondDerivative b K (T c) (hneg c hc)⟩

end NoExoticSixSphere.OrthogonalAntipodalIndex
