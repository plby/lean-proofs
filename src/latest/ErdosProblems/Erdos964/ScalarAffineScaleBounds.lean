import ErdosProblems.Erdos964.PrimeSliceCutoff

/-!
# Power radii compatible with both distribution estimates

On intervals of size `t²`, choose `R = floor(t^β)` with `β < 1/2`.
The fixed affine modulus and every smaller-prime quotient fit the proved
distribution ranges after one threshold.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem scalar_modulusCutoff_sq_le (t : ℕ) (ht : 0 < t) (β : ℝ) :
    (modulusCutoff β t) ^ 2 ≤ modulusCutoff (2 * β) t := by
  apply Nat.le_floor
  rw [Nat.cast_pow]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  calc
    _ ≤ (Real.rpow (t : ℝ) β) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg htR.le β)) 2
    _ = _ := by
      have h : Real.rpow (t : ℝ) (β + β) =
          Real.rpow (t : ℝ) β * Real.rpow (t : ℝ) β := Real.rpow_add htR β β
      rw [two_mul, h, pow_two]

theorem scalar_modulusCutoff_le_self (t : ℕ) (ht : 1 ≤ t) (θ : ℝ) (hθ : θ ≤ 1) :
    modulusCutoff θ t ≤ t := by
  have h : (modulusCutoff θ t : ℝ) ≤ t :=
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg t) θ)).trans
      (Real.rpow_le_self_of_one_le (by exact_mod_cast ht) hθ)
  exact_mod_cast h

theorem scalar_radius_bounds (t K : ℕ) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    1 ≤ modulusCutoff β t ∧ modulusCutoff β t ≤ K * t := by
  constructor
  · apply Nat.le_floor
    rw [Nat.cast_one, Real.rpow_eq_pow]
    exact Real.one_le_rpow (by exact_mod_cast ht : (1 : ℝ) ≤ t) hβ
  · exact (scalar_modulusCutoff_le_self t ht β hβ1).trans (Nat.le_mul_of_pos_left t hK)

theorem scalar_radius_semiprime_cutoff (t L : ℕ) (ht : 1 ≤ t) (htL : t ≤ L)
    (β θ : ℝ) (hβ : 0 ≤ β) (hβθ : 2 * β ≤ θ) :
    (modulusCutoff β t) ^ 2 ≤ modulusCutoff θ L := by
  apply (scalar_modulusCutoff_sq_le t ht β).trans
  apply Nat.floor_mono
  exact (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast ht : (1 : ℝ) ≤ t) hβθ).trans
    (Real.rpow_le_rpow (Nat.cast_nonneg t) (by exact_mod_cast htL) (by linarith))

theorem scalar_radius_le_parameter_power (t : ℕ) (ht : 0 < t) (β : ℝ) :
    (modulusCutoff β t : ℝ) ≤ Real.rpow (t ^ 2 : ℕ) (β / 2) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpower : Real.rpow (t ^ 2 : ℕ) (β / 2) = Real.rpow (t : ℝ) β := by
    rw [Nat.cast_pow]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_two, ← Real.rpow_mul htR.le]
    congr 1
    ring
  rw [hpower]
  exact Nat.floor_le (Real.rpow_nonneg htR.le β)

theorem exists_scalar_radius_square_le_scale (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : β < 1 / 2) :
    ∃ t₀ : ℕ, 4 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t → m * (modulusCutoff β t) ^ 2 ≤ t := by
  let θ := (2 * β + 1) / 2
  have hgap : 2 * β < θ := by dsimp [θ]; linarith
  have hθ : θ ≤ 1 := by dsimp [θ]; linarith
  obtain ⟨t₀, ht₀, hmul⟩ := exists_mul_modulusCutoff_le m hm (2 * β) θ hgap
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht
  have htpos : 0 < t := by omega
  calc
    _ ≤ m * modulusCutoff (2 * β) t :=
      Nat.mul_le_mul_left m (scalar_modulusCutoff_sq_le t htpos β)
    _ ≤ modulusCutoff θ t := hmul t ht
    _ ≤ t := scalar_modulusCutoff_le_self t htpos θ hθ

theorem exists_scalar_radius_prime_cutoff (β θ : ℝ) (hβθ : β < θ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ t₀ : ℕ, 4 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      ∀ x : ℕ, t ^ 2 ≤ x → ∀ p : ℕ, 0 < p → p ≤ x →
        (modulusCutoff β t) ^ 2 / p ≤ modulusCutoff θ (x / p) := by
  obtain ⟨t₀, ht₀, hmul⟩ := exists_mul_modulusCutoff_le 2 (by decide)
    (2 * β) (2 * θ) (by linarith)
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht x htx p hp hpx
  have htpos : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have htwice : 2 * (modulusCutoff β t) ^ 2 ≤ modulusCutoff (2 * θ) t :=
    (Nat.mul_le_mul_left 2 (scalar_modulusCutoff_sq_le t htpos β)).trans (hmul t ht)
  have htwiceR : 2 * (modulusCutoff β t : ℝ) ^ 2 ≤ Real.rpow (t : ℝ) (2 * θ) := by
    have h : 2 * (modulusCutoff β t : ℝ) ^ 2 ≤ (modulusCutoff (2 * θ) t : ℝ) := by
      exact_mod_cast htwice
    exact h.trans (Nat.floor_le (Real.rpow_nonneg htR.le (2 * θ)))
  have hpower : Real.rpow (t : ℝ) (2 * θ) = Real.rpow ((t : ℝ) ^ 2) θ := by
    simp only [Real.rpow_eq_pow, Real.rpow_mul htR.le, Real.rpow_two]
  have hbase : (t : ℝ) ^ 2 ≤ x := by exact_mod_cast htx
  have hupper : Real.rpow (t : ℝ) (2 * θ) ≤ Real.rpow (x : ℝ) θ := by
    rw [hpower]
    exact Real.rpow_le_rpow (sq_nonneg _) hbase hθ
  have htwo : Real.rpow (2 : ℝ) θ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hθ1
  have hhalf : Real.rpow (x : ℝ) θ / 2 ≤ Real.rpow ((x : ℝ) / 2) θ := by
    have hdiv : Real.rpow ((x : ℝ) / 2) θ = Real.rpow (x : ℝ) θ / Real.rpow (2 : ℝ) θ := by
      simp only [Real.rpow_eq_pow, Real.div_rpow (Nat.cast_nonneg x) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hdiv]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg x) θ)
      (Real.rpow_pos_of_pos (by norm_num) θ) htwo
  apply div_le_modulusCutoff_div ((modulusCutoff β t) ^ 2) x p hp hpx θ hθ hθ1
  rw [Nat.cast_pow]
  exact (show (modulusCutoff β t : ℝ) ^ 2 ≤ Real.rpow (x : ℝ) θ / 2 by
    linarith [htwiceR.trans hupper]).trans hhalf

end Erdos964
