import ErdosProblems.Erdos587.HooleyWideFullSeries

/-! # Positive and negative centered frequencies in the power-separated branch -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_wide_full_signed_mean (f g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a q H : ℕ, 0 < q → 0 < H → H ≤ q → q.Coprime a →
        (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) →
        (q : ℝ) * (max 1 (Real.log (Real.log T))) ^ 7 ≤ H * T ^ (1 / 4 : ℝ) →
        let σ := ((q : ℝ) / H)⁻¹
        let M := ⌊T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ 6⌋₊
        Summable (fun m : ℤ => if m = 0 then 0 else
          ‖((σ : ℂ) * g (σ * m)) * deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * m)‖) ∧
        (∑' m : ℤ, if m = 0 then 0 else
          ‖((σ : ℂ) * g (σ * m)) * deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * m)‖) ≤
          C * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4 := by
  obtain ⟨C₁, hC₁, hpos⟩ := exists_delta_wide_full_positive_mean f g
  obtain ⟨C₂, hC₂, hneg⟩ := exists_delta_wide_full_positive_mean
    (conjugateSchwartz f) (reflectedSchwartz g)
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  filter_upwards [hpos, hneg] with T hp hn
  intro a q H hq hH hHq hcop hqhi hbudget
  have hp' := hp a q H hq hH hHq hcop hqhi hbudget
  have hn' := hn a q H hq hH hHq hcop hqhi hbudget
  let σ := ((q : ℝ) / H)⁻¹
  let M := ⌊T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ 6⌋₊
  let S : ℤ → ℝ := fun m => if m = 0 then 0 else
    ‖((σ : ℂ) * g (σ * m)) * deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * m)‖
  have hzero : S 0 = 0 := by simp [S]
  have hpos_id (n : ℕ) : S ((n + 1 : ℕ) : ℤ) =
      ‖((σ : ℂ) * g (σ * ((n : ℝ) + 1))) *
        deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * (n + 1))‖ := by
    dsimp only [S]
    rw [if_neg (by exact_mod_cast Nat.succ_ne_zero n)]
    simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one]
  have hneg_id (n : ℕ) : S (-((n + 1 : ℕ) : ℤ)) =
      ‖((σ : ℂ) * reflectedSchwartz g (σ * ((n : ℝ) + 1))) *
        deltaSmoothCenteredQuadratic (conjugateSchwartz f) (Real.sqrt T) q (a * (n + 1))‖ := by
    dsimp only [S]
    rw [if_neg (neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n))]
    simp only [norm_mul, mul_neg, deltaSmoothCenteredQuadratic_norm_negative f (Real.sqrt T) hq,
      reflectedSchwartz_apply, Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      Int.cast_add, Int.cast_one]
  have hpsum : Summable (fun n : ℕ => S ((n + 1 : ℕ) : ℤ)) :=
    hp'.1.congr (fun n => (hpos_id n).symm)
  have hnsum : Summable (fun n : ℕ => S (-((n + 1 : ℕ) : ℤ))) :=
    hn'.1.congr (fun n => (hneg_id n).symm)
  obtain ⟨hSsum, hSsplit⟩ := summable_int_of_positive_negative hzero hpsum hnsum
  have hpbound : (∑' n : ℕ, S ((n + 1 : ℕ) : ℤ)) ≤
      C₁ * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4 := by
    simp_rw [hpos_id]
    exact hp'.2
  have hnbound : (∑' n : ℕ, S (-((n + 1 : ℕ) : ℤ))) ≤
      C₂ * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4 := by
    simp_rw [hneg_id]
    exact hn'.2
  change Summable S ∧ (∑' m, S m) ≤
    (C₁ + C₂) * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4
  refine ⟨hSsum, ?_⟩
  rw [hSsplit]
  exact (add_le_add hpbound hnbound).trans_eq (by ring)

end Erdos587
