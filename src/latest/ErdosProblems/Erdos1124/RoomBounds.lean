/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Choosing blocks with enough room for a bounded flow

The flow-to-matching argument for circle squaring tiles every free orbit by
large cubes.  A block of side `M` contains order `M ^ d` points of either
set, while at most order `M ^ (d - 1)` units of flow cross any one of its
faces.  This file isolates the elementary arithmetic which lets the volume
term dominate both the discrepancy error and the boundary-flow capacity.

Two interfaces are supplied.  `capacity_le_count_of_lower_bound` consumes an
unnormalized count estimate with an `M ^ (d - 1)` error.  The second interface,
`capacity_le_count_of_density_error`, consumes the normalized discrepancy
estimate used by the analytic part of the proof.  The scale may be chosen to
be a power of two, as required by the dyadic flow construction.
-/

open scoped BigOperators NNReal

namespace Erdos1124.RoomBounds

/-- At a base at least one, an extra nonnegative negative exponent only makes
the real power smaller. -/
lemma rpow_neg_one_add_le_inv {x delta : ℝ} (hx : 1 ≤ x) (hdelta : 0 ≤ delta) :
    x ^ (-(1 + delta)) ≤ x⁻¹ := by
  calc
    x ^ (-(1 + delta)) ≤ x ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = x⁻¹ := Real.rpow_neg_one x

/-- A dyadic integer can be chosen large enough simultaneously to absorb a
fixed discrepancy constant and a fixed boundary-flow constant. -/
theorem exists_dyadic_room_scale {mu C K delta : ℝ}
    (hmu : 0 < mu) (hC : 0 ≤ C) (hdelta : 0 ≤ delta) :
    ∃ k : ℕ, let M : ℕ := 2 ^ k
      C * (M : ℝ) ^ (-(1 + delta)) ≤ mu / 2 ∧
        K ≤ (mu / 2) * M := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    (max (2 * C / mu) (2 * K / mu)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_, ?_⟩
  · have hMpos : 0 < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hMone : 1 ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_pow k 2 (by omega))
    have hthreshold : 2 * C / mu < ((2 ^ k : ℕ) : ℝ) :=
      (le_max_left _ _).trans_lt (by exact_mod_cast hk)
    have hscaled : 2 * C < ((2 ^ k : ℕ) : ℝ) * mu :=
      (div_lt_iff₀ hmu).mp hthreshold
    have hdiv : C / ((2 ^ k : ℕ) : ℝ) ≤ mu / 2 := by
      apply (div_le_iff₀ hMpos).2
      nlinarith
    calc
      C * (((2 ^ k : ℕ) : ℝ) ^ (-(1 + delta))) ≤
          C * (((2 ^ k : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (rpow_neg_one_add_le_inv hMone hdelta) hC
      _ = C / ((2 ^ k : ℕ) : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ mu / 2 := hdiv
  · have hthreshold : 2 * K / mu < ((2 ^ k : ℕ) : ℝ) :=
      (le_max_right _ _).trans_lt (by exact_mod_cast hk)
    have hscaled : 2 * K < ((2 ^ k : ℕ) : ℝ) * mu :=
      (div_lt_iff₀ hmu).mp hthreshold
    nlinarith

/-- If the count in a block has main term `mu * M ^ d` and an error bounded
by `C * M ^ (d - 1)`, then the simple inequality
`C + D * b ≤ mu * M` leaves room for all `D` faces, each carrying at most
`b * M ^ (d - 1)` units of flow. -/
theorem capacity_le_count_of_lower_bound
    {mu C : ℝ} {D b d M count : ℕ}
    (hd : 0 < d)
    (hcount : mu * (M : ℝ) ^ d - C * (M : ℝ) ^ (d - 1) ≤ count)
    (hroom : C + (D * b : ℕ) ≤ mu * M) :
    D * (b * M ^ (d - 1)) ≤ count := by
  have hpow : (M : ℝ) ^ d = (M : ℝ) * (M : ℝ) ^ (d - 1) := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp [pow_succ, mul_comm]
  have hfactor :
      ((D * b : ℕ) : ℝ) * (M : ℝ) ^ (d - 1) ≤
        (mu * (M : ℝ) - C) * (M : ℝ) ^ (d - 1) := by
    gcongr
    linarith
  have hmain :
      (((D * (b * M ^ (d - 1))) : ℕ) : ℝ) ≤
        mu * (M : ℝ) ^ d - C * (M : ℝ) ^ (d - 1) := by
    calc
      (((D * (b * M ^ (d - 1))) : ℕ) : ℝ) =
          ((D * b : ℕ) : ℝ) * (M : ℝ) ^ (d - 1) := by
            push_cast
            ring
      _ ≤ (mu * (M : ℝ) - C) * (M : ℝ) ^ (d - 1) := hfactor
      _ = mu * (M : ℝ) ^ d - C * (M : ℝ) ^ (d - 1) := by
        rw [hpow]
        ring
  exact_mod_cast hmain.trans hcount

/-- A normalized discrepancy estimate supplies at least half of the expected
density once its error is at most `mu / 2`.  If the other half of the density
dominates `D * b / M`, it pays for all bounded face flows. -/
theorem capacity_le_count_of_density_error
    {mu error : ℝ} {D b d M count : ℕ}
    (hd : 0 < d) (hM : 0 < M)
    (hdensity :
      |(count : ℝ) / (M : ℝ) ^ d - mu| ≤ error)
    (herror : error ≤ mu / 2)
    (hcapacity : ((D * b : ℕ) : ℝ) ≤ (mu / 2) * M) :
    D * (b * M ^ (d - 1)) ≤ count := by
  have hdenpos : 0 < (M : ℝ) ^ d := by positivity
  have hlower := (abs_le.mp hdensity).1
  have hdensity_lower :
      mu / 2 ≤ (count : ℝ) / (M : ℝ) ^ d := by
    linarith
  have hcount_lower :
      (mu / 2) * (M : ℝ) ^ d ≤ count :=
    (le_div_iff₀ hdenpos).mp hdensity_lower
  have hpow : (M : ℝ) ^ d = (M : ℝ) * (M : ℝ) ^ (d - 1) := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp [pow_succ, mul_comm]
  have hcapreal :
      (((D * (b * M ^ (d - 1))) : ℕ) : ℝ) ≤
        (mu / 2) * (M : ℝ) ^ d := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, hpow]
    calc
      (D : ℝ) * ((b : ℝ) * (M : ℝ) ^ (d - 1)) =
          (((D * b : ℕ) : ℝ)) * (M : ℝ) ^ (d - 1) := by
            norm_num [mul_assoc]
      _ ≤ ((mu / 2) * (M : ℝ)) * (M : ℝ) ^ (d - 1) := by
        gcongr
      _ = (mu / 2) * ((M : ℝ) * (M : ℝ) ^ (d - 1)) := by ring
  exact_mod_cast hcapreal.trans hcount_lower

/-- Combined dyadic-scale API for normalized discrepancy.  At the returned
scale, *every* positive dimension and every count satisfying the advertised
discrepancy estimate has enough room for the stated boundary capacity. -/
theorem exists_dyadic_capacity_le_count
    {mu C delta : ℝ} (D b : ℕ)
    (hmu : 0 < mu) (hC : 0 ≤ C) (hdelta : 0 ≤ delta) :
    ∃ k : ℕ, let M : ℕ := 2 ^ k
      ∀ {d count : ℕ}, 0 < d →
        |(count : ℝ) / (M : ℝ) ^ d - mu| ≤
          C * (M : ℝ) ^ (-(1 + delta)) →
        D * (b * M ^ (d - 1)) ≤ count := by
  obtain ⟨k, herror, hcapacity⟩ := exists_dyadic_room_scale
    (K := ((D * b : ℕ) : ℝ)) hmu hC hdelta
  refine ⟨k, ?_⟩
  dsimp
  intro d count hd hdensity
  exact capacity_le_count_of_density_error hd (by positivity) hdensity
    herror hcapacity

end Erdos1124.RoomBounds
