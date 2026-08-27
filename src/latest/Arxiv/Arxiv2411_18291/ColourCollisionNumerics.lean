import Arxiv.Arxiv2411_18291.AsymptoticCliqueCount

/-!
# Polynomial collision budgets

If the extension family has size at least `c*n^(m-a)` and the marginal
probability is at least `b*n^(-β)`, the collision term is a relative
`n^(-κ)` error whenever `a+2*β*M+κ<1`.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem colour_collision_scale {x : ℝ} (hx : 0 < x) (b c a β κ : ℝ) (M : ℕ) :
    x ^ (-κ) * (c * x ^ (-a)) * x * (b * x ^ (-β)) ^ (2 * M) =
      c * b ^ (2 * M) * x ^ (1 - κ - a - 2 * β * M) := by
  have he : x ^ (-κ) * x ^ (-a) = x ^ (-(κ + a)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc
    _ = c * ((x ^ (-κ) * x ^ (-a)) * (x * (b * x ^ (-β)) ^ (2 * M))) := by ring
    _ = c * (b ^ (2 * M) * x ^ (1 - (κ + a) - β * (2 * M))) := by
      rw [he, clique_count_scale hx b β (κ + a) (2 * M)]
      push_cast
      rfl
    _ = _ := by
      rw [show 1 - (κ + a) - β * (2 * (M : ℝ)) = 1 - κ - a - 2 * β * M by ring]
      ring

theorem eventually_colour_collision_bound (m M : ℕ) {b c a β κ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hgap : a + 2 * β * M + κ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ A p : ℝ,
      (c * (n : ℝ) ^ (-a)) * (n : ℝ) ^ m ≤ A → b * (n : ℝ) ^ (-β) ≤ p →
      (m : ℝ) ^ 2 * (n : ℝ) ^ (m - 1) ≤ (n : ℝ) ^ (-κ) * A * p ^ (2 * M) := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < 1 - κ - a - 2 * β * M)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop ((m : ℝ) ^ 2 / (c * b ^ (2 * M))))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge] with n hn hln
  intro A p hA hp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ (n : ℝ) ^ (-κ) := Real.rpow_nonneg hnpos.le _
  have hη : 0 < c * (n : ℝ) ^ (-a) := mul_pos hc (Real.rpow_pos_of_pos hnpos _)
  have hp0 : 0 < b * (n : ℝ) ^ (-β) := mul_pos hb (Real.rpow_pos_of_pos hnpos _)
  have hAnonneg : 0 ≤ A := (mul_nonneg hη.le (pow_nonneg hnpos.le _)).trans hA
  have hpnonneg : 0 ≤ p := hp0.le.trans hp
  have hsmall : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ (-κ) * (c * (n : ℝ) ^ (-a)) * n *
      (b * (n : ℝ) ^ (-β)) ^ (2 * M) := by
    rw [colour_collision_scale hnpos]
    have h := (div_le_iff₀ (mul_pos hc (pow_pos hb (2 * M)))).mp hln
    simpa only [Function.comp_def, mul_comm] using h
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
    positivity
  · have hpow : (n : ℝ) ^ (m - 1) * n = (n : ℝ) ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    calc
      _ ≤ ((n : ℝ) ^ (-κ) * (c * (n : ℝ) ^ (-a)) * n *
          (b * (n : ℝ) ^ (-β)) ^ (2 * M)) * (n : ℝ) ^ (m - 1) :=
        mul_le_mul_of_nonneg_right hsmall (pow_nonneg hnpos.le _)
      _ = (n : ℝ) ^ (-κ) * ((c * (n : ℝ) ^ (-a)) * (n : ℝ) ^ m) *
          (b * (n : ℝ) ^ (-β)) ^ (2 * M) := by rw [← hpow]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hA hδ)
        (pow_le_pow_left₀ hp0.le hp _) (pow_nonneg hp0.le _) (mul_nonneg hδ hAnonneg)

end Arxiv2411_18291
