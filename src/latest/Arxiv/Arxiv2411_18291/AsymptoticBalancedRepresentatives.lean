import Arxiv.Arxiv2411_18291.BalancedCliqueRepresentatives
import Arxiv.Arxiv2411_18291.AsymptoticTypicality
import Mathlib.Data.Nat.Sqrt

/-!
# Balanced representatives uniformly over a density interval

For `ρ < 1/2`, a mean scale at least `n^(1-ρ)` dominates a group-size bound
of `sqrt(n)+1`. The simultaneous representative criterion therefore holds
for all sufficiently large `n`, uniformly in the input family and density.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_representative_failure_lt_one (r : ℕ) {ρ : ℝ} (hρ : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ θ C : ℝ, (n : ℝ) ^ (-ρ) ≤ θ → 0 < C →
      C ≤ ((n.sqrt + 1 : ℕ) : ℝ) →
      (n.choose r : ℝ) * Real.exp (-(θ * n / (3 * C))) < 1 := by
  have hlim := typicality_exp_bound_tendsto r 1 (α := 1 / 2 - ρ) (by linarith only [hρ])
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℕ)] with n hf hn
  intro θ C hθ hC hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hnat : (n.sqrt : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hsize' : C ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    push_cast at hsize
    linarith only [hsize, hsqrt, hnat]
  have hscale : (n : ℝ) ^ (1 / 2 - ρ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ (-ρ) * n := by
    rw [← Real.rpow_add hnpos, show (1 / 2 - ρ) + 1 / 2 = -ρ + 1 by ring,
      Real.rpow_add hnpos, Real.rpow_one]
  have hprod : (n : ℝ) ^ (1 / 2 - ρ) * C ≤ 2 * ((n : ℝ) ^ (-ρ) * n) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 - ρ) * (2 * (n : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsize' (Real.rpow_nonneg hnpos.le _)
      _ = _ := by rw [← hscale]; ring
  have hB := mul_le_mul_of_nonneg_right hθ hnpos.le
  have hp : 0 ≤ (n : ℝ) ^ (-ρ) * n := by positivity
  have hlow : (n : ℝ) ^ (1 / 2 - ρ) / 12 ≤ θ * n / (3 * C) := by
    apply (le_div_iff₀ (by positivity : 0 < 3 * C)).mpr
    nlinarith only [hprod, hB, hp]
  have hcount : (n.choose r : ℝ) ≤ (n : ℝ) ^ r := by exact_mod_cast Nat.choose_le_pow n r
  have hprob : Real.exp (-(θ * n / (3 * C))) ≤
      Real.exp (-((n : ℝ) ^ (1 / 2 - ρ) / 12)) := Real.exp_le_exp.mpr (neg_le_neg hlow)
  have hnonneg : 0 ≤ (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ (1 / 2 - ρ) / 12)) := by positivity
  have hf' : 6 * (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ (1 / 2 - ρ) / 12)) < 1 := by
    norm_num only [Nat.cast_one, Nat.mul_one] at hf
    exact hf
  calc
    _ ≤ (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ (1 / 2 - ρ) / 12)) :=
      mul_le_mul hcount hprob (Real.exp_pos _).le (by positivity)
    _ < 1 := by nlinarith only [hnonneg, hf']

theorem eventually_exists_balanced_clique_representatives (q r : ℕ) (hqr : r + 1 ≤ q)
    {ρ : ℝ} (hρ : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ, (n : ℝ) ^ (-ρ) ≤ θ →
      ∀ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D θ →
      ∀ G : Finset (Finset (Block (Fin n) q)), (∀ c ∈ G, c.Nonempty) →
      (∀ c ∈ G, c ⊆ D) → (Pairwise fun c d : G => Disjoint c.val d.val) →
      (∀ c ∈ G, c.card ≤ n.sqrt + 1) →
      ∃ Q : G → Block (Fin n) q, (∀ c, Q c ∈ c.val) ∧ ∀ T : Block (Fin n) r,
        (representativeDegree G Q T.val : ℝ) ≤ 2 * θ * n := by
  filter_upwards [eventually_representative_failure_lt_one r hρ] with n hnum
  intro θ hθ D hD G hne hsub hdis hsize
  have hC : (0 : ℝ) < (n.sqrt + 1 : ℕ) := by positivity
  have hfail := hnum θ ((n.sqrt + 1 : ℕ) : ℝ) hθ hC le_rfl
  have hcard (c) (hc : c ∈ G) : (c.card : ℝ) ≤ (n.sqrt + 1 : ℕ) := by
    exact_mod_cast hsize c hc
  obtain ⟨Q, hQ, hbound⟩ := exists_balanced_clique_representatives hqr D G hne hsub hdis
    hD hC hcard (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfail)
  exact ⟨Q, hQ, by simpa only [Fintype.card_fin] using hbound⟩

end Arxiv2411_18291
