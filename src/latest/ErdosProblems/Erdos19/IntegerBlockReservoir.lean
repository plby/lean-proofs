import ErdosProblems.Erdos19.BlockReservoir
import ErdosProblems.Erdos19.SavingFloorParameters

/-! # A balanced reservoir with integer error bounds -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem balanced_real_to_integer_bounds (n k L a b : ℕ) (hk : 0 < k) (hL : 0 < L)
    (hn : L ≤ n) (hbal : |(a : ℝ) - (b : ℝ) / k| < (1 / (100 * (L : ℝ))) * n) :
    b ≤ k * (a + n / L) ∧ k * a ≤ b + k * (n / L) := by
  have hepos : 1 ≤ n / L := (Nat.le_div_iff_mul_le hL).mpr (by simpa using hn)
  have hfloor := Nat.lt_mul_div_succ n hL
  have hscale := Nat.mul_le_mul_left L (show n / L + 1 ≤ 2 * (n / L) by omega)
  have hnscale : n ≤ 2 * L * (n / L) := by nlinarith only [hfloor, hscale]
  have hnR : (n : ℝ) ≤ 2 * L * (n / L : ℕ) := by exact_mod_cast hnscale
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have herror : (1 / (100 * (L : ℝ))) * n ≤ (n / L : ℕ) := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 * L)).mpr
    have hnonneg : (0 : ℝ) ≤ (n / L : ℕ) := Nat.cast_nonneg _
    nlinarith only [hnR, mul_nonneg hLr.le hnonneg]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hbal
  have hl : (b : ℝ) / k ≤ a + (n / L : ℕ) := by linarith only [hlo, herror]
  have hu : (a : ℝ) - (n / L : ℕ) ≤ (b : ℝ) / k := by linarith only [hhi, herror]
  have hl' := (div_le_iff₀ hkr).mp hl
  have hu' := (le_div_iff₀ hkr).mp hu
  constructor
  · exact_mod_cast (show (b : ℝ) ≤ k * (a + (n / L : ℕ)) by nlinarith only [hl'])
  · exact_mod_cast (show (k : ℝ) * a ≤ b + k * (n / L : ℕ) by nlinarith only [hu'])

theorem eventually_exists_integer_block_reservoir (k L : ℕ) (hk : 0 < k) (hL : 0 < L) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : _root_.SimpleGraph (Fin n),
      ∀ Y : Set (Fin n), ∃ z : Fin n → Fin k,
        (∀ v, (G.neighborSet v).ncard ≤
          k * (((insideBlocks G z).neighborSet v).ncard + n / L)) ∧
        (∀ v, k * ((insideBlocks G z).neighborSet v).ncard ≤
          (G.neighborSet v).ncard + k * (n / L)) ∧
        ∀ a, Y.ncard ≤ k * ((Y.toFinset.filter fun v ↦ z v = a).card + n / L) := by
  classical
  obtain ⟨N, hN⟩ := eventually_exists_balanced_block_reservoir k hk
    (1 / (100 * (L : ℝ))) (by positivity)
  refine ⟨max N L, ?_⟩
  intro n hn G Y
  have hnL : L ≤ n := (le_max_right _ _).trans hn
  obtain ⟨z, _, hdegree, hY⟩ := hN n ((le_max_left _ _).trans hn) G Y.toFinset
  refine ⟨z, ?_, ?_, ?_⟩
  · intro v
    exact (balanced_real_to_integer_bounds n k L _ _ hk hL hnL (hdegree v)).1
  · intro v
    exact (balanced_real_to_integer_bounds n k L _ _ hk hL hnL (hdegree v)).2
  · intro a
    have h := (balanced_real_to_integer_bounds n k L _ _ hk hL hnL (hY a)).1
    simpa only [← Set.ncard_eq_toFinset_card'] using h

#print axioms eventually_exists_integer_block_reservoir

end Erdos19
