import ErdosProblems.Erdos1123.WeightedBlocks
import ErdosProblems.Erdos1123.BlockBackAndForth

/-! # The ordinary density ideal as a finite-block null ideal -/

namespace Erdos1123

open Filter
open scoped Topology

def dyadicCut (n : ℕ) : ℕ := 2 ^ n

theorem dyadicCut_strictMono : StrictMono dyadicCut := pow_right_strictMono₀ (by decide)

theorem dyadicCut_cast_pos (n : ℕ) : 0 < (dyadicCut n : ℝ) := by
  exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) n)

theorem dyadicCut_double (n : ℕ) : (dyadicCut (n + 1) : ℝ) = 2 * (dyadicCut n : ℝ) := by
  simp [dyadicCut, pow_succ, mul_comm]

noncomputable def ordinaryBlocks : WeightSequence ℕ :=
  geometricBlocks (fun _ => 1) (fun n => (n : ℝ)) dyadicCut (fun _ => zero_le_one) Nat.cast_nonneg

theorem cumulative_one_univ (n : ℕ) : cumulative (fun _ => 1) Set.univ n = n := by
  simp [cumulative]

theorem ordinaryBlocks_mass_univ (n : ℕ) : ordinaryBlocks.mass Set.univ n = 1 := by
  rw [ordinaryBlocks, geometricBlocks_mass _ _ _ _ _ dyadicCut_strictMono.monotone]
  rw [cumulative_one_univ, cumulative_one_univ, dyadicCut_double]
  have hn := (dyadicCut_cast_pos n).ne'
  field_simp
  ring

noncomputable def ordinaryBlockStructure : BlockStructure ordinaryBlocks where
  disjoint := geometricBlocks_disjoint _ _ _ _ _ dyadicCut_strictMono
  atomBound n := 1 / (dyadicCut n : ℝ)
  atomBound_nonneg n := div_nonneg zero_le_one (dyadicCut_cast_pos n).le
  atomBound_tendsto :=
    (tendsto_natCast_atTop_atTop.comp dyadicCut_strictMono.tendsto_atTop).const_div_atTop 1
  weight_le _ _ _ := le_rfl
  normalized := by
    have h : ordinaryBlocks.mass Set.univ = fun _ => 1 := funext ordinaryBlocks_mass_univ
    rw [h]
    exact tendsto_const_nhds

theorem ordinary_mass_cumulative (A : Set ℕ) (n : ℕ) :
    ordinaryWeights.mass A n = cumulative (fun _ => 1) A n / n := by
  rw [ordinary_mass, cumulative_eq_sum_filter]
  simp

theorem ordinaryBlocks_null_iff (A : Set ℕ) :
    ordinaryBlocks.IsNull A ↔ ordinaryWeights.IsNull A := by
  have h := geometricBlocks_null_iff (fun _ => 1) (fun n => (n : ℝ)) dyadicCut
    (fun _ => zero_le_one) Nat.cast_nonneg dyadicCut_strictMono
    (fun _ _ h => Nat.cast_le.mpr h) tendsto_natCast_atTop_atTop
    dyadicCut_cast_pos dyadicCut_double A
  change ordinaryBlocks.IsNull A ↔ Tendsto (ordinaryWeights.mass A) atTop (𝓝 0)
  rw [funext (ordinary_mass_cumulative A)]
  exact h

end Erdos1123
