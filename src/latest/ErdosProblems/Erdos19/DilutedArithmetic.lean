import ErdosProblems.Erdos19.DilutedTentativeMean
import ErdosProblems.Erdos19.FactorialSlack

/-! # Elementary estimates for diluted coloring cylinders -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem half_power_le_pred_power (K d : ℕ) (hK : 0 < K) (hd : 2 * d ≤ K) :
    K ^ d ≤ 2 * (K - 1) ^ d := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hdR : (2 : ℝ) * d ≤ K := by exact_mod_cast hd
  let r : ℝ := ((K : ℝ) - 1) / K
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hK1) hKR.le
  have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ r by linarith only [hr]) d
  have hid : 1 + (d : ℝ) * (r - 1) = 1 - (d : ℝ) / K := by
    dsimp only [r]
    field_simp
    ring
  have hdiv : (d : ℝ) / K ≤ 1 / 2 := (div_le_iff₀ hKR).mpr (by linarith only [hdR])
  have hhalf : (1 : ℝ) / 2 ≤ r ^ d := by rw [hid] at hbern; linarith only [hbern, hdiv]
  dsimp only [r] at hhalf
  rw [div_pow] at hhalf
  have hpow := (le_div_iff₀ (pow_pos hKR d)).mp hhalf
  have hpow' : (K : ℝ) ^ d ≤ 2 * ((K : ℝ) - 1) ^ d := by linarith only [hpow]
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ K by omega), Nat.cast_one]
  rw [← hcast] at hpow'
  exact_mod_cast hpow'

theorem mixed_cylinder_half_bound (K N d : ℕ) (hK : 0 < K)
    (hd : 2 * d ≤ K) (hN : d + 2 ≤ N) :
    K ^ N ≤ 2 * K ^ 2 * ((K - 1) ^ d * K ^ (N - d - 2)) := by
  have hpow := half_power_le_pred_power K d hK hd
  calc
    K ^ N = K ^ 2 * (K ^ d * K ^ (N - d - 2)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ K ^ 2 * ((2 * (K - 1) ^ d) * K ^ (N - d - 2)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
    _ = _ := by ring

theorem dilutedTentative_expectation_scaled {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A) (v : V)
    (hC : 0 < C) (hdegree : 2 ≤ (G.neighborSet v).ncard)
    (hpalette : 2 * (G.neighborSet v).ncard ≤ A * C) :
    C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
        Fintype.card (V → Fin A × Fin C) ≤
      2 * (A * C) ^ 2 * (∑ sample : V → Fin A × Fin C,
        (tentativeCollisionColors G (dilutedSample active sample) v).ncard) := by
  have hA : 0 < A := Nat.zero_lt_of_lt active.isLt
  have hK : 0 < A * C := Nat.mul_pos hA hC
  have hd : 2 * ((G.neighborSet v).ncard - 2) ≤ A * C := by omega
  have hN : (G.neighborSet v).ncard - 2 + 2 ≤ Fintype.card V := by
    have h := Set.ncard_le_card (G.neighborSet v)
    rw [Nat.card_eq_fintype_card] at h
    omega
  have hcyl := mixed_cylinder_half_bound (A * C) (Fintype.card V)
    ((G.neighborSet v).ncard - 2) hK hd hN
  have hmean := dilutedTentativeCollision_expectation_lower_bound G (C := C) active v
  have h₁ := Nat.mul_le_mul_left (C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard) hcyl
  have h₂ := Nat.mul_le_mul_left (2 * (A * C) ^ 2) hmean
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  nlinarith only [h₁, h₂]

#print axioms dilutedTentative_expectation_scaled

end Erdos19
