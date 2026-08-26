import ErdosProblems.Erdos547.PairThreshold

/-!
# Fixed parameters and integer rounding for the near-core argument
-/

namespace Erdos547

def corePairDivisor : ℕ := 10 ^ 16
def coreCleaningDivisor : ℕ := 10 ^ 7
def coreDeficitDivisor : ℕ := 10 ^ 52

theorem near_core_integer_bounds (m : ℕ) (hm : coreDeficitDivisor ≤ m) :
    let d := m / coreDeficitDivisor + 1
    let k := m / corePairDivisor
    let t := m / coreCleaningDivisor
    let r := k / 8
    0 < k ∧ 0 < r ∧ 20000 * (3 * (d + k + t) + k) ≤ m ∧
      m * (d + k) ≤ t ^ 2 ∧ 4 * r ≤ k ∧ 2 * r + d ≤ m ∧ k + d ≤ m ∧
      2 * r ≤ m / (4 * corePairDivisor) := by
  let d := m / coreDeficitDivisor + 1
  let k := m / corePairDivisor
  let t := m / coreCleaningDivisor
  let r := k / 8
  change 0 < k ∧ 0 < r ∧ 20000 * (3 * (d + k + t) + k) ≤ m ∧
    m * (d + k) ≤ t ^ 2 ∧ 4 * r ≤ k ∧ 2 * r + d ≤ m ∧ k + d ≤ m ∧
    2 * r ≤ m / (4 * corePairDivisor)
  have hdk : corePairDivisor * (d + k) ≤ 2 * m := by
    dsimp [d, k, corePairDivisor, coreDeficitDivisor] at hm ⊢
    omega
  have htlow : m ≤ 2 * coreCleaningDivisor * t := by
    dsimp [t, coreCleaningDivisor, coreDeficitDivisor] at hm ⊢
    omega
  have hbudget : m * (d + k) ≤ t ^ 2 := by
    have hmul := Nat.mul_le_mul_left m hdk
    have hsq := Nat.mul_self_le_mul_self htlow
    norm_num [corePairDivisor, coreCleaningDivisor] at hmul hsq
    nlinarith only [hmul, hsq]
  refine ⟨?_, ?_, ?_, hbudget, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [d, k, t, r, corePairDivisor, coreCleaningDivisor, coreDeficitDivisor] at hm ⊢ <;> omega

theorem near_core_real_bounds (m : ℕ) (hm : coreDeficitDivisor ≤ m) :
    (1 / (2 * corePairDivisor : ℝ)) * m ≤ (m / corePairDivisor : ℕ) ∧
      (1 / (32 * corePairDivisor : ℝ)) * m ≤ (m / corePairDivisor / 8 - 1 : ℕ) ∧
      (m / coreDeficitDivisor + 1 : ℕ) ≤ (2 / coreDeficitDivisor : ℝ) * m := by
  have hk : m ≤ (2 * corePairDivisor) * (m / corePairDivisor) := by
    dsimp [corePairDivisor, coreDeficitDivisor] at hm ⊢
    omega
  have hr : m ≤ (32 * corePairDivisor) * (m / corePairDivisor / 8 - 1) := by
    dsimp [corePairDivisor, coreDeficitDivisor] at hm ⊢
    omega
  have hd : coreDeficitDivisor * (m / coreDeficitDivisor + 1) ≤ 2 * m := by
    dsimp [coreDeficitDivisor] at hm ⊢
    omega
  have hkr : (m : ℝ) ≤ (2 * corePairDivisor : ℝ) * (m / corePairDivisor : ℕ) := by
    exact_mod_cast hk
  have hrr : (m : ℝ) ≤ (32 * corePairDivisor : ℝ) * (m / corePairDivisor / 8 - 1 : ℕ) := by
    exact_mod_cast hr
  have hdr : (coreDeficitDivisor : ℝ) * (m / coreDeficitDivisor + 1 : ℕ) ≤ 2 * m := by
    exact_mod_cast hd
  constructor
  · norm_num [corePairDivisor] at hkr ⊢
    linarith
  constructor
  · norm_num [corePairDivisor] at hrr ⊢
    linarith
  · norm_num [coreDeficitDivisor] at hdr ⊢
    linarith

theorem deficit_rounding (m j : ℕ)
    (hdegree : (1 - 1 / coreDeficitDivisor : ℝ) * m ≤ j) :
    m ≤ j + (m / coreDeficitDivisor + 1) := by
  have hfloor : m < coreDeficitDivisor * (m / coreDeficitDivisor + 1) := by
    dsimp [coreDeficitDivisor]
    omega
  have hfloor' : (m : ℝ) < (coreDeficitDivisor : ℝ) * (m / coreDeficitDivisor + 1 : ℕ) := by
    exact_mod_cast hfloor
  have hreal : (m : ℝ) ≤ j + (m / coreDeficitDivisor + 1 : ℕ) := by
    norm_num [coreDeficitDivisor] at hdegree hfloor' ⊢
    linarith
  exact_mod_cast hreal

theorem core_decay_exponent_gap :
    (2 / coreDeficitDivisor : ℝ) <
      (1 / (2 * corePairDivisor : ℝ)) ^ 2 * (1 / (32 * corePairDivisor : ℝ)) / 32 := by
  norm_num [coreDeficitDivisor, corePairDivisor]

theorem small_core_integer_bounds (m M : ℕ) (hm : coreDeficitDivisor ≤ m)
    (hM : M < m / (4 * corePairDivisor)) :
    let d := m / coreDeficitDivisor + 1
    let k := m / corePairDivisor
    M ≤ k ∧ d < k ∧ 4 * (M + d) ≤ m ∧ 128 * d ≤ m := by
  dsimp [coreDeficitDivisor, corePairDivisor] at hm hM ⊢
  omega

end Erdos547

#print axioms Erdos547.near_core_integer_bounds
#print axioms Erdos547.near_core_real_bounds
