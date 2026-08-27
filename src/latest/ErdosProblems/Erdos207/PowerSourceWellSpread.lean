/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceAbsorberWellSpread
import ErdosProblems.Erdos207.SourceGlobalAbsorberWellSpread
import ErdosProblems.Erdos207.PowerBankSubsetAbsorption
import ErdosProblems.Erdos207.InitialLocalizedPatternBudgets

/-! # Instantiating source well-spreadness on actual positive power-vortex prefixes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def powerBankSubsetExponent (q rootPower : ℕ) : ℕ := 3 * (156 * rootPower) * q + 1

theorem InitialPowerVortexPackage.bankSubsets_le_power
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hcoeff : powerBankSubsetCoefficient q ≤ t) :
    (subsetsUpToCard P.B q).card ≤ t ^ powerBankSubsetExponent q rootPower := by
  let c := powerAbsorberCoefficient q
  let b := 156 * rootPower
  have ht := P.base_ge_one
  have htpow : 1 ≤ t ^ (3 * b) := Nat.one_le_pow _ _ ht
  have hbank : P.B.card ≤ (c * t ^ b) ^ 3 := by
    simpa only [c, b, highGirthAbsorber_power_normalize] using P.bankCard
  have hbase : P.B.card + 1 ≤ (c ^ 3 + 1) * t ^ (3 * b) := by
    calc
      P.B.card + 1 ≤ (c * t ^ b) ^ 3 + 1 := Nat.add_le_add_right hbank 1
      _ = c ^ 3 * t ^ (3 * b) + 1 := by
        rw [mul_pow, ← pow_mul]
        simp only [Nat.mul_comm b 3]
      _ ≤ c ^ 3 * t ^ (3 * b) + t ^ (3 * b) := Nat.add_le_add_left htpow _
      _ = (c ^ 3 + 1) * t ^ (3 * b) := by ring
  calc
    _ ≤ (q + 1) * (P.B.card + 1) ^ q := card_subsetsUpToCard_le P.B q
    _ ≤ (q + 1) * ((c ^ 3 + 1) * t ^ (3 * b)) ^ q := by gcongr
    _ = powerBankSubsetCoefficient q * t ^ (3 * b * q) := by
      simp only [powerBankSubsetCoefficient, c, mul_pow, ← pow_mul]
      ring
    _ ≤ t ^ powerBankSubsetExponent q rootPower :=
      coeff_mul_pow_le_pow ht hcoeff (by simp only [powerBankSubsetExponent, b, le_refl])

theorem InitialPowerVortexPackage.bankSubsets_mul_level_le_root
    {q h n ell t rootPower step R : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (ht : 2 ≤ t) (hell : 0 < ell) (hcoeff : powerBankSubsetCoefficient q ≤ t)
    (hgap : powerBankSubsetExponent q rootPower + max rootPower (step * (ell - 1)) + 1 ≤ R)
    (hscale : t ^ R ≤ n) (i : Fin (ell + 1)) (hi : i ≠ 0) :
    (subsetsUpToCard P.B q).card * (P.W.U i).card ≤ (P.W.U 0).card := by
  let v := max rootPower (step * (ell - 1))
  have hlevel : (P.W.U i).card ≤ 2 * t ^ v := by
    rw [P.levelCard i hi]
    calc
      _ ≤ t ^ rootPower + t ^ (step * (ell - 1)) :=
        Nat.add_le_add_left (powerFreeSize_positive_le_first P.base_ge_one hell i hi) _
      _ ≤ t ^ v + t ^ v := Nat.add_le_add
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
        (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
      _ = _ := by ring
  calc
    _ ≤ t ^ powerBankSubsetExponent q rootPower * (2 * t ^ v) :=
      Nat.mul_le_mul (P.bankSubsets_le_power hcoeff) hlevel
    _ ≤ t ^ powerBankSubsetExponent q rootPower * (t * t ^ v) := by gcongr
    _ = t ^ (powerBankSubsetExponent q rootPower + v + 1) := by rw [pow_add, pow_add]; ring
    _ ≤ t ^ R := Nat.pow_le_pow_right (by omega) hgap
    _ ≤ n := hscale
    _ = (P.W.U 0).card := by rw [P.W.root, card_univ, Fintype.card_fin]

theorem InitialPowerVortexPackage.positive_prefix_sourceWellSpread
    {q h n ell t rootPower step R : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (ht : 2 ≤ t) (hell : 0 < ell) (hcoeff : powerBankSubsetCoefficient q ≤ t)
    (hgap : powerBankSubsetExponent q rootPower + max rootPower (step * (ell - 1)) + 1 ≤ R)
    (hscale : t ^ R ≤ n) (i : Fin ell) (j : ℕ) (hj : 4 ≤ j) (hjq : j ≤ q) :
    SourceVortexWellSpread (P.W.prefix i.succ) j (absorberInducedConfigurationsOn q j P.B)
      (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1))
      (2 * (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1)) +
        exactBankVortexCoefficient j (i.val + 1)) := by
  have hprefixRoot : (P.W.prefix i.succ).U 0 = P.W.U 0 := by
    change P.W.U (vortexPrefixEmbedding i.succ 0) = P.W.U 0
    congr 1
  have hterminal : 0 < (P.W.prefix i.succ).terminalSize := by
    rw [P.W.prefix_terminalSize]
    exact card_pos.mpr (P.nonempty i.succ)
  have hroot : 0 < ((P.W.prefix i.succ).U 0).card := by
    rw [hprefixRoot]
    exact card_pos.mpr (P.nonempty 0)
  have hsep : ∀ x ∈ graphSupportFinset P.H, x ∉ P.X → x ∉ (P.W.prefix i.succ).U 1 := by
    intro x hxH hxX hxU
    let k := vortexPrefixEmbedding i.succ (1 : Fin (i.succ.val + 1))
    have hk : k ≠ 0 := by
      intro hk0
      have hv := congrArg Fin.val hk0
      have hone : (1 : Fin (i.succ.val + 1)).val = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by simp only [Fin.val_succ]; omega)
      change (1 : Fin (i.succ.val + 1)).val = 0 at hv
      omega
    exact ((P.inner_separated k hk).2 x hxU hxX).1 hxH
  have hbankRoot : (subsetsUpToCard P.B q).card ≤ ((P.W.prefix i.succ).U 0).card := by
    rw [hprefixRoot]
    apply P.bankSubsets_le_root hcoeff (E := R) ?_ hscale
    change powerBankSubsetExponent q rootPower ≤ R
    omega
  have hbank : ((subsetsUpToCard P.B q).card : ℝ≥0) * (P.W.prefix i.succ).terminalSize ≤
      ((P.W.prefix i.succ).U 0).card * (1 : ℝ≥0) := by
    rw [P.W.prefix_terminalSize, hprefixRoot, mul_one]
    exact_mod_cast P.bankSubsets_mul_level_le_root ht hell hcoeff hgap hscale i.succ (Fin.succ_ne_zero i)
  exact absorberInduced_sourceVortexWellSpread_localized (P.W.prefix i.succ) P.H P.X P.B 1
    P.localization hsep hj hjq hterminal hroot hbankRoot hbank

theorem InitialPowerVortexPackage.zero_prefix_sourceWellSpread
    {q h n ell t rootPower step R : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hcoeff : powerBankSubsetCoefficient q ≤ t)
    (hgap : powerBankSubsetExponent q rootPower ≤ R) (hscale : t ^ R ≤ n)
    (j : ℕ) (hj : 4 ≤ j) :
    SourceVortexWellSpread (P.W.prefix 0) j (absorberInducedConfigurationsOn q j P.B)
      (2 * exactBankVortexOrderCoefficient q 0)
      (2 * ((subsetsUpToCard P.B q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
        exactBankVortexCoefficient j 0) := by
  have hterminal : 0 < (P.W.prefix 0).terminalSize := by
    rw [P.W.prefix_terminalSize]
    exact card_pos.mpr (P.nonempty 0)
  have hbank : (subsetsUpToCard P.B q).card ≤ (P.W.prefix 0).terminalSize := by
    rw [P.W.prefix_terminalSize]
    exact P.bankSubsets_le_root hcoeff hgap hscale
  exact absorberInduced_sourceVortexWellSpread_global (P.W.prefix 0) P.B hj hterminal hbank

end

end Erdos207
