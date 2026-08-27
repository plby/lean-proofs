/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPowerVortexPackage
import ErdosProblems.Erdos207.VortexA2LocalizedRootedThreatWeight

/-!
# Absorbing bounded bank subfamilies into the ambient root

The A2 support branch sums over bank parts of cardinality at most `q`.  Their
number is polynomial in the bank size, so a sufficiently large exponent gap
places that whole sum below `|U₀| = n`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Fixed coefficient in the coarse bounded-subset estimate for the bank. -/
def powerBankSubsetCoefficient (q : ℕ) : ℕ :=
  (q + 1) * (powerAbsorberCoefficient q ^ 3 + 1) ^ q

/-- The bank estimate stored in a power-vortex package implies the finite
absorption inequality used by the sharp A2 counts. -/
theorem InitialPowerVortexPackage.bankSubsets_le_root
    {q h n ell t rootPower step E : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hcoeff : powerBankSubsetCoefficient q ≤ t)
    (hExp : 3 * (156 * rootPower) * q + 1 ≤ E)
    (hn : t ^ E ≤ n) :
    (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card := by
  let c := powerAbsorberCoefficient q
  let b := 156 * rootPower
  have ht : 1 ≤ t := P.base_ge_one
  have htpow : 1 ≤ t ^ (3 * b) := Nat.one_le_pow _ _ ht
  have hbank : P.B.card ≤ (c * t ^ b) ^ 3 := by
    simpa only [c, b, highGirthAbsorber_power_normalize] using P.bankCard
  have hbase : P.B.card + 1 ≤ (c ^ 3 + 1) * t ^ (3 * b) := by
    calc
      P.B.card + 1 ≤ (c * t ^ b) ^ 3 + 1 := Nat.add_le_add_right hbank 1
      _ = c ^ 3 * t ^ (3 * b) + 1 := by
        rw [mul_pow, ← pow_mul]
        simp only [Nat.mul_comm b 3]
      _ ≤ c ^ 3 * t ^ (3 * b) + t ^ (3 * b) :=
        Nat.add_le_add_left htpow _
      _ = (c ^ 3 + 1) * t ^ (3 * b) := by ring
  calc
    (subsetsUpToCard P.B q).card ≤
        (q + 1) * (P.B.card + 1) ^ q := card_subsetsUpToCard_le P.B q
    _ ≤ (q + 1) * ((c ^ 3 + 1) * t ^ (3 * b)) ^ q := by gcongr
    _ = powerBankSubsetCoefficient q * t ^ (3 * b * q) := by
      simp only [powerBankSubsetCoefficient, c, mul_pow, ← pow_mul]
      ring
    _ ≤ t ^ E := coeff_mul_pow_le_pow ht hcoeff (by
      simpa only [b] using hExp)
    _ ≤ n := hn
    _ = (P.W.U 0).card := by
      rw [P.W.root, card_univ, Fintype.card_fin]

/-- Eventual initial packages can be chosen together with the exact bank
subfamily absorption inequality. -/
theorem eventually_exists_initialPowerVortexPackage_with_bankAbsorption
    (q h rootPower step ell E : ℕ)
    (hell : 0 < ell) (hroot : 2 ≤ rootPower)
    (habsorberExp : 156 * rootPower + 2 ≤ E)
    (hfreeExp : step * ell + 1 ≤ E)
    (hbankExp : 3 * (156 * rootPower) * q + 1 ≤ E) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ P : InitialPowerVortexPackage q h n ell
          (dyadicPowerScale E n) rootPower step,
        (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card := by
  obtain ⟨Npkg, hNpkg⟩ := eventually_exists_initialPowerVortexPackage
    q h rootPower step ell E hell hroot habsorberExp hfreeExp
  obtain ⟨Nbank, hNbank⟩ := eventually_le_dyadicPowerScale
    (by omega : 0 < E) (powerBankSubsetCoefficient q)
  refine ⟨max 1 (max Npkg Nbank), ?_⟩
  intro n hn
  have hpkg := hNpkg n
    ((le_max_left Npkg Nbank).trans
      ((le_max_right 1 (max Npkg Nbank)).trans hn))
  let P := Classical.choice hpkg
  refine ⟨P, P.bankSubsets_le_root
    (hNbank n ((le_max_right Npkg Nbank).trans
      ((le_max_right 1 (max Npkg Nbank)).trans hn))) hbankExp ?_⟩
  apply dyadicPowerScale_pow_le
  omega

end

end Erdos207
