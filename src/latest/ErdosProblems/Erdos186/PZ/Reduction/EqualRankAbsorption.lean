/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Asymptotic

/-!
# The scalar absorption estimate in the equal-rank case

The retained-population product controls all moves, whereas only the
same-rank moves supply an explicit `gamma` factor.  The lower bound
`m^(-1/3) <= gamma` pays for the bounded number of dimension-changing
moves.  When those moves are at most twice the total rank saving and
`2/3 <= a`, that loss is absorbed by the rank-saving power `m^(-a q)`.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

/-- Scalar core of the equal-rank estimate in Pham--Zakharov Lemma 10. -/
theorem equalRank_shrink_up_bound
    (m L changes shrinks q K : ℕ) (x delta gamma a : ℝ)
    (hdelta0 : 0 < delta) (hgamma0 : 0 < gamma)
    (hgammaDelta : gamma ≤ delta ^ K)
    (hgammaLower : Real.rpow (m : ℝ) (-(1 / 3 : ℝ)) ≤ gamma)
    (hretention : delta ^ L * (m : ℝ) ≤ x)
    (hlength : L = changes + shrinks)
    (hchanges : changes ≤ 2 * q)
    (hm : 2 ≤ m) (ha : (2 / 3 : ℝ) ≤ a) :
    gamma ^ shrinks *
        (Real.rpow (m : ℝ) (-a)) ^ q ≤
      (x / (m : ℝ)) ^ K := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  have hgammaNonneg : 0 ≤ gamma := hgamma0.le
  have hx : 0 ≤ x := by
    exact (mul_nonneg (pow_nonneg hdeltaNonneg _) hmpos.le).trans hretention
  have hratioNonneg : 0 ≤ x / (m : ℝ) := div_nonneg hx hmpos.le
  have hretentionDiv : delta ^ L ≤ x / (m : ℝ) :=
    (le_div_iff₀ hmpos).2 hretention
  have htotal : gamma ^ L ≤ (x / (m : ℝ)) ^ K := by
    calc
      gamma ^ L ≤ (delta ^ K) ^ L :=
        pow_le_pow_left₀ hgammaNonneg hgammaDelta _
      _ = (delta ^ L) ^ K := by
        calc
          (delta ^ K) ^ L = delta ^ (K * L) := (pow_mul delta K L).symm
          _ = delta ^ (L * K) :=
            congrArg (delta ^ ·) (Nat.mul_comm K L)
          _ = (delta ^ L) ^ K := pow_mul delta L K
      _ ≤ (x / (m : ℝ)) ^ K :=
        pow_le_pow_left₀ (pow_nonneg hdeltaNonneg _) hretentionDiv _
  have hgammaProduct : gamma ^ shrinks * gamma ^ changes ≤
      (x / (m : ℝ)) ^ K := by
    calc
      gamma ^ shrinks * gamma ^ changes = gamma ^ L := by
        rw [← pow_add, hlength, Nat.add_comm]
      _ ≤ (x / (m : ℝ)) ^ K := htotal
  have hgammaChanges : 0 < gamma ^ changes := pow_pos hgamma0 _
  have hshrinkDiv : gamma ^ shrinks ≤
      (x / (m : ℝ)) ^ K / gamma ^ changes :=
    (le_div_iff₀ hgammaChanges).2 hgammaProduct
  have hlowerPow :
      (Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ changes ≤
        gamma ^ changes :=
    pow_le_pow_left₀ (Real.rpow_nonneg hmpos.le _) hgammaLower _
  have hlowerPowPos :
      0 < (Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ changes :=
    pow_pos (Real.rpow_pos_of_pos hmpos _) _
  have hinv : (gamma ^ changes)⁻¹ ≤
      ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ changes)⁻¹ :=
    (inv_le_inv₀ hgammaChanges hlowerPowPos).2 hlowerPow
  have hrpowPow : ∀ (z : ℝ) (n : ℕ),
      (Real.rpow (m : ℝ) z) ^ n =
        Real.rpow (m : ℝ) (z * (n : ℝ)) := by
    intro z n
    have hnat := Real.rpow_natCast (Real.rpow (m : ℝ) z) n
    have hmul : Real.rpow (m : ℝ) (z * (n : ℝ)) =
        Real.rpow (Real.rpow (m : ℝ) z) (n : ℝ) :=
      Real.rpow_mul hmpos.le z (n : ℝ)
    exact hnat.symm.trans hmul.symm
  have hinvPower :
      ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ changes)⁻¹ =
        Real.rpow (m : ℝ) ((changes : ℝ) / 3) := by
    calc
      ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ changes)⁻¹ =
          (Real.rpow (m : ℝ)
            ((-(1 / 3 : ℝ)) * (changes : ℝ)))⁻¹ := by rw [hrpowPow]
      _ = Real.rpow (m : ℝ)
          (-((-(1 / 3 : ℝ)) * (changes : ℝ))) :=
        (Real.rpow_neg hmpos.le _).symm
      _ = Real.rpow (m : ℝ) ((changes : ℝ) / 3) := by
        congr 1
        ring
  have hshrink : gamma ^ shrinks ≤
      (x / (m : ℝ)) ^ K *
        Real.rpow (m : ℝ) ((changes : ℝ) / 3) := by
    calc
      gamma ^ shrinks ≤ (x / (m : ℝ)) ^ K / gamma ^ changes := hshrinkDiv
      _ = (x / (m : ℝ)) ^ K * (gamma ^ changes)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (x / (m : ℝ)) ^ K *
          ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ changes)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (pow_nonneg hratioNonneg _)
      _ = (x / (m : ℝ)) ^ K *
          Real.rpow (m : ℝ) ((changes : ℝ) / 3) := by rw [hinvPower]
  have hchangesReal : (changes : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hchanges
  have hexponent : (changes : ℝ) / 3 - a * (q : ℝ) ≤ 0 := by
    have hqnonneg : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have habsorb :
      Real.rpow (m : ℝ) ((changes : ℝ) / 3) *
          (Real.rpow (m : ℝ) (-a)) ^ q ≤ 1 := by
    rw [hrpowPow]
    calc
      Real.rpow (m : ℝ) ((changes : ℝ) / 3) *
          Real.rpow (m : ℝ) ((-a) * (q : ℝ)) =
        Real.rpow (m : ℝ)
          ((changes : ℝ) / 3 + (-a) * (q : ℝ)) :=
            (Real.rpow_add hmpos _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (show 1 ≤ m by omega)) (by linarith)
  calc
    gamma ^ shrinks * (Real.rpow (m : ℝ) (-a)) ^ q ≤
        ((x / (m : ℝ)) ^ K *
          Real.rpow (m : ℝ) ((changes : ℝ) / 3)) *
            (Real.rpow (m : ℝ) (-a)) ^ q := by
      exact mul_le_mul_of_nonneg_right hshrink
        (pow_nonneg (Real.rpow_nonneg hmpos.le _) _)
    _ = (x / (m : ℝ)) ^ K *
        (Real.rpow (m : ℝ) ((changes : ℝ) / 3) *
          (Real.rpow (m : ℝ) (-a)) ^ q) := by ring
    _ ≤ (x / (m : ℝ)) ^ K * 1 :=
      mul_le_mul_of_nonneg_left habsorb (pow_nonneg hratioNonneg _)
    _ = (x / (m : ℝ)) ^ K := by ring

end

end Erdos186.PZ.Reduction
