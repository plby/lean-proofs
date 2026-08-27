/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTWeightScalarBounds
import ErdosProblems.Erdos4b.FGKMTWeightErrorBudget
import ErdosProblems.Erdos4b.FGKMTTotalMassDecay
import ErdosProblems.Erdos4b.FGKMTPinnedPrimeChosenScales

/-!
# Joint quantitative estimates for the original sieve weights

One excluded prime precedes every dimension, admissible tuple and interval.
The remaining tuple and dimension conditions are stated explicitly; this
is not yet the random sieve or either final prime-gap theorem.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def CommonWeightEstimates (x m B : ℕ) (y : ℝ) (h : Fin (m + 1) → ℕ) (e : ℝ) : Prop :=
  let k := m + 1
  let W := dimensionPreSieveModulus k B
  let R := dimensionSieveRadius x
  let w := commonPrimeSieveWeight k W (B * W) R y h
  let tau := commonWeightTau k W (B * W) R x h
  let u := commonWeightGain m B W R x
  let error := 1 / Real.log (Real.log (x : ℝ)) ^ 10
  0 < tau ∧ 0 < u ∧ (x : ℝ) ^ (-e) ≤ tau ∧
    Real.log (k : ℝ) / 18432 ≤ u ∧ u ≤ 12 * Real.exp 24 * Real.log (k : ℝ) ∧
    (∀ p : ℕ, ∀ n : ℤ, 0 ≤ w p n) ∧
    (∀ p : ℕ, ∀ n : ℤ, y < |(n : ℝ)| → w p n = 0) ∧
    (∀ p : ℕ, ∀ n : ℤ, w p n ≤ (x : ℝ) ^ (1 / 3 + e : ℝ)) ∧
    (∀ p ∈ commonPinnedPrimeSet (x / 2) x,
      |(∑' n : ℤ, w p n) - tau * y / Real.log (x : ℝ) ^ k| /
        (tau * y / Real.log (x : ℝ) ^ k) ≤ error) ∧
    (∀ Q : ℕ, Q.Prime → x < Q → (Q : ℝ) ≤ y → ∀ j : Fin k,
      |commonPinnedPrimeMass m W (B * W) R Q (x / 2) x y h j -
          tau * (u / (k : ℝ)) * x / (2 * Real.log (x : ℝ) ^ k)| /
        (tau * (u / (k : ℝ)) * x / (2 * Real.log (x : ℝ) ^ k)) ≤ error)

theorem exists_commonWeightEstimates {e : ℝ} (he : 0 < e) :
    ∃ a : ℝ, 0 < a ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧ ∀ x : ℕ, X0 ≤ x → ∃ B : ℕ,
      1 ≤ B ∧ (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
      (B = 1 ∨ B.Prime) ∧ ∀ m : ℕ,
        1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
        (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        ∀ h : Fin (m + 1) → ℕ, Function.Injective h →
        BoundedGaps.IsAdmissible (Finset.univ.image h) →
        (∀ i, h i < 2 * (m + 1) ^ 2) → ∀ y : ℝ, (x : ℝ) ≤ y →
        2 * (m + 1 : ℕ) ^ 2 * (x : ℝ) ≤ y → CommonWeightEstimates x m B y h e := by
  obtain ⟨a, d, ha, hd, Xp, hXp, hprime⟩ := exists_commonPinnedPrimeMass_chosenScales
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Xs, hscales⟩ := eventually_atTop.mp
    ((eventually_commonPrimeSieveWeight_total_relative_decay ha.le).and
      ((eventually_commonWeightTau_ge_inv_rpow he).and
        (eventually_chosenWeightGain_bounds.and
          ((eventually_commonPrimeSieveWeight_pointwise he).and
            ((eventually_weightMeanErrors_loglog_saving 10 hd (by norm_num : (0 : ℝ) < 1)).and
              (eventually_dimensionSieveRadius_window.and
                (eventually_dimensionPrimeCutoff_le_half.and
                  (hlogTop.eventually (eventually_ge_atTop (1 : ℝ))))))))))
  refine ⟨a, ha, max Xp Xs, hXp.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxp : Xp ≤ x := (le_max_left _ _).trans hx
  have hxs : Xs ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by omega
  have hxposR : (0 : ℝ) < x := by exact_mod_cast hxpos
  obtain ⟨B, hBpos, hBbound, hB, hpin⟩ := hprime x hxp
  obtain ⟨htotal, htau, hgain, hpoint, hbudget, hR, hcut, hL⟩ := hscales x hxs
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  refine ⟨B, hBpos, hBbound, hB, ?_⟩
  intro m hm hlog hdim h hinj hadm hshift y hxy hybound
  let W := dimensionPreSieveModulus (m + 1) B
  let R := dimensionSieveRadius x
  have hk : 2 ≤ m + 1 := by omega
  have htau' := htau (m + 1) B hk hlog hdim hB h hadm
  have hgain' := hgain m B hm hlog hB
  have htaupos := (Real.rpow_pos_of_pos hxposR (-e)).trans_le htau'
  have hugainpos : 0 < commonWeightGain m B W R x :=
    (by positivity : 0 < Real.log (m + 1 : ℕ) / 18432).trans_le hgain'.1
  refine ⟨htaupos, hugainpos, htau', hgain'.1, hgain'.2,
    commonPrimeSieveWeight_nonneg _ _ _ _ _ _,
    commonPrimeSieveWeight_zero_of_outside _ _ _ _ _ _,
    hpoint (m + 1) B hk hdim y h, ?_, ?_⟩
  · intro p hp
    have hP := mem_commonPinnedPrimeSet.mp hp
    have ht := htotal (m + 1) B hk hlog hdim hB hBbound p hP.2.2 hP.1
      h hinj hadm hshift y hxy
    rw [commonWeightTau_total_identity hLpos.ne' h y]
    exact ht.trans hbudget.1
  · intro Q hQ hxQ hQy j
    have hcutoff := hcut (m + 1) hdim
    have hQW : Q.Coprime W := prime_coprime_dimensionPreSieve hQ
      (hcutoff.trans_lt ((Nat.div_le_self x 2).trans_lt hxQ))
    have hxyj : (h j : ℝ) * x ≤ y := by
      have hj : (h j : ℝ) ≤ 2 * (m + 1 : ℕ) ^ 2 := by exact_mod_cast (hshift j).le
      exact (mul_le_mul_of_nonneg_right hj (Nat.cast_nonneg x)).trans hybound
    have hp := hpin m hm hlog hdim Q y hQ hxQ hQy h hinj hadm hshift j hxyj
    have hid := commonPinnedPrimeMainTerm_tau_gain_identity hm hlog (by omega : 0 < B)
      (dimensionPreSieveModulus_pos _ _) (dimensionPreSieveModulus_coprime hB) hQW
      hR.1 hxpos hLpos.ne' (fun _p hp hpk => small_prime_dvd_dimensionPreSieve hp hpk) h j
    dsimp only at hp
    rw [hid] at hp
    exact hp.trans hbudget.2

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonWeightEstimates
