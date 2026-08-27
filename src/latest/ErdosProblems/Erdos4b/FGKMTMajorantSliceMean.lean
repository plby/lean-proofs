/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMajorantSliceCost
import ErdosProblems.Erdos4b.FGKMTDoubleSmoothMean
import ErdosProblems.Erdos4b.FGKMTTensorDenominators

/-! # Full-support harmonic mean and upper bound for a majorant slice -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def majorantSliceSieveSum (k M R m : ℕ) (g : ℕ → ℝ) (t : Fin m → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 0 (R ^ 2),
    sieveProfileMajorant k (m + 1) (Fin.cons (Real.log a / Real.log R) t) *
      roughSieveWeight M g a

theorem exists_majorantSliceSieveSum_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R : ℕ}, 2 ≤ k → 10000 ≤ Real.log k → 0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      ∀ (pinned : Bool) (m : ℕ) (t : Fin m → ℝ),
        |majorantSliceSieveSum k M R m (actualSieveDenominator pinned k) t -
          sieveMainConstant M (actualSieveDenominator pinned k) * Real.log R *
            majorantFaceValue k m t| ≤
          C * sieveMainConstant M (actualSieveDenominator pinned k) * (k : ℝ) *
            sieveProfileScale k * modulusLogScale M ^ 3 * majorantFaceValue k m t := by
  obtain ⟨C₁, hC₁, hmean⟩ := exists_roughSieveWeight_double_smooth_error_logScale
  obtain ⟨C₂, hC₂, hderiv⟩ := exists_sieveProfileMajorant_cons_deriv_bound
  refine ⟨2 * C₁ * C₂, by positivity, ?_⟩
  intro k M R hk hlog hM hR hsmall pinned m t
  have hk0 : 0 < k := by omega
  let g := actualSieveDenominator pinned k
  let G := fun x => sieveProfileMajorant k (m + 1) (Fin.cons x t)
  have hchain := actualSieveDenominator_chain hk (by omega : 1 ≤ k) hsmall pinned
  have hg (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) :
      (p : ℝ) / 2 ≤ g p ∧ |g p - p| ≤ 2 * (k : ℝ) ∧ g p ≤ p - 1 := by
    simpa only [g, Nat.cast_zero, add_zero] using hchain 0 (by omega) p hp hpM
  have hG2 : G 2 = 0 :=
    sieveProfileMajorant_zero_of_coord_ge_two hk0 hlog (0 : Fin (m + 1)) le_rfl
  have h := hmean hk0 hM hR (fun p hp hpk => hsmall p hp (by omega)) g
    (fun p hp hpM => (hg p hp hpM).1) (fun p hp hpM => (hg p hp hpM).2.1)
    (fun p hp hpM => (hg p hp hpM).2.2) (sieveProfileMajorant_cons_contDiff k m t)
    (V := C₂ * (k : ℝ) * sieveProfileScale k * majorantFaceValue k m t)
    (fun x hx => hderiv hk0 hlog m t x hx.1)
  change |majorantSliceSieveSum k M R m g t -
    sieveMainConstant M g * Real.log R * (∫ x in (0 : ℝ)..2, G x)| ≤
      C₁ * sieveMainConstant M g * modulusLogScale M ^ 3 *
        (|G 2| + 2 * (C₂ * (k : ℝ) * sieveProfileScale k * majorantFaceValue k m t)) at h
  rw [hG2, abs_zero, zero_add] at h
  have hint : (∫ x in (0 : ℝ)..2, G x) = majorantFaceValue k m t :=
    (majorantFaceValue_eq_interval hk0 hlog m t).symm
  rw [hint] at h
  convert h using 1
  ring

theorem harmonic_majorant_upper_of_error {S K L V C k T D : ℝ}
    (hK : 0 ≤ K) (hV : 0 ≤ V) (hcost : C * k * T * D ≤ L)
    (h : |S - K * L * V| ≤ C * K * k * T * D * V) :
    S ≤ 2 * K * L * V := by
  have hleft := (le_abs_self (S - K * L * V)).trans h
  have hc := mul_le_mul_of_nonneg_right hcost (mul_nonneg hK hV)
  nlinarith

theorem exists_majorantSliceSieveSum_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R : ℕ}, 2 ≤ k → 10000 ≤ Real.log k → 0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      C * (k : ℝ) * sieveProfileScale k * modulusLogScale M ^ 3 ≤ Real.log R →
      ∀ (pinned : Bool) (m : ℕ) (t : Fin m → ℝ),
        majorantSliceSieveSum k M R m (actualSieveDenominator pinned k) t ≤
          2 * sieveMainConstant M (actualSieveDenominator pinned k) * Real.log R *
            majorantFaceValue k m t := by
  obtain ⟨C, hC, herror⟩ := exists_majorantSliceSieveSum_error
  refine ⟨C, hC, ?_⟩
  intro k M R hk hlog hM hR hsmall hcost pinned m t
  have hchain := actualSieveDenominator_chain hk (by omega : 1 ≤ k) hsmall pinned
  have hg (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) := hchain 0 (by omega) p hp hpM
  simp only [Nat.cast_zero, add_zero] at hg
  have hK := sieveMainConstant_pos (k := k) (by omega) hM
    (fun p hp hpk => hsmall p hp (by omega)) (actualSieveDenominator pinned k)
    (fun p hp hpM => (hg p hp hpM).1) (fun p hp hpM => (hg p hp hpM).2.1)
    (fun p hp hpM => (hg p hp hpM).2.2)
  exact harmonic_majorant_upper_of_error hK.le (majorantFaceValue_nonneg k m t) hcost
    (herror hk hlog hM hR hsmall pinned m t)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_majorantSliceSieveSum_error
#print axioms Erdos4b.FGKMT.exists_majorantSliceSieveSum_upper
