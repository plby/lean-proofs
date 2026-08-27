import ErdosProblems.Erdos587.HooleySmallCutoff
import ErdosProblems.Erdos587.HooleyRestrictedProducts
import ErdosProblems.Erdos587.HooleySqrtCutoff

/-!
# The finite restricted-moment induction

The lower moments are imposed before summing the next moment. The
largest-prime error is iterated through square-root cutoffs, and the
Mertens recurrence then recovers the harmonic moment sum.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def deltaLowerRestrictedMoment (G : ℕ → Prop) [DecidablePred G]
    (B : ℝ) (q x : ℕ) : ℝ :=
  ∑ n ∈ deltaRestrictedSet ((deltaSmoothNumbers x).filter G)
    (deltaSmoothMomentEnvelope B) (q - 1), harmonicDeltaMoment n q

noncomputable def deltaLowerRestrictedError (G : ℕ → Prop) [DecidablePred G]
    (B : ℝ) (q x : ℕ) : ℝ := by
  classical
  exact restrictedDeltaPrimeError
    (fun n => G n ∧ MeetsDeltaMoments (deltaSmoothMomentEnvelope B) (q - 1) n) q x

open Classical in
lemma deltaLowerRestrictedMoment_eq (G : ℕ → Prop) [DecidablePred G]
    (B : ℝ) (q x : ℕ) :
    deltaLowerRestrictedMoment G B q x = restrictedHarmonicDeltaMoment
      (fun n => G n ∧ MeetsDeltaMoments (deltaSmoothMomentEnvelope B) (q - 1) n) q x := by
  unfold deltaLowerRestrictedMoment restrictedHarmonicDeltaMoment
  congr 1
  ext n
  simp only [mem_deltaRestrictedSet, Finset.mem_filter, and_assoc]

lemma deltaLowerRestrictedError_block_le (G : ℕ → Prop) [DecidablePred G]
    {B U K : ℝ} (hB : 0 < B) (hU : 0 ≤ U) (hK : 0 ≤ K) {q x y : ℕ}
    (hq : 3 ≤ q) (hy : 2 ≤ y) (hyx : y ≤ x)
    (hdiv : ∀ n ∈ (deltaSmoothNumbers x).filter G, (n.divisors.card : ℝ) ≤ U)
    (hIH : ∀ a : ℕ, 2 ≤ a → a ≤ q - 1 →
      deltaLowerRestrictedMoment G B a x ≤ K * deltaSmoothMomentEnvelope B a / (a : ℝ) ^ 2) :
    deltaLowerRestrictedError G B q x ≤ deltaLowerRestrictedError G B q y +
      (deltaPrimeWindowConstant / Real.log (y : ℝ)) *
        ((4 * U * K / (q : ℝ) ^ 2) * deltaSmoothMomentEnvelope B q / B) := by
  classical
  let H := fun n => G n ∧ MeetsDeltaMoments (deltaSmoothMomentEnvelope B) (q - 1) n
  have hset : (deltaSmoothNumbers x).filter H =
      deltaRestrictedSet ((deltaSmoothNumbers x).filter G)
        (deltaSmoothMomentEnvelope B) (q - 1) := by
    ext n
    simp only [H, Finset.mem_filter, mem_deltaRestrictedSet, and_assoc]
  have hS : ∀ n ∈ (deltaSmoothNumbers x).filter G, n ≠ 0 :=
    fun n hn => (mem_deltaSmoothNumbers.mp (Finset.mem_filter.mp hn).1).1.ne_zero
  have hprod := sum_smoothed_restricted_products_le
    ((deltaSmoothNumbers x).filter G) hS hB.le hU hK hdiv hq hIH
  have hbound := restrictedDeltaPrimeError_block_le H q hy hyx
  rw [hset] at hbound
  apply hbound.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left
  · apply (le_div_iff₀ hB).mpr
    simpa only [mul_comm B] using hprod
  · exact div_nonneg deltaPrimeWindowConstant_pos.le
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))

/-- A logarithmic bound for the prime error costs only the reciprocal-prime
budget when passed through the Mertens recurrence. -/
theorem restrictedHarmonicDeltaMoment_of_error_bound (G : ℕ → Prop) [DecidablePred G]
    (hG1 : G 1) (hGdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → G n → G m)
    {q x : ℕ} (hq : q ≠ 0) (hx : 2 ≤ x) {J L : ℝ} (hJ : 0 ≤ J) (hL : 1 ≤ L)
    (hbudget : (∑ p ∈ x.primesBelow, (1 : ℝ) / p) ≤ L)
    (herror : ∀ y : ℕ, 2 ≤ y → y ≤ x →
      1 + restrictedDeltaPrimeError G q y ≤ J * Real.log (y : ℝ)) :
    restrictedHarmonicDeltaMoment G q x ≤
      (1 + deltaTailEulerConstant) * J * L * Real.log (x : ℝ) := by
  have hlog : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hsum : (∑ p ∈ x.primesBelow,
      (1 + restrictedDeltaPrimeError G q p) / ((p : ℝ) * Real.log (p : ℝ))) ≤ J * L := by
    calc
      _ ≤ ∑ p ∈ x.primesBelow, J / p := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpx, hp⟩ := Nat.mem_primesBelow.mp hp
        have hplog : 0 < Real.log (p : ℝ) :=
          Real.log_pos (by exact_mod_cast hp.one_lt)
        calc
          _ ≤ (J * Real.log (p : ℝ)) / ((p : ℝ) * Real.log (p : ℝ)) :=
            div_le_div_of_nonneg_right (herror p hp.two_le hpx.le) (by positivity)
          _ = _ := by field_simp
      _ = J * ∑ p ∈ x.primesBelow, (1 : ℝ) / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hJ
  calc
    _ ≤ (1 + restrictedDeltaPrimeError G q x) +
        deltaTailEulerConstant * Real.log (x : ℝ) *
          ∑ p ∈ x.primesBelow,
            (1 + restrictedDeltaPrimeError G q p) / ((p : ℝ) * Real.log (p : ℝ)) :=
      restrictedHarmonicDeltaMoment_mertens_bound G hG1 hGdiv hq x
    _ ≤ J * Real.log (x : ℝ) + deltaTailEulerConstant * Real.log (x : ℝ) * (J * L) :=
      add_le_add (herror x hx le_rfl)
        (mul_le_mul_of_nonneg_left hsum (mul_nonneg deltaTailEulerConstant_pos.le hlog))
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hL (mul_nonneg hJ hlog)
      nlinarith only [h]

end Erdos587
