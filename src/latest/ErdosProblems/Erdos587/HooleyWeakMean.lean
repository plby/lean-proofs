import ErdosProblems.Erdos587.HooleyPrimeCaps
import ErdosProblems.Erdos587.HooleyExceptionalMoments

/-!
# Weak harmonic mean bound for Delta

Prime-prefix caps and moment restrictions together leave a set on which
Delta is small, while discarding reciprocal mass of order `log X / A`.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def deltaHarmonicMomentConstant : ℝ :=
  deltaMomentInductionConstant deltaReciprocalMeanConstant

lemma deltaHarmonicMomentConstant_bounds :
    1 ≤ deltaHarmonicMomentConstant ∧
      deltaSecondMomentConstant ≤ 2 * deltaHarmonicMomentConstant ^ 2 ∧
        (1 + deltaTailEulerConstant) * deltaHigherErrorConstant deltaReciprocalMeanConstant ≤
          deltaHarmonicMomentConstant :=
  deltaMomentInductionConstant_bounds deltaReciprocalMeanConstant_pos.le

theorem exists_deltaSmooth_retained_set {X : ℕ} (hX : 2 ≤ X)
    {A L R : ℝ} (hA : 1 ≤ A) (hL : 1 ≤ L) (hR : 0 ≤ R)
    (hbudget : (∑ p ∈ X.primesBelow, (1 : ℝ) / p) ≤ L)
    {q : ℕ} (hq : q ≠ 0)
    (hdivexp : deltaReciprocalMeanConstant * Real.log (X : ℝ) ≤ R ^ q) :
    ∃ S ⊆ deltaSmoothNumbers X,
      (∑ n ∈ deltaSmoothNumbers X \ S, (1 : ℝ) / n) ≤
        (deltaReciprocalMeanConstant + deltaHarmonicMomentConstant) * Real.log (X : ℝ) / A ∧
      ∀ n ∈ S, (hooleyDelta n : ℝ) ≤
        2 * R * (q : ℝ) ^ 3 * (deltaHarmonicMomentConstant * A * L) := by
  classical
  let P := X.primesBelow.sort
  let G := MeetsDeltaPrimePrefixes P A
  let T := (deltaSmoothNumbers X).filter G
  let C := deltaHarmonicMomentConstant
  let E := deltaSmoothMomentEnvelope (C * A * L)
  let S := deltaRestrictedSet T E q
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hC := deltaHarmonicMomentConstant_bounds.1
  have hB : 1 ≤ C * A * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hA) hL
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hP : P.Nodup := Finset.sort_nodup _ _
  have hsorted : P.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hPset : P.toFinset = X.primesBelow := Finset.sort_toFinset _ _
  have hG1 : G 1 := meetsDeltaPrimePrefixes_one P hA
  have hGdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → G n → G m := by
    intro m n hn hmn hGn
    exact hGn.of_dvd hn.ne_zero hmn
  have hdiv : ∀ x : ℕ, 2 ≤ x → x ≤ X → ∀ n ∈ (deltaSmoothNumbers x).filter G,
      (n.divisors.card : ℝ) ≤ deltaReciprocalMeanConstant * A * Real.log (x : ℝ) := by
    intro x hx hxX n hn
    obtain ⟨hn, hGn⟩ := Finset.mem_filter.mp hn
    exact hGn.divisor_cap hP hsorted hPset hApos.le hx hxX hn
  have hmassG : (∑ n ∈ deltaSmoothNumbers X \ T, (1 : ℝ) / n) ≤
      deltaReciprocalMeanConstant * Real.log (X : ℝ) / A := by
    have hset : deltaSmoothNumbers X \ T =
        (deltaSmoothNumbers X).filter (fun n => ¬ MeetsDeltaPrimePrefixes P A n) := by
      ext n
      simp only [T, G, Finset.mem_sdiff, Finset.mem_filter]
      tauto
    rw [hset]
    apply (deltaPrimePrefixes_exceptional_mass_le hP hPset hApos).trans
    apply div_le_div_of_nonneg_right _ hApos.le
    rw [deltaPrimeChoiceMass_eq hP, hPset]
    exact delta_prime_eulerProduct_le hX _ (fun p hp =>
      Nat.mem_primesLE.mpr ⟨(Nat.mem_primesBelow.mp hp).1.le, (Nat.mem_primesBelow.mp hp).2⟩)
  have hmassM : (∑ n ∈ T \ S, (1 : ℝ) / n) ≤ C * Real.log (X : ℝ) / A := by
    apply deltaRestrictedSet_mass_bound T E q (by positivity) (by simp [E])
    · intro j hj hjq
      exact lt_of_lt_of_le zero_lt_one (one_le_deltaSmoothMomentEnvelope hB j)
    · intro j hj hjq
      exact deltaLowerRestrictedMoment_bound G hG1 hGdiv hA hC hL
        deltaReciprocalMeanConstant_pos.le deltaHarmonicMomentConstant_bounds.2.1
        deltaHarmonicMomentConstant_bounds.2.2 hbudget hdiv j hj X hX le_rfl
  have hST : S ⊆ T := deltaRestrictedSet_subset T E q
  have hTX : T ⊆ deltaSmoothNumbers X := Finset.filter_subset _ _
  refine ⟨S, hST.trans hTX, ?_, ?_⟩
  · have hsplit : (∑ n ∈ deltaSmoothNumbers X \ S, (1 : ℝ) / n) =
        (∑ n ∈ deltaSmoothNumbers X \ T, (1 : ℝ) / n) +
          ∑ n ∈ T \ S, (1 : ℝ) / n := by
      rw [Finset.sum_sdiff_eq_sub (hST.trans hTX), Finset.sum_sdiff_eq_sub hTX,
        Finset.sum_sdiff_eq_sub hST]
      ring
    rw [hsplit]
    have h := add_le_add hmassG hmassM
    apply h.trans_eq
    dsimp only [C]
    ring
  · intro n hn
    obtain ⟨hnT, hmeets⟩ := mem_deltaRestrictedSet.mp hn
    obtain ⟨hnX, hnG⟩ := Finset.mem_filter.mp hnT
    have hn0 := (mem_deltaSmoothNumbers.mp hnX).1.ne_zero
    have hcap := hdiv X hX le_rfl n (Finset.mem_filter.mpr ⟨hnX, hnG⟩)
    have hcap' : (n.divisors.card : ℝ) ≤ A * R ^ q := by
      have h := mul_le_mul_of_nonneg_left hdivexp hApos.le
      nlinarith only [hcap, h]
    have hAB : A ≤ C * A * L := by
      have h := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hC hL) hApos.le
      nlinarith only [h]
    exact hooleyDelta_le_of_meets_smooth_moments hn0 hq (le_trans zero_le_one hB)
      hAB hR hcap' hmeets

noncomputable def deltaDivisorExponentialConstant : ℝ :=
  Real.exp (1 + |Real.log deltaReciprocalMeanConstant|)

lemma deltaDivisorExponentialConstant_pos : 0 < deltaDivisorExponentialConstant :=
  Real.exp_pos _

lemma deltaDivisor_log_le_exponential {X q : ℕ} (hX : 2 ≤ X) (hq : 1 ≤ q)
    (hlog : Real.log (Real.log (X : ℝ)) ≤ q) :
    deltaReciprocalMeanConstant * Real.log (X : ℝ) ≤ deltaDivisorExponentialConstant ^ q := by
  have hV := deltaReciprocalMeanConstant_pos
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have habs := le_abs_self (Real.log deltaReciprocalMeanConstant)
  have hmul := mul_le_mul_of_nonneg_right hqR (abs_nonneg (Real.log deltaReciprocalMeanConstant))
  calc
    _ = Real.exp (Real.log deltaReciprocalMeanConstant + Real.log (Real.log (X : ℝ))) := by
      rw [Real.exp_add, Real.exp_log hV, Real.exp_log hlogX]
    _ ≤ Real.exp ((q : ℝ) * (1 + |Real.log deltaReciprocalMeanConstant|)) := by
      apply Real.exp_monotone
      nlinarith only [hlog, habs, hmul]
    _ = _ := Real.exp_nat_mul _ q

noncomputable def deltaWeakThresholdConstant : ℝ :=
  16 * deltaDivisorExponentialConstant * deltaHarmonicMomentConstant

lemma deltaWeakThresholdConstant_pos : 0 < deltaWeakThresholdConstant := by
  have hR := deltaDivisorExponentialConstant_pos
  have hC := deltaHarmonicMomentConstant_bounds.1
  unfold deltaWeakThresholdConstant
  positivity

open Classical in
/-- A weak reciprocal-mass bound with the fourth power of the log-log
budget. Both constants are absolute and independent of `A` and `X`. -/
theorem deltaSmooth_weak_mean {X : ℕ} (hX : 2 ≤ X) {A L : ℝ}
    (hA : 1 ≤ A) (hL : 1 ≤ L)
    (hbudget : (∑ p ∈ X.primesBelow, (1 : ℝ) / p) ≤ L)
    (hloglog : Real.log (Real.log (X : ℝ)) ≤ L) :
    (∑ n ∈ (deltaSmoothNumbers X).filter
        (fun n => deltaWeakThresholdConstant * A * L ^ 4 < (hooleyDelta n : ℝ)),
      (1 : ℝ) / n) ≤
        (deltaReciprocalMeanConstant + deltaHarmonicMomentConstant) * Real.log (X : ℝ) / A := by
  let q := ⌈L⌉₊
  have hqL : L ≤ (q : ℝ) := Nat.le_ceil L
  have hq : 1 ≤ q := by
    have hqR : (1 : ℝ) ≤ q := hL.trans hqL
    exact_mod_cast hqR
  have hq2L : (q : ℝ) ≤ 2 * L := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ L by linarith)
    dsimp only [q]
    linarith
  obtain ⟨S, hSX, hmass, hpoint⟩ := exists_deltaSmooth_retained_set hX hA hL
    deltaDivisorExponentialConstant_pos.le hbudget (by omega : q ≠ 0)
    (deltaDivisor_log_le_exponential hX hq (hloglog.trans hqL))
  have hthreshold : 2 * deltaDivisorExponentialConstant * (q : ℝ) ^ 3 *
      (deltaHarmonicMomentConstant * A * L) ≤ deltaWeakThresholdConstant * A * L ^ 4 := by
    have hR := deltaDivisorExponentialConstant_pos
    have hC := deltaHarmonicMomentConstant_bounds.1
    calc
      _ ≤ 2 * deltaDivisorExponentialConstant * (2 * L) ^ 3 *
          (deltaHarmonicMomentConstant * A * L) := by gcongr
      _ = _ := by unfold deltaWeakThresholdConstant; ring
  apply le_trans _ hmass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnX, hnlarge⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_sdiff.mpr
    refine ⟨hnX, ?_⟩
    intro hnS
    exact (not_le_of_gt hnlarge) ((hpoint n hnS).trans hthreshold)
  · intro n hn hnot
    positivity

end Erdos587
