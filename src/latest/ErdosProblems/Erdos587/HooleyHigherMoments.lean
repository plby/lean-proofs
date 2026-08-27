import ErdosProblems.Erdos587.HooleySecondMoment

/-!
# Higher restricted harmonic moments

The constants are independent of the moment order, truncation parameter,
and ambient cutoff. A divisor cap on every smooth prefix is the only
extra input; its exceptional mass is handled separately.
-/

open scoped BigOperators

namespace Erdos587

lemma one_le_deltaSmoothMomentEnvelope {B : ℝ} (hB : 1 ≤ B) (q : ℕ) :
    1 ≤ deltaSmoothMomentEnvelope B q := by
  have hf : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  unfold deltaSmoothMomentEnvelope deltaMomentEnvelope
  exact one_le_mul_of_one_le_of_one_le hf
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf) (one_le_pow₀ hB))

lemma deltaLowerRestrictedError_sqrt_step (G : ℕ → Prop) [DecidablePred G]
    {A C L V : ℝ} (hA : 0 < A) (hC : 0 < C) (hL : 0 < L) (hV : 0 ≤ V)
    {q x : ℕ} (hq : 3 ≤ q) (hx : 4 ≤ x)
    (hdiv : ∀ n ∈ (deltaSmoothNumbers x).filter G,
      (n.divisors.card : ℝ) ≤ V * A * Real.log (x : ℝ))
    (hIH : ∀ a : ℕ, 2 ≤ a → a ≤ q - 1 →
      deltaLowerRestrictedMoment G (C * A * L) a x ≤
        (C * Real.log (x : ℝ) / A) * deltaSmoothMomentEnvelope (C * A * L) a / (a : ℝ) ^ 2) :
    deltaLowerRestrictedError G (C * A * L) q x ≤
      deltaLowerRestrictedError G (C * A * L) q x.sqrt +
        (16 * deltaPrimeWindowConstant * V *
          (deltaSmoothMomentEnvelope (C * A * L) q / (A * L * (q : ℝ) ^ 2))) *
            Real.log (x : ℝ) := by
  have hD := deltaPrimeWindowConstant_pos
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hy := (delta_sqrt_cutoff_bounds hx).1
  have hyx := (delta_sqrt_cutoff_bounds hx).2.le
  have hlogy : 0 < Real.log (x.sqrt : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x.sqrt by omega))
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hE := deltaSmoothMomentEnvelope_nonneg
    (show 0 ≤ C * A * L by positivity) q
  have hbound := deltaLowerRestrictedError_block_le G (by positivity : 0 < C * A * L)
    (by positivity : 0 ≤ V * A * Real.log (x : ℝ))
    (by positivity : 0 ≤ C * Real.log (x : ℝ) / A) hq hy hyx hdiv hIH
  apply hbound.trans
  apply add_le_add le_rfl
  calc
    _ = (4 * deltaPrimeWindowConstant * V *
        (deltaSmoothMomentEnvelope (C * A * L) q / (A * L * (q : ℝ) ^ 2)) *
          Real.log (x : ℝ)) * (Real.log (x : ℝ) / Real.log (x.sqrt : ℝ)) := by
      field_simp
    _ ≤ (4 * deltaPrimeWindowConstant * V *
        (deltaSmoothMomentEnvelope (C * A * L) q / (A * L * (q : ℝ) ^ 2)) *
          Real.log (x : ℝ)) * 4 := by
      apply mul_le_mul_of_nonneg_left
      · exact (div_le_iff₀ hlogy).mpr (delta_sqrt_cutoff_log_bounds hx).1
      · positivity
    _ = _ := by ring

noncomputable def deltaHigherErrorConstant (V : ℝ) : ℝ :=
  3 / Real.log 2 + 32 * deltaPrimeWindowConstant * V

lemma deltaHigherErrorConstant_pos {V : ℝ} (hV : 0 ≤ V) :
    0 < deltaHigherErrorConstant V := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD := deltaPrimeWindowConstant_pos
  unfold deltaHigherErrorConstant
  positivity

lemma deltaHigherErrorConstant_log_lower {V : ℝ} (hV : 0 ≤ V)
    {x : ℕ} (hx : 2 ≤ x) : 3 ≤ deltaHigherErrorConstant V * Real.log (x : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD := deltaPrimeWindowConstant_pos
  have hlog : Real.log 2 ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hbase : (3 : ℝ) ≤ deltaHigherErrorConstant V * Real.log 2 := by
    unfold deltaHigherErrorConstant
    have hnonneg : 0 ≤ 32 * deltaPrimeWindowConstant * V * Real.log 2 := by positivity
    have hcancel : (3 / Real.log 2 : ℝ) * Real.log 2 = 3 := by field_simp
    nlinarith only [hnonneg, hcancel]
  exact hbase.trans (mul_le_mul_of_nonneg_left hlog (deltaHigherErrorConstant_pos hV).le)

theorem deltaLowerRestrictedError_le (G : ℕ → Prop) [DecidablePred G]
    {A C L V : ℝ} (hA : 1 ≤ A) (hC : 1 ≤ C) (hL : 1 ≤ L) (hV : 0 ≤ V)
    {q X : ℕ} (hq : 3 ≤ q)
    (hdiv : ∀ x : ℕ, 2 ≤ x → x ≤ X → ∀ n ∈ (deltaSmoothNumbers x).filter G,
      (n.divisors.card : ℝ) ≤ V * A * Real.log (x : ℝ))
    (hIH : ∀ a : ℕ, 2 ≤ a → a ≤ q - 1 → ∀ x : ℕ, 2 ≤ x → x ≤ X →
      deltaLowerRestrictedMoment G (C * A * L) a x ≤
        (C * Real.log (x : ℝ) / A) * deltaSmoothMomentEnvelope (C * A * L) a / (a : ℝ) ^ 2)
    (x : ℕ) (hx : 2 ≤ x) (hxX : x ≤ X) :
    1 + deltaLowerRestrictedError G (C * A * L) q x ≤
      deltaHigherErrorConstant V *
        (deltaSmoothMomentEnvelope (C * A * L) q / (A * L * (q : ℝ) ^ 2)) *
          Real.log (x : ℝ) := by
  classical
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hB : 1 ≤ C * A * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hA) hL
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hE := deltaSmoothMomentEnvelope_nonneg (le_trans zero_le_one hB) q
  let J := deltaSmoothMomentEnvelope (C * A * L) q / (A * L * (q : ℝ) ^ 2)
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  apply delta_sqrt_recursion_log_bound_upto
    (fun y => 1 + deltaLowerRestrictedError G (C * A * L) q y)
    (mul_nonneg (deltaHigherErrorConstant_pos hV).le hJ)
    (K := 16 * deltaPrimeWindowConstant * V * J) _ _ _ x hx hxX
  · have hcost : 32 * deltaPrimeWindowConstant * V ≤ deltaHigherErrorConstant V := by
      unfold deltaHigherErrorConstant
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hpos : (0 : ℝ) ≤ 3 / Real.log 2 := by positivity
      linarith
    have h := mul_le_mul_of_nonneg_right hcost hJ
    linarith
  · intro y hy hy3 _
    have hsmall := restrictedDeltaPrimeError_small
      (fun n => G n ∧ MeetsDeltaMoments (deltaSmoothMomentEnvelope (C * A * L)) (q - 1) n)
      q hy3
    change deltaLowerRestrictedError G (C * A * L) q y ≤ (2 : ℝ) ^ q at hsmall
    have hratio : 3 * deltaSmoothMomentEnvelope (C * A * L) q /
        ((q : ℝ) ^ 2 * (C * A * L)) ≤ 3 * J := by
      calc
        _ ≤ 3 * deltaSmoothMomentEnvelope (C * A * L) q /
            ((q : ℝ) ^ 2 * (A * L)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          gcongr
          nlinarith [mul_pos hApos hLpos]
        _ = _ := by dsimp only [J]; ring
    have hbound : 1 + deltaLowerRestrictedError G (C * A * L) q y ≤ 3 * J :=
      (add_le_add (le_refl (1 : ℝ)) hsmall).trans
        ((small_cutoff_le_deltaSmoothMomentEnvelope hB (by omega : 2 ≤ q)).trans hratio)
    have hlog := mul_le_mul_of_nonneg_right (deltaHigherErrorConstant_log_lower hV hy) hJ
    nlinarith only [hbound, hlog]
  · intro y hy hyX
    have h := deltaLowerRestrictedError_sqrt_step G hApos hCpos hLpos hV hq hy
      (hdiv y (by omega) hyX) (fun a ha haq => hIH a ha haq y (by omega) hyX)
    dsimp only [J]
    linarith

lemma delta_prime_budget_mono {x X : ℕ} (hxX : x ≤ X) :
    (∑ p ∈ x.primesBelow, (1 : ℝ) / p) ≤ ∑ p ∈ X.primesBelow, (1 : ℝ) / p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpx, hp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨hpx.trans_le hxX, hp⟩
  · intro p hp hnot
    positivity

/-- Uniform restricted harmonic moment bound. The base predicate need only
be downward closed and cap the divisor function at every smooth cutoff. -/
theorem deltaLowerRestrictedMoment_bound (G : ℕ → Prop) [DecidablePred G]
    (hG1 : G 1) (hGdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → G n → G m)
    {A C L V : ℝ} (hA : 1 ≤ A) (hC : 1 ≤ C) (hL : 1 ≤ L) (hV : 0 ≤ V)
    (hbaseC : deltaSecondMomentConstant ≤ 2 * C ^ 2)
    (hstepC : (1 + deltaTailEulerConstant) * deltaHigherErrorConstant V ≤ C)
    {X : ℕ} (hbudget : (∑ p ∈ X.primesBelow, (1 : ℝ) / p) ≤ L)
    (hdiv : ∀ x : ℕ, 2 ≤ x → x ≤ X → ∀ n ∈ (deltaSmoothNumbers x).filter G,
      (n.divisors.card : ℝ) ≤ V * A * Real.log (x : ℝ))
    (q : ℕ) (hq : 2 ≤ q) (x : ℕ) (hx : 2 ≤ x) (hxX : x ≤ X) :
    deltaLowerRestrictedMoment G (C * A * L) q x ≤
      (C * Real.log (x : ℝ) / A) * deltaSmoothMomentEnvelope (C * A * L) q / (q : ℝ) ^ 2 := by
  classical
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hB : 1 ≤ C * A * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hA) hL
  induction q using Nat.strong_induction_on generalizing x with
  | h q ih =>
    have hlog : 0 ≤ Real.log (x : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
    have hbudgetx := (delta_prime_budget_mono hxX).trans hbudget
    by_cases hq2 : q = 2
    · subst q
      calc
        _ ≤ ∑ n ∈ deltaSmoothNumbers x, harmonicDeltaMoment n 2 := by
          unfold deltaLowerRestrictedMoment
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact (deltaRestrictedSet_subset _ _ _).trans (Finset.filter_subset _ _)
          · exact fun n _ _ => harmonicDeltaMoment_nonneg n 2
        _ ≤ deltaSecondMomentConstant * L * Real.log (x : ℝ) :=
          sum_deltaSmoothNumbers_harmonicDeltaMoment_two_le hx hL hbudgetx
        _ ≤ (2 * C ^ 2) * L * Real.log (x : ℝ) := by
          gcongr
        _ = _ := by
          rw [deltaSmoothMomentEnvelope_two]
          norm_num
          field_simp
          ring
    · have hq3 : 3 ≤ q := by omega
      have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      let H := fun n => G n ∧
        MeetsDeltaMoments (deltaSmoothMomentEnvelope (C * A * L)) (q - 1) n
      have hH1 : H 1 := by
        refine ⟨hG1, ?_⟩
        intro j hj hjq
        simpa only [deltaMoment_at_one (by omega : j ≠ 0), Nat.divisors_one,
          Finset.card_singleton, Nat.cast_one, div_one] using
          one_le_deltaSmoothMomentEnvelope hB j
      have hHdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → H n → H m := by
        intro m n hn hmn hHn
        exact ⟨hGdiv hn hmn hHn.1, hHn.2.of_dvd hn hmn⟩
      have hIH : ∀ a : ℕ, 2 ≤ a → a ≤ q - 1 → ∀ y : ℕ, 2 ≤ y → y ≤ X →
          deltaLowerRestrictedMoment G (C * A * L) a y ≤
            (C * Real.log (y : ℝ) / A) * deltaSmoothMomentEnvelope (C * A * L) a /
              (a : ℝ) ^ 2 := by
        intro a ha haq y hy hyX
        exact ih a (by omega) ha y hy hyX
      let J := deltaHigherErrorConstant V *
        (deltaSmoothMomentEnvelope (C * A * L) q / (A * L * (q : ℝ) ^ 2))
      have hE := deltaSmoothMomentEnvelope_nonneg (le_trans zero_le_one hB) q
      have hJ : 0 ≤ J := by
        dsimp only [J]
        exact mul_nonneg (deltaHigherErrorConstant_pos hV).le (by positivity)
      have herror (y : ℕ) (hy : 2 ≤ y) (hyx : y ≤ x) :
          1 + restrictedDeltaPrimeError H q y ≤ J * Real.log (y : ℝ) :=
        deltaLowerRestrictedError_le G hA hC hL hV hq3 hdiv hIH y hy (hyx.trans hxX)
      calc
        _ = restrictedHarmonicDeltaMoment H q x := deltaLowerRestrictedMoment_eq G _ q x
        _ ≤ (1 + deltaTailEulerConstant) * J * L * Real.log (x : ℝ) :=
          restrictedHarmonicDeltaMoment_of_error_bound H hH1 hHdiv (by omega) hx hJ hL
            hbudgetx herror
        _ = ((1 + deltaTailEulerConstant) * deltaHigherErrorConstant V) *
            ((Real.log (x : ℝ) / A) * deltaSmoothMomentEnvelope (C * A * L) q /
              (q : ℝ) ^ 2) := by
          dsimp only [J]
          field_simp
        _ ≤ C * ((Real.log (x : ℝ) / A) * deltaSmoothMomentEnvelope (C * A * L) q /
            (q : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hstepC (by positivity)
        _ = _ := by ring

noncomputable def deltaMomentInductionConstant (V : ℝ) : ℝ :=
  1 + deltaSecondMomentConstant + (1 + deltaTailEulerConstant) * deltaHigherErrorConstant V

lemma deltaMomentInductionConstant_bounds {V : ℝ} (hV : 0 ≤ V) :
    1 ≤ deltaMomentInductionConstant V ∧
      deltaSecondMomentConstant ≤ 2 * deltaMomentInductionConstant V ^ 2 ∧
        (1 + deltaTailEulerConstant) * deltaHigherErrorConstant V ≤
          deltaMomentInductionConstant V := by
  have hsecond := deltaSecondMomentConstant_pos
  have hhigher : 0 < (1 + deltaTailEulerConstant) * deltaHigherErrorConstant V :=
    mul_pos (by linarith [deltaTailEulerConstant_pos]) (deltaHigherErrorConstant_pos hV)
  have hC : 1 ≤ deltaMomentInductionConstant V := by
    unfold deltaMomentInductionConstant
    linarith
  refine ⟨hC, ?_, ?_⟩
  · have hle : deltaSecondMomentConstant ≤ deltaMomentInductionConstant V := by
      unfold deltaMomentInductionConstant
      linarith
    nlinarith only [hle, hC]
  · unfold deltaMomentInductionConstant
    linarith

end Erdos587
