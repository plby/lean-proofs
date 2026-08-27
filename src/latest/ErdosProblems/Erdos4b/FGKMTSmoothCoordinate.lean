/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRoughSupport
import ErdosProblems.Erdos4b.FGKMTSmoothMean

/-!
# A uniform smooth estimate after removing one coordinate

The remaining product `e` may be any natural number up to `E`. Its
squarefree and coprimality constraints are enforced by the weight itself.
The error has the same shifted arithmetic weight as the main term, which
is necessary for an induction that does not lose a constant at every prime.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem modulusLogScale_mono {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    modulusLogScale M ≤ modulusLogScale N := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : Real.log M ≤ Real.log N := Real.log_le_log hMR (by exact_mod_cast hMN)
  have hMlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have harg : 0 < 4 + Real.log M := by linarith
  have hargle : 4 + Real.log M ≤ 4 + Real.log N := by linarith
  have houter := Real.log_le_log harg hargle
  unfold modulusLogScale
  linarith

theorem exists_roughSieveWeight_smooth_coordinate_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R E e : ℕ}, 0 < k → 0 < M → 1 < R → e ≤ E →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G → ∀ {V : ℝ},
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      |(∑ n ∈ Finset.Icc 0 R,
          G (Real.log n / Real.log R) * roughSieveWeight M g (e * n)) -
        sieveMainConstant M g * roughSieveWeight M (fun p => g p + 1) e *
          Real.log R * (∫ x in (0 : ℝ)..1, G x)| ≤
          C * sieveMainConstant M g * roughSieveWeight M (fun p => g p + 1) e *
            modulusLogScale (M * E) ^ 3 * (|G 1| + V) := by
  obtain ⟨C, hC, hbound⟩ := exists_roughSieveWeight_smooth_error_logScale
  refine ⟨C, hC, ?_⟩
  intro k M R E e hk hM hR heE hsmall g hg hclose hupper G hG V hV
  have hrec := sieveMainConstant_coordinate_recurrence_all hk hM hsmall g hg hclose e
  rw [sum_roughSieveWeight_mul]
  by_cases hfe : roughSieveWeight M g e = 0
  · have hc := sieveMainConstant_pos hk hM hsmall g hg hclose hupper
    have he1 : roughSieveWeight M (fun p => g p + 1) e = 0 := by
      rw [hfe, mul_zero] at hrec
      exact (mul_eq_zero.mp hrec.symm).resolve_left hc.ne'
    simp [hfe, he1]
  · have hepos : 0 < e := Nat.pos_of_ne_zero (roughSieveWeight_support hfe).1.ne_zero
    have hMe : 0 < M * e := Nat.mul_pos hM hepos
    have hsmallMe p hp hpk : p ∣ M * e := dvd_mul_of_dvd_left (hsmall p hp hpk) e
    have hnotM p (hpMe : ¬p ∣ M * e) : ¬p ∣ M :=
      fun hpM => hpMe (dvd_mul_of_dvd_left hpM e)
    have hb := hbound hk hMe hR hsmallMe g
      (fun p hp hpMe => hg p hp (hnotM p hpMe))
      (fun p hp hpMe => hclose p hp (hnotM p hpMe))
      (fun p hp hpMe => hupper p hp (hnotM p hpMe)) hG hV
    have hfe0 : 0 ≤ roughSieveWeight M g e := roughSieveWeight_nonneg M g
      (fun p hp hpM => (half_pos (show (0 : ℝ) < p by exact_mod_cast hp.pos)).le.trans
        (hg p hp hpM)) e
    have hfe1 : 0 ≤ roughSieveWeight M (fun p => g p + 1) e := roughSieveWeight_nonneg M _
      (fun p hp hpM => by
        have hgp := hg p hp hpM
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        linarith) e
    have hc0 := (sieveMainConstant_pos hk hM hsmall g hg hclose hupper).le
    have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, zero_le_one⟩)
    have hscale := modulusLogScale_mono hMe (Nat.mul_le_mul_left M heE)
    have hscalePow : modulusLogScale (M * e) ^ 3 ≤ modulusLogScale (M * E) ^ 3 :=
      pow_le_pow_left₀ (zero_le_one.trans (one_le_modulusLogScale _)) hscale 3
    have hmain :
        roughSieveWeight M g e * sieveMainConstant (M * e) g =
          sieveMainConstant M g * roughSieveWeight M (fun p => g p + 1) e := by
      simpa only [mul_comm (roughSieveWeight M g e)] using hrec
    have hidentity :
        roughSieveWeight M g e *
            (∑ n ∈ Finset.Icc 0 R, G (Real.log n / Real.log R) * roughSieveWeight (M * e) g n) -
          sieveMainConstant M g * roughSieveWeight M (fun p => g p + 1) e *
            Real.log R * (∫ x in (0 : ℝ)..1, G x) =
        roughSieveWeight M g e *
          ((∑ n ∈ Finset.Icc 0 R, G (Real.log n / Real.log R) * roughSieveWeight (M * e) g n) -
            sieveMainConstant (M * e) g * Real.log R * (∫ x in (0 : ℝ)..1, G x)) := by
      rw [← hmain]
      ring
    rw [hidentity, abs_mul, abs_of_nonneg hfe0]
    calc
      _ ≤ roughSieveWeight M g e *
          (C * sieveMainConstant (M * e) g * modulusLogScale (M * e) ^ 3 * (|G 1| + V)) :=
        mul_le_mul_of_nonneg_left hb hfe0
      _ = C * sieveMainConstant M g * roughSieveWeight M (fun p => g p + 1) e *
          modulusLogScale (M * e) ^ 3 * (|G 1| + V) := by
        calc
          _ = C * (roughSieveWeight M g e * sieveMainConstant (M * e) g) *
              modulusLogScale (M * e) ^ 3 * (|G 1| + V) := by ring
          _ = _ := by rw [hmain]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscalePow (by positivity)) (by positivity)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_roughSieveWeight_smooth_coordinate_error
