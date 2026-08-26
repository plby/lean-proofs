import ErdosProblems.Erdos421.BuchstabWeightPrimeSaving

/-! # Splitting the actual prime sum at the Buchstab branch point -/

namespace Erdos421

open MeasureTheory

noncomputable def buchstabPrimeBreakpoint (X : ℝ) : ℝ := Real.exp (Real.log X / 3)

theorem buchstabPrimeBreakpoint_one_lt {X : ℝ} (hX : 1 < X) : 1 < buchstabPrimeBreakpoint X :=
  Real.one_lt_exp_iff.mpr (div_pos (Real.log_pos hX) (by norm_num))

theorem logarithmicBuchstabArgument_breakpoint {X : ℝ} (hX : 1 < X) :
    logarithmicBuchstabArgument X (buchstabPrimeBreakpoint X) = 2 := by
  have hlog := Real.log_pos hX
  rw [logarithmicBuchstabArgument, buchstabPrimeBreakpoint, Real.log_exp]
  field_simp
  norm_num

theorem logarithmicBuchstabArgument_antitone {X : ℝ} (hX : 1 < X) :
    AntitoneOn (logarithmicBuchstabArgument X) (Set.Ioi 1) := by
  intro a ha b hb hab
  have ha1 : 1 < a := ha
  dsimp only [logarithmicBuchstabArgument]
  exact sub_le_sub_right (div_le_div_of_nonneg_left (Real.log_pos hX).le (Real.log_pos ha1)
    (Real.log_le_log (by linarith) hab)) 1

theorem logarithmicBuchstabArgument_lower_branch {X t : ℝ} (hX : 1 < X) (ht : 1 < t)
    (hct : buchstabPrimeBreakpoint X ≤ t) : logarithmicBuchstabArgument X t ≤ 2 := by
  have h := logarithmicBuchstabArgument_antitone hX
    (buchstabPrimeBreakpoint_one_lt hX) ht hct
  rwa [logarithmicBuchstabArgument_breakpoint hX] at h

theorem logarithmicBuchstabArgument_upper_branch {X t : ℝ} (hX : 1 < X) (ht : 1 < t)
    (htc : t ≤ buchstabPrimeBreakpoint X) : 2 ≤ logarithmicBuchstabArgument X t := by
  have h := logarithmicBuchstabArgument_antitone hX ht
    (buchstabPrimeBreakpoint_one_lt hX) htc
  rwa [logarithmicBuchstabArgument_breakpoint hX] at h

theorem prime_interval_sum_add (f : ℕ → ℝ) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    (∑ p ∈ primesInRealInterval a b, f p) =
      (∑ p ∈ primesInRealInterval a c, f p) + (∑ p ∈ primesInRealInterval c b, f p) := by
  simp only [primesInRealInterval, Finset.sum_filter]
  exact (Finset.sum_Ioc_consecutive (fun p ↦ if p.Prime then f p else 0)
    (Nat.floor_mono hac) (Nat.floor_mono hcb)).symm

theorem buchstabPrimeWeight_continuousOn {F : ℝ → ℝ} (hF : Continuous F) (X : ℝ) :
    ContinuousOn (buchstabPrimeWeight X F) (Set.Ioi 1) :=
  (hF.comp_continuousOn (logarithmicBuchstabArgument_continuousOn X)).mul
    reciprocalLogSquare_continuousOn

theorem buchstabPrimeDiscrepancy_add {F : ℝ → ℝ} (hF : Continuous F)
    {X a b c : ℝ} (ha : 1 < a) (hac : a ≤ c) (hcb : c ≤ b) :
    buchstabPrimeDiscrepancy X F a b =
      buchstabPrimeDiscrepancy X F a c + buchstabPrimeDiscrepancy X F c b := by
  have hc := buchstabPrimeWeight_continuousOn hF X
  have hi₁ : IntervalIntegrable (buchstabPrimeWeight X F) volume a c :=
    ContinuousOn.intervalIntegrable_of_Icc hac (hc.mono (fun _ ht ↦ ha.trans_le ht.1))
  have hi₂ : IntervalIntegrable (buchstabPrimeWeight X F) volume c b :=
    ContinuousOn.intervalIntegrable_of_Icc hcb
      (hc.mono (fun _ ht ↦ (ha.trans_le hac).trans_le ht.1))
  have hi := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have hs := prime_interval_sum_add
    (fun p ↦ F (logarithmicBuchstabArgument X p) / ((p : ℝ) * Real.log p)) hac hcb
  unfold buchstabPrimeDiscrepancy
  rw [hs, ← hi]
  ring

end Erdos421
