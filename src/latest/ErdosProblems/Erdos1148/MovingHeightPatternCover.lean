import ErdosProblems.Erdos1148.InitialExceptionCover
import ErdosProblems.Erdos1148.InitialCuspReturn
import ErdosProblems.Erdos1148.BufferedRunIntervals
import ErdosProblems.Erdos1148.BufferedExcursionScale

/-! # Fixed-pattern covers with one moving-height initial condition and no terminal condition -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_moving_height_pattern_lift_cover {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K C : ℝ, 1 ≤ K ∧ 1 ≤ C ∧ ∀ (g₀ : SL(2, ℝ)) (H Y : ℝ),
      1 ≤ H → 1 ≤ Y → Real.exp 1 ≤ H ^ 4 → 96 / cuspEndpointLengthSqLower ≤ H →
      ∀ (n : ℕ) (E : Set SL(2, ℝ)), LiftForwardClose η 0 E →
      (∀ g ∈ E, modularMk (g * diagonalFlow (2 * Real.log H)) ∉ modularCusp Y) →
      (∀ g ∈ E, modularCuspVisitTimes H n (modularMk (g * diagonalFlow (2 * Real.log H))) =
        modularCuspVisitTimes H n (modularMk g₀)) →
      let V := modularCuspVisitTimes H n (modularMk g₀)
      let r := (maximalNatRuns V).card
      LiftCoverBound η ((n : ℝ) + 4 * Real.log H) E
        (C * (Y * H + 1) ^ 3 * K ^ (2 * r + 1) *
          Real.exp ((n : ℝ) + 4 * Real.log H - ((V.card : ℝ) - r) / 2)) := by
  classical
  obtain ⟨Ko, hKo, hord⟩ := exists_ordinary_lift_refinement hηpos hη
  obtain ⟨Kr, hKr, hret⟩ := exists_buffered_cusp_entry_lift_refinement hηpos hη
  obtain ⟨Ci, hCi, hinit⟩ := exists_initial_cusp_run_lift_refinement hηpos hη
  let K := max 1 (max Ko Kr)
  let C := max Ci 1
  have hK : 1 ≤ K := le_max_left _ _
  have hC : 1 ≤ C := le_max_right _ _
  have hKoK : Ko ≤ K := (le_max_left Ko Kr).trans (le_max_right _ _)
  have hKrK : Kr ≤ K := (le_max_right Ko Kr).trans (le_max_right _ _)
  refine ⟨K, C, hK, hC, ?_⟩
  intro g₀ H Y hH hY hwindow hlarge n E hE hheight htimes
  let V := modularCuspVisitTimes H n (modularMk g₀)
  let r := (maximalNatRuns V).card
  let T := (n : ℝ) + 4 * Real.log H
  let J := C * (Y * H + 1) ^ 3
  have hHpos : 0 < H := by linarith
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hbase : 1 ≤ Y * H + 1 := by nlinarith
  have hpow : (1 : ℝ) ≤ (Y * H + 1) ^ 3 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hbase 3
  have hJ : 1 ≤ J := by
    have hprod := mul_le_mul hC hpow zero_le_one (zero_le_one.trans hC)
    simpa only [one_mul] using hprod
  obtain ⟨l, hfin, hnodup, hpair, hlen, hsum⟩ := exists_ordered_long_nat_runs V
  have hrun (p : ℕ × ℕ) (hp : p ∈ l) : p ∈ maximalNatRuns V ∧ p.1 < p.2 := by
    have hmem : p ∈ l.toFinset := List.mem_toFinset.mpr hp
    rw [hfin] at hmem
    exact Finset.mem_filter.mp hmem
  let intervals := l.map (bufferedRunInterval H)
  have hintervalPair : intervals.Pairwise (fun p q => p.2 ≤ q.1) :=
    bufferedRunIntervals_pairwise g₀ hHpos l (fun p hp => (hrun p hp).1) hpair
  have hbounds : ∀ p ∈ intervals, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hb := bufferedRunInterval_bounds g₀ hH (hrun q hq).1
    have hlt : (q.1 : ℝ) < q.2 := by exact_mod_cast (hrun q hq).2
    exact ⟨hb.1, by dsimp only [bufferedRunInterval]; linarith, hb.2.2⟩
  have ho : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → ∀ F ⊆ E,
      LiftForwardClose η s F → LiftCoverBound η t F (K * Real.exp (t - s)) := by
    intro s t hs hst F _ hF
    have h : LiftCoverBound η (s + (t - s)) F (Ko * Real.exp (t - s)) :=
      hord hs (sub_nonneg.mpr hst) F hF
    rw [show s + (t - s) = t by ring] at h
    exact h.mono_bound (mul_le_mul_of_nonneg_right hKoK (Real.exp_pos _).le)
  have hr : ∀ p ∈ intervals, p.1 ≠ 0 → ∀ F ⊆ E, LiftForwardClose η p.1 F →
      LiftCoverBound η p.2 F (K * Real.exp ((p.2 - p.1) / 2)) := by
    intro p hp hp0 F hFE hF
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq0 : q.1 ≠ 0 := by
      intro hz
      apply hp0
      change (q.1 : ℝ) = 0
      simp only [hz, Nat.cast_zero]
    have hL : (1 : ℝ) ≤ (q.2 : ℝ) - q.1 := by
      have hstep : (q.1 : ℝ) + 1 ≤ q.2 := by exact_mod_cast (hrun q hq).2
      linarith
    have hsmall := exp_neg_buffered_duration_small cuspEndpointLengthSqLower_pos hH
      (by linarith : (0 : ℝ) ≤ (q.2 : ℝ) - q.1) hlarge
    have hexc : ∀ g ∈ F, BufferedCuspEntry H ((q.2 : ℝ) - q.1)
        (g * diagonalFlow (bufferedRunInterval H q).1) := by
      intro g hg
      exact bufferedRunInterval_entry_of_pattern g₀ g hHpos hwindow (hrun q hq).1 hq0
        (htimes g (hFE hg))
    have hc : LiftCoverBound η ((bufferedRunInterval H q).1 +
        (((q.2 : ℝ) - q.1) + 4 * Real.log H)) F
        (Kr * Real.exp ((((q.2 : ℝ) - q.1) + 4 * Real.log H) / 2)) :=
      hret (Nat.cast_nonneg q.1) hH hL hsmall F hF hexc
    have hend : (bufferedRunInterval H q).1 + (((q.2 : ℝ) - q.1) + 4 * Real.log H) =
        (bufferedRunInterval H q).2 := by dsimp only [bufferedRunInterval]; ring
    rw [hend] at hc
    have hc' : LiftCoverBound η (bufferedRunInterval H q).2 F
        (Kr * Real.exp (((bufferedRunInterval H q).2 - (bufferedRunInterval H q).1) / 2)) := by
      simpa only [bufferedRunInterval_duration] using hc
    exact hc'.mono_bound (mul_le_mul_of_nonneg_right hKrK (Real.exp_pos _).le)
  have hi : ∀ p ∈ intervals, p.1 = 0 → LiftCoverBound η p.2 E (J * Real.exp (p.2 / 2)) := by
    intro p hp hp0
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq0 : q.1 = 0 := by
      have hcast : (q.1 : ℝ) = 0 := hp0
      exact_mod_cast hcast
    have hcusp : ∀ g ∈ E, ∀ t ∈ Set.Icc 0 (q.2 : ℝ),
        modularMk ((g * diagonalFlow (2 * Real.log H)) * diagonalFlow t) ∈ modularCusp H := by
      intro g hg
      exact bufferedRunInterval_initial_cusp_of_pattern g₀ g hHpos hwindow (hrun q hq).1 hq0
        (htimes g hg)
    have hc := hinit H Y (q.2 : ℝ) hH hY (Nat.cast_nonneg _) E hE hheight hcusp
    apply hc.mono_bound
    change Ci * (Y * H + 1) ^ 3 * Real.exp (((q.2 : ℝ) + 4 * Real.log H) / 2) ≤
      (C * (Y * H + 1) ^ 3) * Real.exp (((q.2 : ℝ) + 4 * Real.log H) / 2)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (Real.exp_pos _).le
  have hc := ordered_interval_lift_cover_initial_exception hK hJ hT hE ho intervals
    hintervalPair hbounds hr hi
  apply hc.mono_bound
  have hlength : intervals.length ≤ r := by simpa only [intervals, List.length_map] using hlen
  have hgain : (V.card : ℝ) - r ≤ (intervals.map (fun p => p.2 - p.1)).sum := by
    dsimp only [intervals]
    have hsum' : (l.map (fun p => (p.2 : ℝ) - p.1)).sum = (V.card : ℝ) - r := hsum
    rw [List.map_map, ← hsum']
    apply List.sum_le_sum
    intro p _
    dsimp only [Function.comp_apply, bufferedRunInterval]
    linarith
  have hpower := pow_le_pow_right₀ hK
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hlength) 1)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpower (zero_le_one.trans hJ))
    (Real.exp_le_exp.mpr (by linarith [hgain])) (Real.exp_pos _).le (by positivity)

end Erdos1148.DukeArithmetic
