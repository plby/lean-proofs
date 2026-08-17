/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.FactorialGrowth
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The almost-complete harmonic block

For each `N`, let `harmonicEndpoint N` be the first `M` for which the
reciprocal sum on `(N,M]` reaches one.  The block ending at `M-1` has a
positive residual of size at most `1/M`, and `M/N → e`.
-/

open Filter Finset
open scoped BigOperators Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

theorem rec_sum_Ioc_eq_harmonic_sub (N M : ℕ) (hNM : N ≤ M) :
    UnitFractions.rec_sum (Ioc N M) = harmonic M - harmonic N := by
  rw [UnitFractions.rec_sum, harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  have hsplit : Icc 1 M = Icc 1 N ∪ Ioc N M := by
    ext x
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  rw [hsplit, Finset.sum_union]
  · simp [one_div]
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [mem_Icc] at hx
    simp only [mem_Ioc] at hy
    omega

private theorem exists_harmonic_gt (R : ℚ) :
    ∃ M : ℕ, R < harmonic M := by
  have hdiv : Tendsto
      (fun n : ℕ ↦ ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1))
      atTop atTop := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨M, hM⟩ :=
    (hdiv.eventually (eventually_ge_atTop ((R : ℝ) + 1))).exists
  have hsum : (∑ i ∈ range M, (1 : ℝ) / ((i : ℝ) + 1)) =
      (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    have himage : Icc 1 M = (range M).image (fun i ↦ i + 1) := by
      ext x
      simp only [mem_Icc, mem_image, mem_range]
      constructor
      · intro hx
        exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    rw [himage, Finset.sum_image]
    · norm_num
    · intro a ha b hb hab
      simp only at hab
      omega
  have hR : (R : ℝ) < (harmonic M : ℝ) := by
    rw [← hsum]
    linarith [hM]
  exact ⟨M, by exact_mod_cast hR⟩

private theorem exists_crossing (N : ℕ) :
    ∃ M : ℕ, 1 ≤ UnitFractions.rec_sum (Ioc N M) := by
  obtain ⟨M, hM⟩ := exists_harmonic_gt (harmonic N + 1)
  refine ⟨max M N, ?_⟩
  rw [rec_sum_Ioc_eq_harmonic_sub N (max M N) (le_max_right _ _)]
  have hmono : harmonic M ≤ harmonic (max M N) := by
    rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx ↦ Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hx).1,
          (Finset.mem_Icc.mp hx).2.trans (le_max_left _ _)⟩)
      (fun _ _ _ ↦ by positivity)
  linarith

/-- The first endpoint at which the harmonic tail from `N+1` reaches one. -/
def harmonicEndpoint (N : ℕ) : ℕ :=
  Nat.find (exists_crossing N)

theorem harmonicEndpoint_spec (N : ℕ) :
    1 ≤ UnitFractions.rec_sum (Ioc N (harmonicEndpoint N)) :=
  Nat.find_spec (exists_crossing N)

theorem harmonicEndpoint_gt (N : ℕ) : N < harmonicEndpoint N := by
  by_contra h
  have hle : harmonicEndpoint N ≤ N := Nat.le_of_not_gt h
  have hempty : Ioc N (harmonicEndpoint N) = ∅ := by
    ext x
    simp [Finset.mem_Ioc]
    omega
  have hs := harmonicEndpoint_spec N
  rw [hempty] at hs
  norm_num [UnitFractions.rec_sum] at hs

theorem harmonicEndpoint_prefix_lt (N : ℕ) :
    UnitFractions.rec_sum (Ioc N (harmonicEndpoint N - 1)) < 1 := by
  have hpred : harmonicEndpoint N - 1 < harmonicEndpoint N := by
    have := harmonicEndpoint_gt N
    omega
  have hnot := Nat.find_min (exists_crossing N) hpred
  exact lt_of_not_ge hnot

theorem harmonicEndpoint_sum_lt_add_inv (N : ℕ) :
    UnitFractions.rec_sum (Ioc N (harmonicEndpoint N)) <
      1 + 1 / (harmonicEndpoint N : ℚ) := by
  have hgt := harmonicEndpoint_gt N
  have hsplit : Ioc N (harmonicEndpoint N) =
      insert (harmonicEndpoint N) (Ioc N (harmonicEndpoint N - 1)) := by
    ext x
    simp only [mem_Ioc, mem_insert]
    omega
  rw [hsplit, UnitFractions.rec_sum, Finset.sum_insert]
  · change (1 : ℚ) / harmonicEndpoint N +
      UnitFractions.rec_sum (Ioc N (harmonicEndpoint N - 1)) < _
    linarith [harmonicEndpoint_prefix_lt N]
  · simp [Finset.mem_Ioc]
    omega

theorem harmonicEndpoint_tendsto_atTop :
    Tendsto harmonicEndpoint atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop B] with N hN
  exact hN.trans (harmonicEndpoint_gt N).le

theorem harmonicEndpoint_block_tendsto_one :
    Tendsto
      (fun N : ℕ ↦
        (UnitFractions.rec_sum (Ioc N (harmonicEndpoint N)) : ℝ))
      atTop (nhds 1) := by
  have hMtop := harmonicEndpoint_tendsto_atTop
  have hinv : Tendsto (fun N : ℕ ↦ (1 : ℝ) / harmonicEndpoint N)
      atTop (nhds 0) := by
    change Tendsto
      ((fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) ∘ harmonicEndpoint)
      atTop (nhds 0)
    exact (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hMtop
  have hlower : Tendsto (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hupper : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) + 1 / (harmonicEndpoint N : ℝ))
      atTop (nhds 1) := by simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards with N
    exact_mod_cast harmonicEndpoint_spec N
  · filter_upwards with N
    have hR := (Rat.cast_le (K := ℝ)).mpr
      (harmonicEndpoint_sum_lt_add_inv N).le
    norm_num [Rat.cast_add, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast] at hR
    simpa [one_div] using hR

/-- The crossing endpoint has the sharp asymptotic ratio `e`. -/
theorem harmonicEndpoint_ratio_tendsto :
    Tendsto
      (fun N : ℕ ↦ (harmonicEndpoint N : ℝ) / (N : ℝ))
      atTop (nhds (Real.exp 1)) := by
  have hMtop := harmonicEndpoint_tendsto_atTop
  have herrN := Real.tendsto_harmonic_sub_log
  have herrM := Real.tendsto_harmonic_sub_log.comp hMtop
  have hblock := harmonicEndpoint_block_tendsto_one
  have hlogdiff : Tendsto
      (fun N : ℕ ↦ Real.log (harmonicEndpoint N : ℝ) - Real.log (N : ℝ))
      atTop (nhds 1) := by
    have hcomb := hblock.sub herrM |>.add herrN
    convert hcomb using 1
    · funext N
      rw [rec_sum_Ioc_eq_harmonic_sub N (harmonicEndpoint N)
        (harmonicEndpoint_gt N).le]
      push_cast
      simp only [Function.comp_apply]
      ring
    · ring_nf
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlogdiff
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < harmonicEndpoint N := by
    exact_mod_cast Nat.zero_lt_of_lt (harmonicEndpoint_gt N)
  change Real.exp
      (Real.log (harmonicEndpoint N : ℝ) - Real.log (N : ℝ)) = _
  rw [Real.exp_sub, Real.exp_log hMpos, Real.exp_log hNpos]

end

end Erdos284

#print axioms Erdos284.harmonicEndpoint_ratio_tendsto
