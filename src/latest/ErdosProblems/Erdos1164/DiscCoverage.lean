import ErdosProblems.Erdos1164.ExcursionAvoidance
import ErdosProblems.Erdos1165.AnnulusHarnack

/-! # A finite-disc union bound in the origin local-time clock -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1164

open Erdos1165.PointBeforeReturn

noncomputable abbrev discSites (r : ℕ) : Finset Point := Erdos1165.Annulus.closedDisc r

theorem mem_discSites (r : ℕ) (x : Point) : x ∈ discSites r ↔ x ∈ latticeDisc r :=
  Erdos1165.Annulus.mem_closedDisc_iff_radiusSqInt_le r x

/-- An explicit common lower bound for hitting a site of the disc in one
return excursion. Its denominator has logarithmic growth in the radius. -/
noncomputable def discEscape (r : ℕ) : ℝ :=
  1 / (4 + 2 * Real.log ((24 * (4 * r + 3) ^ 3 : ℕ) : ℝ))

private theorem discEscape_denominator_ge_four (r : ℕ) :
    4 ≤ 4 + 2 * Real.log ((24 * (4 * r + 3) ^ 3 : ℕ) : ℝ) := by
  have hnat : 1 ≤ 24 * (4 * r + 3) ^ 3 := Nat.succ_le_of_lt (by positivity)
  have hlog : 0 ≤ Real.log ((24 * (4 * r + 3) ^ 3 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnat)
  linarith

theorem discEscape_pos (r : ℕ) : 0 < discEscape r := by
  unfold discEscape
  exact one_div_pos.mpr (by linarith [discEscape_denominator_ge_four r])

theorem discEscape_le_one (r : ℕ) : discEscape r ≤ 1 := by
  unfold discEscape
  apply (div_le_one (by linarith [discEscape_denominator_ge_four r])).mpr
  linarith [discEscape_denominator_ge_four r]

theorem discEscape_le_pointBeforeReturn {r : ℕ} {x : Point}
    (hx : x ∈ latticeDisc r) (hx0 : x ≠ 0) :
    discEscape r ≤ pointBeforeReturnProbability x := by
  have hnorm := Erdos1165.AnnulusHarnack.manhattanNorm_le_two_mul_of_mem_closedDisc r
    ((mem_discSites r x).mpr hx)
  have hscale : pointBeforeReturnLogScale x ≤ 24 * (4 * r + 3) ^ 3 := by
    unfold pointBeforeReturnLogScale
    have hb : 2 * Erdos1165.PotentialKernel.manhattanNorm x + 3 ≤ 4 * r + 3 := by omega
    exact Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hb 3)
  have hscalePos : (0 : ℝ) < (pointBeforeReturnLogScale x : ℕ) := by
    exact_mod_cast pointBeforeReturnLogScale_pos x
  have hlog : Real.log (pointBeforeReturnLogScale x : ℝ) ≤
      Real.log ((24 * (4 * r + 3) ^ 3 : ℕ) : ℝ) :=
    Real.log_le_log hscalePos (by exact_mod_cast hscale)
  have hlog0 : 0 ≤ Real.log (pointBeforeReturnLogScale x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast pointBeforeReturnLogScale_pos x)
  apply le_trans _ (pointBeforeReturnProbability_lower_log hx0)
  unfold discEscape
  apply one_div_le_one_div_of_le (by linarith : 0 < 4 + 2 * Real.log (pointBeforeReturnLogScale x : ℝ))
  linarith

/-- The walk has accumulated many origin visits but has not covered the disc. -/
def discFailureWithVisits (n r k : ℕ) : Set WalkPath :=
  {s | k ≤ originVisits s n ∧ ¬ CoversBy s n r}

theorem measurableSet_discFailureWithVisits (n r k : ℕ) :
    MeasurableSet (discFailureWithVisits n r k) :=
  (measurableSet_le measurable_const (measurable_originVisits n)).inter
    (measurableSet_coversBy n r).compl

private theorem discFailureWithVisits_subset (n r k : ℕ) (hk : 0 < k) :
    discFailureWithVisits n r k ⊆
      ⋃ x ∈ (discSites r).erase 0, missedPointWithVisits x n k := by
  intro s hs
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (hk.trans_le hs.1)
  have hj' : j < n ∧ s j = 0 := by
    simpa only [Finset.mem_filter, Finset.mem_range] using hj
  have hnot := hs.2
  unfold CoversBy at hnot
  push Not at hnot
  obtain ⟨x, hx, hmiss⟩ := hnot
  have hx0 : x ≠ 0 := by
    intro heq
    exact hmiss j hj'.1.le (hj'.2.trans heq.symm)
  apply Set.mem_iUnion.mpr
  refine ⟨x, Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hx0, (mem_discSites r x).mpr hx⟩, ?_⟩⟩
  exact ⟨hs.1.trans (originVisits_le_localTime s n), hmiss⟩

/-- With many origin visits, failure to cover a fixed disc has an exponential
cost times the number of its lattice sites. This theorem is unconditional. -/
theorem discFailureWithVisits_bound (n r k : ℕ) (hk : 2 ≤ k) :
    walkLaw (discFailureWithVisits n r k) ≤
      (discSites r).card *
        ENNReal.ofReal (Real.exp (-(discEscape r * (k - 1 : ℕ)))) := by
  calc
    walkLaw (discFailureWithVisits n r k) ≤
        walkLaw (⋃ x ∈ (discSites r).erase 0, missedPointWithVisits x n k) :=
      measure_mono (discFailureWithVisits_subset n r k (by omega))
    _ ≤ ∑ x ∈ (discSites r).erase 0, walkLaw (missedPointWithVisits x n k) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ (discSites r).erase 0,
        ENNReal.ofReal (Real.exp (-(discEscape r * (k - 1 : ℕ)))) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨hx0, hx⟩ := Finset.mem_erase.mp hx
      apply (missedPointWithVisits_exponential x n k hx0 hk).trans
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hp := discEscape_le_pointBeforeReturn ((mem_discSites r x).mp hx) hx0
      nlinarith [show (0 : ℝ) ≤ (k - 1 : ℕ) by positivity]
    _ = ((discSites r).erase 0).card *
        ENNReal.ofReal (Real.exp (-(discEscape r * (k - 1 : ℕ)))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      gcongr
      exact Finset.erase_subset (a := (0 : Point)) (s := discSites r)

theorem discSites_card_le (r : ℕ) : (discSites r).card ≤ (2 * r + 1) ^ 2 := by
  have hcard : (discSites r).card ≤ (Erdos1165.Annulus.coordinateBox r).card :=
    Finset.card_filter_le _ _
  have heq : (Erdos1165.Annulus.coordinateBox r).card = (2 * r + 1) ^ 2 := by
    have hn : ((r : ℤ) + 1 + r).toNat = 2 * r + 1 := by omega
    simp [Erdos1165.Annulus.coordinateBox, Int.card_Icc, hn, pow_two]
  exact heq ▸ hcard

theorem discEscape_denominator_le (r : ℕ) :
    4 + 2 * Real.log ((24 * (4 * r + 3) ^ 3 : ℕ) : ℝ) ≤
      200 * Real.log ((r + 2 : ℕ) : ℝ) := by
  have hlog := half_le_log_succ (n := r + 1) (by omega)
  have h24 : Real.log 24 ≤ (23 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24)
    linarith
  have h4 : Real.log 4 ≤ (3 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have harg : (0 : ℝ) < (4 * r + 3 : ℕ) := by positivity
  have hprod : ((4 * r + 3 : ℕ) : ℝ) ≤ 4 * ((r + 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ r by positivity]
  have hlogarg := Real.log_le_log harg hprod
  rw [Real.log_mul (by norm_num) (by positivity)] at hlogarg
  have heq : Real.log ((24 * (4 * r + 3) ^ 3 : ℕ) : ℝ) =
      Real.log 24 + 3 * Real.log ((4 * r + 3 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    norm_num
  rw [heq]
  have hlog' : (1 / 2 : ℝ) ≤ Real.log ((r + 2 : ℕ) : ℝ) := by
    simpa only [Nat.add_assoc] using hlog
  nlinarith

theorem one_div_log_le_discEscape (r : ℕ) :
    1 / (200 * Real.log ((r + 2 : ℕ) : ℝ)) ≤ discEscape r := by
  unfold discEscape
  exact one_div_le_one_div_of_le
    (by linarith [discEscape_denominator_ge_four r]) (discEscape_denominator_le r)

/-- Polynomial disc size and a uniform logarithmic excursion cost. -/
theorem discFailureWithVisits_bound_log (n r k : ℕ) (hk : 2 ≤ k) :
    walkLaw (discFailureWithVisits n r k) ≤
      ((2 * r + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (Real.exp (-((k - 1 : ℕ) : ℝ) /
          (200 * Real.log ((r + 2 : ℕ) : ℝ)))) := by
  apply (discFailureWithVisits_bound n r k hk).trans
  apply mul_le_mul'
  · exact_mod_cast discSites_card_le r
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (one_div_log_le_discEscape r)
      (show (0 : ℝ) ≤ (k - 1 : ℕ) by positivity)
    simpa only [div_eq_mul_inv, one_mul, neg_mul, mul_comm] using (neg_le_neg h)

/-- Reduction of the small-radius tail to the lower tail of the origin clock.
The second term is already bounded unconditionally by the excursion argument. -/
theorem radius_lower_tail_split (n r k : ℕ) (hk : 2 ≤ k) :
    walkLaw {s | coveredRadius s n < r} ≤
      walkLaw {s | originVisits s n < k} +
        ((2 * r + 1 : ℕ) : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (Real.exp (-((k - 1 : ℕ) : ℝ) /
            (200 * Real.log ((r + 2 : ℕ) : ℝ)))) := by
  have hsub : {s : WalkPath | coveredRadius s n < r} ⊆
      {s : WalkPath | originVisits s n < k} ∪ discFailureWithVisits n r k := by
    intro s hs
    by_cases hcount : originVisits s n < k
    · exact Or.inl hcount
    · right
      refine ⟨Nat.le_of_not_gt hcount, ?_⟩
      intro hcover
      exact Nat.not_lt_of_ge hcover.le_coveredRadius hs
  exact (measure_mono hsub).trans
    ((measure_union_le _ _).trans
      (add_le_add le_rfl (discFailureWithVisits_bound_log n r k hk)))

end Erdos1164
