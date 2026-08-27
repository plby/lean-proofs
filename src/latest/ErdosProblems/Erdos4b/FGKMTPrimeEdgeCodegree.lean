/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeEdgeSparsity

/-! # Summed codegrees of the actual source prime edges -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem upperHalfPrimeDivisors_card_le_one {x : ℕ} {d : ℤ}
    (hd : d ≠ 0) (hheight : |(d : ℝ)| < (x : ℝ) ^ 2 / 4) :
    ((commonPinnedPrimeSet (x / 2) x).filter fun p : ℕ => (p : ℤ) ∣ d).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  by_contra hne
  obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpP', hpd'⟩ := Finset.mem_filter.mp hp'
  have hP := mem_commonPinnedPrimeSet.mp hpP
  have hP' := mem_commonPinnedPrimeSet.mp hpP'
  have hdiv := Nat.Prime.dvd_mul_of_dvd_ne hne hP.2.2 hP'.2.2
    (Int.natCast_dvd.mp hpd) (Int.natCast_dvd.mp hpd')
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hdiv
  have hprod : (p : ℝ) * p' ≤ |(d : ℝ)| := by
    have hh : ((p * p' : ℕ) : ℝ) ≤ (d.natAbs : ℝ) := by exact_mod_cast hle
    simpa only [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs] using hh
  have hp2 : x < 2 * p := by omega
  have hp2' : x < 2 * p' := by omega
  have hpR : (x : ℝ) / 2 < p := by
    have hh : (x : ℝ) < 2 * p := by exact_mod_cast hp2
    linarith
  have hpR' : (x : ℝ) / 2 < p' := by
    have hh : (x : ℝ) < 2 * p' := by exact_mod_cast hp2'
    linarith
  have hlarge : (x : ℝ) ^ 2 / 4 < (p : ℝ) * p' := by
    calc
      _ = ((x : ℝ) / 2) * ((x : ℝ) / 2) := by ring
      _ ≤ (p : ℝ) * ((x : ℝ) / 2) := mul_le_mul_of_nonneg_right hpR.le (by positivity)
      _ < _ := mul_lt_mul_of_pos_left hpR' (by exact_mod_cast hP.2.2.pos)
  exact (lt_irrefl _) ((hprod.trans_lt hheight).trans hlarge)

open scoped Classical in
def SourceProbabilityData.primeTupleEdgePairProbability {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    (p q q' : ℕ) : ℝ :=
  ∑ n ∈ integerWeightWindow (sourceIntervalLength c x),
    if q ∈ D.primeTupleEdge S Q a p n ∧ q' ∈ D.primeTupleEdge S Q a p n
      then D.conditionedTupleMass S a p n else 0

theorem SourceProbabilityData.primeTupleEdgePairProbability_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (q q' : ℕ) :
    0 ≤ D.primeTupleEdgePairProbability S Q a p q q' := by
  classical
  apply Finset.sum_nonneg
  intro n _hn
  split_ifs
  · exact D.conditionedTupleMass_nonneg S a hp n
  · exact le_rfl

theorem SourceProbabilityData.primeTupleEdgePairProbability_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (q q' : ℕ) :
    D.primeTupleEdgePairProbability S Q a p q q' ≤ D.primeTupleEdgeProbability S Q a p q := by
  classical
  apply Finset.sum_le_sum
  intro n _hn
  by_cases hboth : q ∈ D.primeTupleEdge S Q a p n ∧ q' ∈ D.primeTupleEdge S Q a p n
  · rw [if_pos hboth, if_pos hboth.1]
  · rw [if_neg hboth]
    split_ifs
    · exact D.conditionedTupleMass_nonneg S a hp n
    · exact le_rfl

theorem SourceProbabilityData.primeTupleEdgePairProbability_zero_of_not_dvd
    {c e : ℝ} {x : ℕ} (D : SourceProbabilityData c e x) (S Q : Finset ℕ)
    (a : ResidueAssignment S) {p q q' : ℕ} (hd : ¬(p : ℤ) ∣ (q : ℤ) - q') :
    D.primeTupleEdgePairProbability S Q a p q q' = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro n _hn
  rw [if_neg (fun h => hd (D.primeTupleEdge_pair_dvd S Q a h.1 h.2))]

theorem SourceProbabilityData.primeTupleEdge_codegree_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    {q q' : ℕ} (hne : q ≠ q') (hheight : |(q : ℝ) - q'| < (x : ℝ) ^ 2 / 4)
    {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ p ∈ commonPinnedPrimeSet (x / 2) x, D.primeTupleEdgeProbability S Q a p q ≤ B) :
    (∑ p ∈ commonPinnedPrimeSet (x / 2) x, D.primeTupleEdgePairProbability S Q a p q q') ≤ B := by
  classical
  let J := (commonPinnedPrimeSet (x / 2) x).filter fun p : ℕ => (p : ℤ) ∣ (q : ℤ) - q'
  have hd : (q : ℤ) - q' ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hcard : J.card ≤ 1 := upperHalfPrimeDivisors_card_le_one hd (by
    simpa only [Int.cast_sub, Int.cast_natCast] using hheight)
  have hsupport : (∑ p ∈ commonPinnedPrimeSet (x / 2) x,
      D.primeTupleEdgePairProbability S Q a p q q') =
      ∑ p ∈ J, D.primeTupleEdgePairProbability S Q a p q q' := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    apply D.primeTupleEdgePairProbability_zero_of_not_dvd S Q a
    intro hdiv
    exact hnot (Finset.mem_filter.mpr ⟨hp, hdiv⟩)
  rw [hsupport]
  calc
    _ ≤ ∑ _p ∈ J, B := Finset.sum_le_sum fun p hp =>
      (D.primeTupleEdgePairProbability_le S Q a (Finset.mem_filter.mp hp).1 q q').trans
        (hpoint p (Finset.mem_filter.mp hp).1)
    _ = (J.card : ℝ) * B := by simp
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
    _ = _ := one_mul _

theorem eventually_sourceIntervalLength_lt_quarter_sq {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, sourceIntervalLength c x < (x : ℝ) ^ 2 / 4 := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).def (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [eventually_sourceIntervalLength_bounds hc, hsmall,
    eventually_ge_atTop (1 : ℕ)] with x hy hsmall hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hsmall' : Real.log (x : ℝ) ^ 2 ≤ (1 / 8 : ℝ) * x := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.rpow_one,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (x : ℝ))),
      abs_of_nonneg hxR.le] using hsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall' hxR.le
  nlinarith [hy.2.1, sq_pos_of_pos hxR]

theorem eventually_source_primeTupleEdge_codegree_le {c e : ℝ}
    (hc : 0 < c) (he : e ≤ 1 / 120) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ≤ x) →
      ∀ a : ResidueAssignment S, ∀ q ∈ sourceSievingPrimes c x,
      ∀ q' ∈ sourceSievingPrimes c x, q ≠ q' →
      (∑ p ∈ commonPinnedPrimeSet (x / 2) x,
        D.primeTupleEdgePairProbability S (sourceSievingPrimes c x) a p q q') ≤
          (x : ℝ) ^ (-1 / 20 : ℝ) := by
  filter_upwards [eventually_primeTupleEdgeProbability_le (c := c) he,
    eventually_sourceIntervalLength_lt_quarter_sq hc, eventually_sourceIntervalLength_bounds hc,
    eventually_ge_atTop (1 : ℕ)] with x hsparse hheight hy hx
  intro D S hS hupper a q hq q' hq' hne
  have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
  have hQprime : ∀ r ∈ sourceSievingPrimes c x, r.Prime :=
    fun r hr => ((mem_sourceSievingPrimes hy0).mp hr).1
  have hqy := ((mem_sourceSievingPrimes hy0).mp hq).2.2
  have hq'y := ((mem_sourceSievingPrimes hy0).mp hq').2.2
  have hdheight : |(q : ℝ) - q'| < (x : ℝ) ^ 2 / 4 := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hq'0 : (0 : ℝ) ≤ q' := Nat.cast_nonneg q'
    have hdle : |(q : ℝ) - q'| ≤ sourceIntervalLength c x :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact hdle.trans_lt hheight
  have h := D.primeTupleEdge_codegree_le S (sourceSievingPrimes c x) a hne hdheight
    (Real.rpow_nonneg (Nat.cast_nonneg x) _) (fun p hp =>
      hsparse D S hS hupper (sourceSievingPrimes c x) hQprime a p hp q)
  exact h.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.upperHalfPrimeDivisors_card_le_one
#print axioms Erdos4b.FGKMT.eventually_source_primeTupleEdge_codegree_le
