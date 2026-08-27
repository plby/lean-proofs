/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeTupleEdges

/-! # Uniform vertex probabilities for the literal source random edges -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

open scoped Classical in
def SourceProbabilityData.primeTupleEdgeProbability {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    (p q : ℕ) : ℝ :=
  ∑ n ∈ integerWeightWindow (sourceIntervalLength c x),
    if q ∈ D.primeTupleEdge S Q a p n then D.conditionedTupleMass S a p n else 0

theorem SourceProbabilityData.primeTupleEdgeProbability_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (q : ℕ) :
    0 ≤ D.primeTupleEdgeProbability S Q a p q := by
  classical
  apply Finset.sum_nonneg
  intro n _hn
  split_ifs
  · exact D.conditionedTupleMass_nonneg S a hp n
  · exact le_rfl

theorem SourceProbabilityData.primeTupleEdgeProbability_zero_of_bad {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (a : ResidueAssignment S) {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x)
    (hbad : p ∈ D.badTuplePrimes S a) (q : ℕ) :
    D.primeTupleEdgeProbability S Q a p q = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro n _hn
  by_cases hn0 : n = 0
  · subst n
    rw [D.primeTupleEdge_zero S Q hQ a (mem_commonPinnedPrimeSet.mp hp).2.2]
    simp
  · simp only [conditionedTupleMass, if_pos hbad, if_neg hn0, ite_self]

theorem SourceProbabilityData.primeTupleEdgeProbability_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x)
    (hL : 2 ≤ Real.log (x : ℝ)) (q : ℕ) :
    D.primeTupleEdgeProbability S Q a p q ≤
      (D.dimension : ℝ) * (2 * (x : ℝ) ^ (-2 / 3 + e : ℝ) /
        residueSieveDensity S ^ D.dimension) := by
  classical
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  by_cases hbad : p ∈ D.badTuplePrimes S a
  · rw [D.primeTupleEdgeProbability_zero_of_bad S Q hQ a hp hbad q]
    positivity
  have hcap := D.conditionedTupleMass_atom_bound hS a hp hbad hL
  have hmass := translatedResidueTuple_membership_mass_le (D.tupleOffsets p)
    (integerWeightWindow (sourceIntervalLength c x)) (q : ℤ) (D.conditionedTupleMass S a p)
    (by positivity) (fun n _hn => hcap n)
  rw [D.tupleOffsets_card (mem_commonPinnedPrimeSet.mp hp).2.2.pos] at hmass
  refine le_trans ?_ hmass
  apply Finset.sum_le_sum
  intro n _hn
  change (if q ∈ D.primeTupleEdge S Q a p n then D.conditionedTupleMass S a p n else 0) ≤
    if (q : ℤ) ∈ D.residueTuple p n then D.conditionedTupleMass S a p n else 0
  by_cases hq : q ∈ D.primeTupleEdge S Q a p n
  · rw [if_pos hq, if_pos ((D.mem_primeTupleEdge S Q a p n q).mp hq).2.1]
  · rw [if_neg hq]
    split_ifs
    · exact D.conditionedTupleMass_nonneg S a hp n
    · exact le_rfl

theorem eventually_primeTupleEdgeProbability_le {c e : ℝ} (he : e ≤ 1 / 120) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ≤ x) →
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ a : ResidueAssignment S,
      ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ q : ℕ,
        D.primeTupleEdgeProbability S Q a p q ≤ (x : ℝ) ^ (-3 / 5 : ℝ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 120)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_residueSieveDensity_inv_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1 / 120), hsmall,
    hlog.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hnorm hsmall hL hx
  intro D S hS hupper Q hQ a p hp q
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hlog0 := Real.log_natCast_nonneg x
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (Real.rpow_nonneg hxpos.le (1 / 120 : ℝ))] at hsmall
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [D.dimension_eq] using growingSieveDimension_le x
  have hdim := (hk.trans (Real.rpow_le_self_of_one_le hL1 (by norm_num))).trans hsmall
  have htwo : (2 : ℝ) ≤ (x : ℝ) ^ (1 / 120 : ℝ) := hL.trans hsmall
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hinv := hnorm S hS hupper D.dimension hk
  have hatom : (x : ℝ) ^ (-2 / 3 + e : ℝ) ≤ (x : ℝ) ^ (-2 / 3 + 1 / 120 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  calc
    _ ≤ (D.dimension : ℝ) * (2 * (x : ℝ) ^ (-2 / 3 + e : ℝ) /
        residueSieveDensity S ^ D.dimension) := D.primeTupleEdgeProbability_le hS Q hQ a hp hL q
    _ = ((D.dimension : ℝ) * 2 * (x : ℝ) ^ (-2 / 3 + e : ℝ)) *
        (residueSieveDensity S ^ D.dimension)⁻¹ := by ring
    _ ≤ (((x : ℝ) ^ (1 / 120 : ℝ) * (x : ℝ) ^ (1 / 120 : ℝ)) *
        (x : ℝ) ^ (-2 / 3 + 1 / 120 : ℝ)) * (x : ℝ) ^ (1 / 120 : ℝ) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul hdim htwo (by norm_num) (by positivity))
          hatom (by positivity) (by positivity)
      · exact hinv
      · positivity
      · positivity
    _ = (x : ℝ) ^ (-19 / 30 : ℝ) := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.SourceProbabilityData.primeTupleEdgeProbability_le
#print axioms Erdos4b.FGKMT.eventually_primeTupleEdgeProbability_le
