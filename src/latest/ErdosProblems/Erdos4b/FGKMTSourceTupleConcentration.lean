/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTupleOverlap
import ErdosProblems.Erdos4b.FGKMTSourceProbabilityData

/-! # Concentration for the constructed source tuple distributions -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

def SourceProbabilityData.tupleOffsets {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (p : ℕ) : Finset ℤ :=
  Finset.univ.image (fun i => (D.shifts i : ℤ) * p)

def SourceProbabilityData.residueTuple {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (p : ℕ) (n : ℤ) : Finset ℤ :=
  translatedResidueTuple (D.tupleOffsets p) n

theorem SourceProbabilityData.tupleOffsets_card {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {p : ℕ} (hp : 0 < p) :
    (D.tupleOffsets p).card = D.dimension := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hinj : Function.Injective (fun i => (D.shifts i : ℤ) * p) := by
    intro i j hij
    apply D.shifts_injective
    exact_mod_cast (mul_right_cancel₀ hpZ hij)
  rw [tupleOffsets, Finset.card_image_of_injective _ hinj]
  simp

theorem SourceProbabilityData.residueTuple_card {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {p : ℕ} (hp : 0 < p) (n : ℤ) :
    (D.residueTuple p n).card = D.dimension := by
  rw [residueTuple, translatedResidueTuple_card, D.tupleOffsets_card hp]

theorem SourceProbabilityData.tuple_overlap_mass_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) :
    residueTupleOverlapMass (integerWeightWindow (sourceIntervalLength c x))
      (D.mass p) (D.residueTuple p) ≤
        (D.dimension : ℝ) ^ 2 * (x : ℝ) ^ (-2 / 3 + e : ℝ) := by
  have hppos := (mem_commonPinnedPrimeSet.mp hp).2.2.pos
  have h := translatedResidueTuple_overlap_mass_le (D.tupleOffsets p)
    (integerWeightWindow (sourceIntervalLength c x)) (D.mass p)
    (fun n _hn => D.mass_nonneg p hp n) (D.mass_sum_one p hp)
    (Real.rpow_nonneg (Nat.cast_nonneg x) _) (fun n _hn => D.mass_atom_bound p hp n)
  change residueTupleOverlapMass _ _ (translatedResidueTuple (D.tupleOffsets p)) ≤ _
  simpa only [D.tupleOffsets_card hppos] using h

theorem eventually_sourceTuple_ranges {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      2 * (growingSieveDimension x : ℝ) ≤ Real.log (x : ℝ) ∧
      2 * sourceIntervalLength c x ≤ (x : ℝ) ^ 2 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).def (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [eventually_sourceIntervalLength_bounds hc, hsmall,
    hlog.eventually (eventually_ge_atTop (4 : ℝ))] with x hy hsmall hL
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hk : (growingSieveDimension x : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
    refine (growingSieveDimension_le x).trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hsqrt : Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hsmall' : Real.log (x : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * x := by
    have hh : |Real.log (x : ℝ) ^ 2| ≤ (1 / 2 : ℝ) * x := by
      simpa only [Function.comp_apply, Real.rpow_two, Real.rpow_one,
        Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ x from Nat.cast_nonneg x)] using hsmall
    exact (le_abs_self _).trans hh
  refine ⟨by linarith, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hsmall' (Nat.cast_nonneg x)
  nlinarith [hy.2.1]

theorem SourceProbabilityData.residueTuple_height {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    (hy : 2 * sourceIntervalLength c x ≤ (x : ℝ) ^ 2)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x)
    {n : ℤ} (hn : n ∈ integerWeightWindow (sourceIntervalLength c x)) :
    ∀ q ∈ D.residueTuple p n, |(q : ℝ)| ≤ (x : ℝ) ^ 2 := by
  intro q hq
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hh
  have hny := (mem_integerWeightWindow _ _).mp hn
  have hpR : (p : ℝ) ≤ x := by exact_mod_cast (mem_commonPinnedPrimeSet.mp hp).2.1
  have hhR : (D.shifts i : ℝ) ≤ 2 * (D.dimension : ℝ) ^ 2 := by
    exact_mod_cast (D.shifts_bounds i).2.2.le
  have hprod := mul_le_mul hhR hpR (Nat.cast_nonneg p) (by positivity)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have htri := abs_add_le (n : ℝ) ((D.shifts i : ℝ) * p)
  have hprod0 : (0 : ℝ) ≤ (D.shifts i : ℝ) * p :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg p)
  rw [abs_of_nonneg hprod0] at htri
  linarith

theorem eventually_source_tuple_concentration {c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ r : ℝ, 0 < r →
      (∑ a : ResidueAssignment S,
        if r * residueSieveDensity S ^ D.dimension ≤
            |(∑ n ∈ integerWeightWindow (sourceIntervalLength c x),
                D.mass p n * residueAvoidanceIndicator S (D.residueTuple p n) a) -
              residueSieveDensity S ^ D.dimension|
          then residueAssignmentMass S a else 0) ≤
        (3 * (144 / Real.log (x : ℝ) ^ 16) * (residueSieveDensity S ^ D.dimension) ^ 2 +
          (D.dimension : ℝ) ^ 2 * (x : ℝ) ^ (-2 / 3 + e : ℝ)) /
            (r * residueSieveDensity S ^ D.dimension) ^ 2 := by
  filter_upwards [eventually_uniform_weighted_residue_concentration (α := ℤ)
    (by norm_num : (0 : ℝ) ≤ 2), eventually_sourceTuple_ranges hc,
    eventually_sourceIntervalLength_bounds hc] with x hcor hranges hy
  intro D S hS hrough p hp r hr
  have hdim := growingSieveDimension_le x
  rw [← D.dimension_eq] at hdim
  have hshift := hy.2.2 D.dimension hdim
  have hk : 2 * (D.dimension : ℝ) ≤ Real.log (x : ℝ) := by
    simpa only [D.dimension_eq] using hranges.1
  have h := hcor S hS hrough (integerWeightWindow (sourceIntervalLength c x))
    (D.mass p) (D.residueTuple p) D.dimension (fun n _hn => D.mass_nonneg p hp n)
    (D.mass_sum_one p hp) (fun n _hn => D.residueTuple_card
      (mem_commonPinnedPrimeSet.mp hp).2.2.pos n) hk
    (fun _n hn => by simpa only [Real.rpow_two] using
      D.residueTuple_height hshift hranges.2 hp hn) r hr
  norm_num only [show (48 : ℝ) * (2 + 1) = 144 by norm_num] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (sq_nonneg _))
  linarith [D.tuple_overlap_mass_le hp]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.SourceProbabilityData.tuple_overlap_mass_le
#print axioms Erdos4b.FGKMT.eventually_source_tuple_concentration
