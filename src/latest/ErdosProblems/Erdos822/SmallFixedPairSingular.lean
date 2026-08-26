/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmallFixedPairMass
import ErdosProblems.Erdos822.SmallQuadraticCharge
import ErdosProblems.Erdos822.GILSingularMajorant
import ErdosProblems.Erdos822.MediumRangeGcdMass

/-! # The complete singular average in one fixed small-divisor fiber -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

noncomputable def smallOffDiagonalPrimePairs (N S : ℕ) (C : ℝ) (k m' h : ℕ) : Finset (ℕ × ℕ) :=
  (fixedCommonDivisorPrimePairs (gilCofactors N S C) N (N ^ 60) k m' h).filter
    (fun rq ↦ k * rq.1 * rq.2 ≠ m')

theorem exists_eventually_small_fixedPair_singular_bound {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ k m' h U : ℕ,
      k ∈ oddSmallFactors N → m' ∈ gilCofactors N S C → 0 < h → h ≤ N ^ 3 →
      h ∣ shiftedTotient m' → roughPart h (b1Cutoff N) = h → Nat.log 2 N ≤ U →
      (∑ rq ∈ smallOffDiagonalPrimePairs N S C k m' h,
        ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) *
          Erdos851.singularFactor (reducedTotientDet (k * rq.1 * rq.2) m') 2 U) ≤
        K * Real.log (b1Cutoff N : ℝ) * (4 : ℝ) ^ h.primeFactors.card / (h : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbase⟩ := exists_eventually_small_fixedPair_mass_bound (C + 2)
  obtain ⟨D, hD, hcharge⟩ := exists_eventually_fixedPair_determinantCharge_bound (C + 2)
  obtain ⟨M, hM, hmajor⟩ := exists_eventually_gil_fullSingularFactor_le_charge hS C
  refine ⟨M * (A + D), by positivity, ?_⟩
  filter_upwards [hbase, hcharge, hmajor, eventually_gilCofactors_divisor_primeMass_le hS C,
    eventually_ge_atTop 2, tendsto_b1Cutoff_atTop.eventually_ge_atTop 2,
    tendsto_b1DoubleLog_atTop.eventually_ge_atTop 4]
    with N hbase hcharge hmajor hmass hN hy hZ
  intro k m' h U hk hm' hh hhN hhF hrough hLU
  let B := gilCofactors N S C
  let Q := fixedCommonDivisorPrimePairs B N (N ^ 60) k m' h
  let Z := b1DoubleLog N
  let L := Nat.log 2 N
  let R : ℝ := (Z : ℝ) / Real.log (Z : ℝ)
  let f : ℕ × ℕ → ℝ := fun rq ↦ smallDeterminantMass L Z k rq.1 rq.2 m' h
  have hlogZ : 1 ≤ Real.log (Z : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hZ
  have hlogZpos : 0 < Real.log (Z : ℝ) := by linarith only [hlogZ]
  have hZR : (0 : ℝ) < Z := by exact_mod_cast (by omega : 0 < Z)
  have hlogy : 0 < Real.log (b1Cutoff N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b1Cutoff N))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hB := gilCofactors_subset_squarefreeLargeGcdFree N S C
  have hhMass := hmass m' hm' h hhF
  have hbase' := hbase B k m' h (b1Cutoff N) hB hm' hk hh hhN hhMass hrough
    (b1Cutoff_lt_pow_twentyone hN)
  have hcharge' := hcharge B k m' h L Z (b1Cutoff N) hB hm' hk hh hhN hhMass hrough
    (b1Cutoff_lt_pow_twentyone hN) (Nat.log_le_self 2 N) (by omega)
  have hscaled : R * (D * (4 : ℝ) ^ h.primeFactors.card /
      ((h : ℝ) ^ 2 * Z * Real.log (Z : ℝ))) ≤ D * (4 : ℝ) ^ h.primeFactors.card / (h : ℝ) ^ 2 := by
    calc
      _ = (D * (4 : ℝ) ^ h.primeFactors.card / (h : ℝ) ^ 2) / (Real.log (Z : ℝ)) ^ 2 := by
        dsimp [R]
        have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
        field_simp
      _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hlogZ)
  calc
    _ ≤ M * Real.log (b1Cutoff N : ℝ) *
        ∑ rq ∈ smallOffDiagonalPrimePairs N S C k m' h, ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) * (1 + R * f rq) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      rintro ⟨r, q⟩ hrq
      obtain ⟨hrq, hne⟩ := Finset.mem_filter.mp hrq
      have hd := mem_fixedCommonDivisorPrimePairs_iff.mp hrq
      have hpoint := hmajor k r q m' h U (mem_oddCofactorTriples_iff.mpr ⟨hk, hd.1, hd.2.1⟩)
        hd.2.2.1 hm' hne hd.2.2.2.1 hhF hLU
      have h := mul_le_mul_of_nonneg_left hpoint (by positivity : (0 : ℝ) ≤ 1 / (r * q : ℕ))
      convert h using 1 <;> dsimp [R, f, L, Z] <;> ring
    _ ≤ M * Real.log (b1Cutoff N : ℝ) *
        ∑ rq ∈ Q, ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) * (1 + R * f rq) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro rq hrq hnot
      have hf := smallDeterminantMass_nonneg L Z k rq.1 rq.2 m' h
      change 0 ≤ f rq at hf
      positivity
    _ = M * Real.log (b1Cutoff N : ℝ) *
        ((∑ rq ∈ Q, (1 : ℝ) / (rq.1 * rq.2 : ℕ)) +
          R * ∑ rq ∈ Q, ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) * f rq) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro rq hrq
      ring
    _ ≤ M * Real.log (b1Cutoff N : ℝ) *
        (A * (4 : ℝ) ^ h.primeFactors.card / (h : ℝ) ^ 2 +
          D * (4 : ℝ) ^ h.primeFactors.card / (h : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add hbase' ((mul_le_mul_of_nonneg_left hcharge' hR).trans hscaled)
    _ = _ := by ring

#print axioms exists_eventually_small_fixedPair_singular_bound

end Erdos822
