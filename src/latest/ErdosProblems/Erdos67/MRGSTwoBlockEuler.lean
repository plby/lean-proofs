import ErdosProblems.Erdos67.MRGSTwoBlockDeletion
import ErdosProblems.Erdos67.MRGSTwistedEuler
import ErdosProblems.Erdos67.MRHalaszBandLocalMass

/-!
# Local GS Euler exponent after deleting a prime block

This is the quantitative Euler-exponent calculation used in the proof of
source equation (A.8).  Deleted primes contribute their reciprocal mass;
the remaining primes are controlled by Cauchy--Schwarz using only the
remaining reciprocal mass and the original pretentious distance.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67.MRHalaszBands

noncomputable section

/-- A prime block and its complement partition the full reciprocal-prime
mass.  This is the exact finite identity used when the source `7/8` exponent
is converted to the usual prime harmonic sum. -/
theorem primeBandReciprocalMass_add_compl
    (Q : ℕ → Prop) [DecidablePred Q] (N : ℕ) :
    primeBandReciprocalMass Q N +
        primeBandReciprocalMass (fun p ↦ ¬ Q p) N =
      PrimeEstimates.primeReciprocals N := by
  unfold primeBandReciprocalMass
  change (∑ p ∈ primesUpTo N with Q p, 1 / (p : ℝ)) +
      (∑ p ∈ primesUpTo N with ¬ Q p, 1 / (p : ℝ)) = _
  have hsets : primesUpTo N = Nat.primesLE N := by
    ext p
    simp [Nat.mem_primesLE, mem_primesUpTo, and_comm]
  calc
    (∑ p ∈ primesUpTo N with Q p, 1 / (p : ℝ)) +
        (∑ p ∈ primesUpTo N with ¬ Q p, 1 / (p : ℝ)) =
      ∑ p ∈ primesUpTo N, 1 / (p : ℝ) :=
        Finset.sum_filter_add_sum_filter_not _ _ _
    _ = PrimeEstimates.primeReciprocals N := by
      rw [hsets]
      simp [PrimeEstimates.primeReciprocals,
        Erdos784.Analytic.primeReciprocals, one_div]

theorem sq_sum_norm_archimedeanUntwist_sub_one_div_filter_le
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    (t : ℝ) (N : ℕ) :
    (∑ p ∈ primesUpTo N with ¬ Q p,
        ‖archimedeanUntwist f t p - 1‖ / (p : ℝ)) ^ 2 ≤
      2 * pretentiousDistSq f (archimedeanTwist t) N *
        primeBandReciprocalMass (fun p ↦ ¬ Q p) N := by
  let S : Finset ℕ := (primesUpTo N).filter (fun p ↦ ¬ Q p)
  let r : ℕ → ℝ := fun p ↦ ‖archimedeanUntwist f t p - 1‖ / (p : ℝ)
  let a : ℕ → ℝ := fun p ↦ ‖archimedeanUntwist f t p - 1‖ ^ 2 / (p : ℝ)
  let b : ℕ → ℝ := fun p ↦ 1 / (p : ℝ)
  have hpPos (p : ℕ) (hp : p ∈ S) : (0 : ℝ) < p := by
    exact_mod_cast (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1.pos
  have hcs :
      (∑ p ∈ S, r p) ^ 2 ≤
        (∑ p ∈ S, a p) * ∑ p ∈ S, b p := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro p hp
      exact div_nonneg (sq_nonneg _) (hpPos p hp).le
    · intro p hp
      exact div_nonneg zero_le_one (hpPos p hp).le
    · intro p hp
      dsimp [r, a, b]
      field_simp [ne_of_gt (hpPos p hp)]
      simp [sub_eq_add_neg]
  have ha : (∑ p ∈ S, a p) ≤
      2 * pretentiousDistSq f (archimedeanTwist t) N := by
    calc
      (∑ p ∈ S, a p) ≤
          ∑ p ∈ S, 2 * pretentiousTerm f (archimedeanTwist t) p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
        dsimp [a, pretentiousTerm]
        have hpoint := norm_archimedeanUntwist_sub_one_sq_le
          hbound hpprime t
        calc
          ‖archimedeanUntwist f t p - 1‖ ^ 2 / (p : ℝ) ≤
              (2 * (1 - (f p * conj (archimedeanTwist t p)).re)) /
                (p : ℝ) :=
            div_le_div_of_nonneg_right hpoint (Nat.cast_nonneg p)
          _ = 2 * ((1 - (f p * conj (archimedeanTwist t p)).re) /
                (p : ℝ)) := by ring
      _ ≤ ∑ p ∈ primesUpTo N,
          2 * pretentiousTerm f (archimedeanTwist t) p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp _
        have hpprime := (mem_primesUpTo.mp hp).1
        exact mul_nonneg (by norm_num)
          (pretentiousTerm_nonneg (hbound p)
            (norm_archimedeanTwist hpprime.pos t).le)
      _ = 2 * pretentiousDistSq f (archimedeanTwist t) N := by
        unfold pretentiousDistSq
        rw [Finset.mul_sum]
  have hb : (∑ p ∈ S, b p) =
      primeBandReciprocalMass (fun p ↦ ¬ Q p) N := by
    rfl
  have hdist0 : 0 ≤ pretentiousDistSq f (archimedeanTwist t) N := by
    exact pretentiousDistSq_nonneg
      (fun p _hp ↦ hbound p)
      (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
  have hmass0 : 0 ≤ primeBandReciprocalMass (fun p ↦ ¬ Q p) N := by
    unfold primeBandReciprocalMass
    positivity
  change (∑ p ∈ S, r p) ^ 2 ≤ _
  rw [hb] at hcs
  exact hcs.trans (mul_le_mul ha le_rfl hmass0 (by positivity))

theorem gsEulerExponent_archimedeanUntwist_deletePrimeBand_le
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    (t : ℝ) (N : ℕ) :
    gsEulerExponent (archimedeanUntwist (gsDeletePrimeBand f Q) t) N ≤
      primeBandReciprocalMass Q N +
        Real.sqrt
          (2 * pretentiousDistSq f (archimedeanTwist t) N *
            primeBandReciprocalMass (fun p ↦ ¬ Q p) N) + 8 := by
  have hsets : (N + 1).primesBelow = primesUpTo N := by
    ext p
    simp [Nat.mem_primesBelow, mem_primesUpTo, and_comm]
  have hlinear :
      (∑ p ∈ primesUpTo N,
          ‖archimedeanUntwist (gsDeletePrimeBand f Q) t p - 1‖ /
            (p : ℝ)) =
        primeBandReciprocalMass Q N +
          ∑ p ∈ primesUpTo N with ¬ Q p,
            ‖archimedeanUntwist f t p - 1‖ / (p : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (primesUpTo N) Q
      (fun p ↦ ‖archimedeanUntwist (gsDeletePrimeBand f Q) t p - 1‖ /
        (p : ℝ))]
    unfold primeBandReciprocalMass
    congr 1
    · apply Finset.sum_congr rfl
      intro p hp
      have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
      have hpQ := (Finset.mem_filter.mp hp).2
      have hhas : HasPrimeFactor Q p := by
        rw [hasPrimeFactor_iff, hpprime.primeFactors]
        exact ⟨p, by simp, hpQ⟩
      rw [archimedeanUntwist, if_neg hpprime.ne_zero,
        gsDeletePrimeBand_apply f Q hpprime.pos, if_pos hhas]
      simp
    · apply Finset.sum_congr rfl
      intro p hp
      have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
      have hpQ := (Finset.mem_filter.mp hp).2
      have hhas : ¬ HasPrimeFactor Q p := by
        rw [hasPrimeFactor_iff, hpprime.primeFactors]
        simpa using hpQ
      rw [archimedeanUntwist, if_neg hpprime.ne_zero,
        gsDeletePrimeBand_apply f Q hpprime.pos, if_neg hhas,
        archimedeanUntwist, if_neg hpprime.ne_zero]
  have hsquare := sq_sum_norm_archimedeanUntwist_sub_one_div_filter_le
    hbound Q t N
  have hsum0 : 0 ≤ ∑ p ∈ primesUpTo N with ¬ Q p,
      ‖archimedeanUntwist f t p - 1‖ / (p : ℝ) := by positivity
  have hdist0 : 0 ≤ pretentiousDistSq f (archimedeanTwist t) N := by
    exact pretentiousDistSq_nonneg
      (fun p _hp ↦ hbound p)
      (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
  have hmass0 : 0 ≤ primeBandReciprocalMass (fun p ↦ ¬ Q p) N := by
    unfold primeBandReciprocalMass
    positivity
  have hsqrt :
      (∑ p ∈ primesUpTo N with ¬ Q p,
          ‖archimedeanUntwist f t p - 1‖ / (p : ℝ)) ≤
        Real.sqrt
          (2 * pretentiousDistSq f (archimedeanTwist t) N *
            primeBandReciprocalMass (fun p ↦ ¬ Q p) N) := by
    exact (Real.le_sqrt hsum0
      (mul_nonneg (mul_nonneg (by positivity) hdist0) hmass0)).2 hsquare
  unfold gsEulerExponent
  rw [Finset.sum_add_distrib, hsets, hlinear]
  have htail : (∑ p ∈ primesUpTo N,
      2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 8 := by
    simpa only [hsets] using sum_primePowerTail_le_eight N
  exact add_le_add (add_le_add le_rfl hsqrt) htail

/-- The elementary scalar maximization in the source proof of (A.8).  If
the deleted mass is at most half of the total mass and the distance is at
most one eighth of the total mass, the linear GS exponent is at most seven
eighths of the total mass. -/
theorem deletedMass_add_sqrt_le_seven_eighths
    {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hBhalf : B ≤ (B + C) / 2)
    (hDeighth : D ≤ (B + C) / 8) :
    B + Real.sqrt (2 * D * C) ≤ (7 / 8 : ℝ) * (B + C) := by
  let P : ℝ := B + C
  have hP : 0 ≤ P := add_nonneg hB hC
  have harg : 0 ≤ 2 * D * C := mul_nonneg (mul_nonneg (by norm_num) hD) hC
  have harg_le : 2 * D * C ≤ P * C / 4 := by
    dsimp [P] at hDeighth ⊢
    nlinarith
  have hrhs : 0 ≤ (7 / 8 : ℝ) * P - B := by
    dsimp [P] at hBhalf ⊢
    nlinarith
  have hsquare : P * C / 4 ≤ ((7 / 8 : ℝ) * P - B) ^ 2 := by
    dsimp [P] at hBhalf ⊢
    nlinarith [sq_nonneg (B - C)]
  have hsqrt : Real.sqrt (2 * D * C) ≤ (7 / 8 : ℝ) * P - B := by
    exact Real.sqrt_le_iff.mpr ⟨hrhs, harg_le.trans hsquare⟩
  dsimp [P] at hsqrt ⊢
  linarith

/-- Source `7/8 log log` form of the deleted-coefficient GS exponent.  The
total reciprocal mass is kept as the exact sum of the deleted and retained
prime masses, so no prime-number asymptotic is needed in this theorem. -/
theorem gsEulerExponent_archimedeanUntwist_deletePrimeBand_le_seven_eighths
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    (t : ℝ) (N : ℕ)
    (hBhalf : primeBandReciprocalMass Q N ≤
      (primeBandReciprocalMass Q N +
        primeBandReciprocalMass (fun p ↦ ¬ Q p) N) / 2)
    (hDeighth : pretentiousDistSq f (archimedeanTwist t) N ≤
      (primeBandReciprocalMass Q N +
        primeBandReciprocalMass (fun p ↦ ¬ Q p) N) / 8) :
    gsEulerExponent (archimedeanUntwist (gsDeletePrimeBand f Q) t) N ≤
      (7 / 8 : ℝ) *
        (primeBandReciprocalMass Q N +
          primeBandReciprocalMass (fun p ↦ ¬ Q p) N) + 8 := by
  have hbase := gsEulerExponent_archimedeanUntwist_deletePrimeBand_le
    hbound Q t N
  have hB : 0 ≤ primeBandReciprocalMass Q N := by
    unfold primeBandReciprocalMass
    positivity
  have hC : 0 ≤ primeBandReciprocalMass (fun p ↦ ¬ Q p) N := by
    unfold primeBandReciprocalMass
    positivity
  have hD : 0 ≤ pretentiousDistSq f (archimedeanTwist t) N := by
    exact pretentiousDistSq_nonneg
      (fun p _hp ↦ hbound p)
      (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
  have hscalar := deletedMass_add_sqrt_le_seven_eighths
    hB hC hD hBhalf hDeighth
  linarith

/-- The same `7/8` estimate rewritten with the repository's canonical full
reciprocal-prime mass. -/
theorem gsEulerExponent_archimedeanUntwist_deletePrimeBand_le_primeReciprocals
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    (t : ℝ) (N : ℕ)
    (hBhalf : primeBandReciprocalMass Q N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hDeighth : pretentiousDistSq f (archimedeanTwist t) N ≤
      PrimeEstimates.primeReciprocals N / 8) :
    gsEulerExponent (archimedeanUntwist (gsDeletePrimeBand f Q) t) N ≤
      (7 / 8 : ℝ) * PrimeEstimates.primeReciprocals N + 8 := by
  have hmass := primeBandReciprocalMass_add_compl Q N
  have h := gsEulerExponent_archimedeanUntwist_deletePrimeBand_le_seven_eighths
    hbound Q t N
    (by simpa only [hmass] using hBhalf)
    (by simpa only [hmass] using hDeighth)
  simpa only [hmass] using h

end

end Erdos67.MRHalaszBands
