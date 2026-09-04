/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.EventPartition

/-!
# The processed congruence-class invariant for Erdős Problem 586

This file proves that the recursively distorted measures of `StageLaw`
satisfy the class-mass hypothesis used by the first- and second-moment
estimates.  The proof is entirely finite.  At a successor stage a divisor
of the new partial period either avoids the new stage prime, in which case
its class depends only on the old CRT coordinate, or it is the product of
an old divisor and a power of the new prime.  In the latter case the
one-step product-class estimate from `CongruenceMass` supplies exactly the
new distortion factor.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Every partial period of a nonzero common period is nonzero.  Registering
this derived fact locally makes the finite `ZMod` instances available
throughout the class-mass induction. -/
local instance classMassPartialPeriodNeZero (Q r : ℕ) :
    NeZero (partialPeriod Q r) :=
  ⟨(partialPeriod_pos Q r).ne'⟩

/-! ## Arithmetic and recurrence helpers -/

/-- Removing the new stage prime from a divisor of the successor period
leaves a divisor of the old period. -/
private lemma oldPart_dvd_partialPeriod_of_dvd_succ
    {Q r m : ℕ} (hm : m ∣ partialPeriod Q (r + 1)) :
    oldPart m (r + 1) ∣ partialPeriod Q r := by
  let p := stagePrime (r + 1)
  let E := stageExponent Q (r + 1)
  have hp : Nat.Prime p := stagePrime_prime (by omega)
  by_cases hE : E = 0
  · have hmold : m ∣ partialPeriod Q r := by
      simpa [partialPeriod_succ, p, E, hE] using hm
    simpa [oldPart, p] using (Nat.ordCompl_dvd m p).trans hmold
  · have hEpos : 0 < E := Nat.pos_of_ne_zero hE
    have hcopPow : Nat.Coprime (partialPeriod Q r) (p ^ E) := by
      simpa [p, E] using partialPeriod_coprime_stagePow Q r
    have hcop : Nat.Coprime (partialPeriod Q r) p :=
      (Nat.coprime_pow_right_iff hEpos _ _).mp hcopPow
    have hpold : ¬ p ∣ partialPeriod Q r :=
      hp.coprime_iff_not_dvd.mp hcop.symm
    have hord := Nat.ordCompl_dvd_ordCompl_of_dvd hm p
    rw [partialPeriod_succ, Nat.ordCompl_mul,
      Nat.ordCompl_self_pow hp,
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hp).mpr (Or.inr hpold),
      mul_one] at hord
    simpa [oldPart, p, E] using hord

/-- If a divisor of the successor period avoids the new stage prime, it
already divides the old period. -/
private lemma dvd_partialPeriod_of_dvd_succ_of_not_stagePrime_dvd
    {Q r m : ℕ} (hm : m ∣ partialPeriod Q (r + 1))
    (hp : ¬ stagePrime (r + 1) ∣ m) :
    m ∣ partialPeriod Q r := by
  have hold := oldPart_dvd_partialPeriod_of_dvd_succ hm
  have heq : oldPart m (r + 1) = m := by
    simpa [oldPart] using
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd m
        (stagePrime_prime (by omega))).mpr (Or.inr hp)
  simpa [heq] using hold

/-- Multiplying a modulus by a power of the next stage prime does not
alter any of the factors contributed by the preceding stages. -/
private lemma processedClassFactor_mul_laterStagePrime_pow
    (delta : ℕ → ℝ) {n : ℕ} (r : ℕ) (hrn : r < n) (g j : ℕ) :
    processedClassFactor stagePrime delta (g * stagePrime n ^ j) r =
      processedClassFactor stagePrime delta g r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hprime : Nat.Prime (stagePrime (r + 1)) :=
        stagePrime_prime (by omega)
      have hnprime : Nat.Prime (stagePrime n) :=
        stagePrime_prime (by omega)
      have hlt : stagePrime (r + 1) < stagePrime n :=
        stagePrime_strictMonoOn (by simp) (by
          simp only [Set.mem_Ici]
          omega) (by omega)
      have hnot : ¬ stagePrime n ∣ stagePrime (r + 1) := by
        rw [Nat.prime_dvd_prime_iff_eq hnprime hprime]
        exact ne_of_gt hlt
      have hcop : Nat.Coprime (stagePrime (r + 1))
          (stagePrime n ^ j) :=
        hnprime.coprime_pow_of_not_dvd hnot
      rw [processedClassFactor_succ, processedClassFactor_succ,
        ih (by omega)]
      simp only [hcop.dvd_mul_right]

/-! ## CRT splitting of an arbitrary newly divisible class -/

/-- A congruence modulo `g * p^j`, with `g` supported on the old period,
is the product of its two congruences in the stage CRT coordinates. -/
private theorem mem_splitClass_stageCRTRingEquiv_iff
    {Q r m g j : ℕ}
    (hm : m ∣ partialPeriod Q (r + 1))
    (hg : g ∣ partialPeriod Q r)
    (hj : j ≤ stageExponent Q (r + 1))
    (hpg : ¬ stagePrime (r + 1) ∣ g)
    (hdecomp : m = g * stagePrime (r + 1) ^ j)
    (b : ℤ) (x : ZMod (partialPeriod Q (r + 1))) :
    ((stageCRTRingEquiv Q r x).1 ∈
          congruenceClass (partialPeriod Q r) g hg b ∧
      (stageCRTRingEquiv Q r x).2 ∈
          congruenceClass
            (stagePrime (r + 1) ^ stageExponent Q (r + 1))
            (stagePrime (r + 1) ^ j) (Nat.pow_dvd_pow _ hj) b) ↔
      x ∈ congruenceClass (partialPeriod Q (r + 1)) m hm b := by
  rw [← ZMod.natCast_zmod_val x]
  simp only [map_natCast, Prod.fst_natCast, Prod.snd_natCast]
  have hOld :
      (x.val : ZMod (partialPeriod Q r)) ∈
          congruenceClass (partialPeriod Q r) g hg b ↔
        (x.val : ℤ) ≡ b [ZMOD g] := by
    simpa using (intCast_mem_congruenceClass hg (x.val : ℤ) b)
  have hNew :
      (x.val : ZMod
          (stagePrime (r + 1) ^ stageExponent Q (r + 1))) ∈
          congruenceClass
            (stagePrime (r + 1) ^ stageExponent Q (r + 1))
            (stagePrime (r + 1) ^ j) (Nat.pow_dvd_pow _ hj) b ↔
        (x.val : ℤ) ≡ b [ZMOD stagePrime (r + 1) ^ j] := by
    simpa using
      (intCast_mem_congruenceClass (Nat.pow_dvd_pow _ hj) (x.val : ℤ) b)
  have hFull :
      (x.val : ZMod (partialPeriod Q (r + 1))) ∈
          congruenceClass (partialPeriod Q (r + 1)) m hm b ↔
        (x.val : ℤ) ≡ b [ZMOD m] := by
    simpa using (intCast_mem_congruenceClass hm (x.val : ℤ) b)
  rw [hOld, hNew, hFull]
  have hcop : Nat.Coprime g (stagePrime (r + 1) ^ j) :=
    (stagePrime_prime (by omega)).coprime_pow_of_not_dvd hpg
  rw [Int.modEq_and_modEq_iff_modEq_mul (by simpa using hcop)]
  have hmod :
      (g : ℤ) * (stagePrime (r + 1) : ℤ) ^ j = (m : ℤ) := by
    exact_mod_cast hdecomp.symm
  rw [hmod]

/-! ## The invariant for the actual recursive law -/

/-- At every zero-indexed stage, every positive divisor class of the
current partial period has the BBMST processed-prime mass bound.  This is
the stronger induction statement underlying
`stageDistribution_hasProcessedClassMassBound`. -/
theorem stageDistribution_classMass_le
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) :
    ∀ (r m : ℕ) (hm : m ∣ partialPeriod Q r) (hm0 : 0 < m) (b : ℤ),
      (stageDistribution A s Q hQ r).mass
          (congruenceClass (partialPeriod Q r) m hm b) ≤
        (1 / (m : ℝ)) *
          processedClassFactor stagePrime distortionDelta m r := by
  intro r
  induction r with
  | zero =>
      intro m hm hm0 b
      have hm1 : m = 1 := by
        simpa using hm
      subst m
      simpa using
        (stageDistribution A s Q hQ 0).mass_le_one
          (congruenceClass (partialPeriod Q 0) 1 hm b)
  | succ r ih =>
      intro m hm hm0 b
      let q := partialPeriod Q r
      let p := stagePrime (r + 1)
      let E := stageExponent Q (r + 1)
      let P := p ^ E
      let : NeZero q :=
        ⟨partialPeriod_ne_zero_of_Q_ne_zero Q r hQ⟩
      let : NeZero P := ⟨by
        exact (pow_pos (stagePrime_pos (by omega)) _).ne'⟩
      by_cases hpm : p ∣ m
      · have hmQ : m ∣ Q :=
          hm.trans (partialPeriod_dvd Q (r + 1) hQ)
        have hmne : m ≠ 0 := hm0.ne'
        have hnew : IsNewModulus Q (r + 1) m := by
          refine ⟨by omega, hmQ, ?_, oldPart_dvd_partialPeriod_of_dvd_succ hm⟩
          exact (stagePrime_prime (by omega)).factorization_pos_of_dvd hmne hpm
        obtain ⟨g, j, hgq, hj0, hjE, hpg, hdecomp⟩ :=
          newModulus_exists_oldPart_pow hQ hnew
        have hg0 : 0 < g :=
          Nat.pos_of_dvd_of_pos hgq (NeZero.pos q)
        have he0 : 0 < stagePrime (r + 1) ^ j :=
          pow_pos (stagePrime_pos (by omega)) _
        have hfactor :
            processedClassFactor stagePrime distortionDelta g r =
              processedClassFactor stagePrime distortionDelta m r := by
          rw [hdecomp,
            processedClassFactor_mul_laterStagePrime_pow distortionDelta r
              (by omega)]
        have hden : 0 < 1 - distortionDelta (r + 1) := by
          have := distortionDelta_le_half (r + 1)
          linarith
        have hstep :
            (stageDistribution A s Q hQ (r + 1)).mass
                (congruenceClass (partialPeriod Q (r + 1)) m hm b) ≤
              (stageDistribution A s Q hQ r).mass
                  (congruenceClass (partialPeriod Q r) g hgq b) /
                (stagePrime (r + 1) ^ j : ℕ) /
                  (1 - distortionDelta (r + 1)) := by
          change
            ((distort (stageDistribution A s Q hQ r)
              (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
              (distortionDelta_nonneg (r + 1))
              (distortionDelta_le_half (r + 1))).mapEquiv
                (stageCRTRingEquiv Q r).toEquiv.symm).mass _ ≤ _
          rw [FiniteProbability.mapEquiv_mass]
          change finiteWeightMass
              (distortWeight (stageDistribution A s Q hQ r)
                (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))) _ ≤ _
          have hset :
              (stageCRTRingEquiv Q r).toEquiv.symm ⁻¹'
                  congruenceClass (partialPeriod Q (r + 1)) m hm b =
                {z : ZMod q × ZMod P |
                  z.1 ∈ congruenceClass q g hgq b ∧
                    z.2 ∈ congruenceClass P
                      (stagePrime (r + 1) ^ j)
                        (Nat.pow_dvd_pow _ hjE) b} := by
            ext z
            simpa [q, p, E, P] using
              (mem_splitClass_stageCRTRingEquiv_iff hm hgq hjE hpg
                hdecomp b ((stageCRTRingEquiv Q r).symm z)).symm
          rw [hset]
          exact finiteWeightMass_distort_product_congruenceClass_le
            hgq (Nat.pow_dvd_pow _ hjE) he0
              (stageDistribution A s Q hQ r)
              (stageBadEvent A s Q r hQ)
              (distortionDelta_nonneg (r + 1))
              (distortionDelta_le_half (r + 1)) b b
        calc
          (stageDistribution A s Q hQ (r + 1)).mass
              (congruenceClass (partialPeriod Q (r + 1)) m hm b) ≤
              (stageDistribution A s Q hQ r).mass
                  (congruenceClass (partialPeriod Q r) g hgq b) /
                (stagePrime (r + 1) ^ j : ℕ) /
                  (1 - distortionDelta (r + 1)) := hstep
          _ ≤ (((1 / (g : ℝ)) *
                  processedClassFactor stagePrime distortionDelta g r) /
                (stagePrime (r + 1) ^ j : ℕ)) /
                  (1 - distortionDelta (r + 1)) := by
            exact div_le_div_of_nonneg_right
              (div_le_div_of_nonneg_right (ih g hgq hg0 b)
                (Nat.cast_nonneg _)) hden.le
          _ = (1 / (m : ℝ)) *
                processedClassFactor stagePrime distortionDelta m (r + 1) := by
            rw [processedClassFactor_succ, if_pos hpm, ← hfactor, hdecomp]
            push_cast
            field_simp [ne_of_gt hg0, ne_of_gt he0, ne_of_gt hden]
      · have hmold : m ∣ partialPeriod Q r :=
          dvd_partialPeriod_of_dvd_succ_of_not_stagePrime_dvd hm hpm
        have hclass :
            congruenceClass (partialPeriod Q (r + 1)) m hm b =
              {x | (stageCRTRingEquiv Q r x).1 ∈
                congruenceClass (partialPeriod Q r) m hmold b} := by
          ext x
          exact (mem_oldClass_stageCRTRingEquiv_iff hmold b x).symm
        calc
          (stageDistribution A s Q hQ (r + 1)).mass
              (congruenceClass (partialPeriod Q (r + 1)) m hm b) =
              (stageDistribution A s Q hQ r).mass
                (congruenceClass (partialPeriod Q r) m hmold b) := by
            rw [hclass]
            exact stageDistribution_oldEvent_invariant A s Q r hQ _
          _ ≤ (1 / (m : ℝ)) *
              processedClassFactor stagePrime distortionDelta m r :=
            ih m hmold hm0 b
          _ = (1 / (m : ℝ)) *
              processedClassFactor stagePrime distortionDelta m (r + 1) := by
            simp [processedClassFactor, p, hpm]

/-- The actual recursively distorted law supplies the processed-class
mass hypothesis required by `StageAssembly` at every positive stage.
There are no analytic assumptions: the result uses only the finite CRT
recursion and the fixed distortion parameters. -/
theorem stageDistribution_hasProcessedClassMassBound
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) :
    HasProcessedClassMassBound (Q := Q) (r := r + 1)
      (stageDistribution A s Q hQ r) distortionDelta := by
  intro m hm hm0 b
  simpa using stageDistribution_classMass_le A s Q hQ r m hm hm0 b

end

end Erdos586
