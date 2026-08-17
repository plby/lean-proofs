/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.Certificate
import ErdosProblems.Erdos586.PrimeStages
import ErdosProblems.Erdos586.Tail

/-!
# Connecting the checked recurrence to the analytic tail

This file contains the small but essential compatibility layer between the
three independently checked parts of the proof:

* the prime stages attached to a finite covering system;
* the fixed-`1/5` recurrence and its finite certificate through stage 10000;
* the elementary analytic estimate which controls every later stage.

In particular, the theorems below expose no prime-estimate or convergence
hypothesis.  Those facts are discharged once and for all by `Tail.tail_budget`.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

/-! ## Compatibility of the prime and recurrence conventions -/

/-- The stage-prime sequence and the analytic-tail prime sequence use the
same one-based convention. -/
@[simp] lemma stagePrime_eq_primeAt (r : ℕ) :
    stagePrime r = Tail.primeAt r := by
  rfl

@[simp] lemma tail_qAt_eq_stagePrime (r : ℕ) :
    Tail.qAt r = (stagePrime r : ℝ) - 1 := by
  rfl

/-- At distortion parameter `1/5`, the sieve Euler factor is exactly the
numerator factor used by the tail calculation. -/
lemma sieveFactor_one_fifth_eq_tailN (r : ℕ) :
    sieveFactor (stagePrime r) (1 / 5) = Tail.tailN r := by
  have hq : (Tail.primeAt r : ℝ) - 1 ≠ 0 := by
    have hp : 1 < Tail.primeAt r := by
      unfold Tail.primeAt
      exact (Nat.prime_nth_prime (r - 1)).one_lt
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  rw [stagePrime_eq_primeAt]
  unfold sieveFactor stageA Tail.tailN Tail.numeratorFactor Tail.qAt
  norm_num
  field_simp [hq]
  ring

/-- At distortion parameter `1/5`, the sieve loss coefficient is exactly
the denominator coefficient used by the tail calculation. -/
lemma lossRatio_one_fifth_eq_tailC_mul (r : ℕ) (x : ℝ) :
    lossRatio (stagePrime r) (1 / 5) x = Tail.tailC r * x := by
  have hq : (Tail.primeAt r : ℝ) - 1 ≠ 0 := by
    have hp : 1 < Tail.primeAt r := by
      unfold Tail.primeAt
      exact (Nat.prime_nth_prime (r - 1)).one_lt
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  rw [stagePrime_eq_primeAt]
  unfold lossRatio stageB Tail.tailC Tail.denominatorCoeff Tail.qAt
  norm_num
  field_simp [hq]
  ring

/-- Exact identification of a stage update with the fixed-shape analytic
tail recurrence. -/
lemma recurrenceMap_one_fifth_eq_tail (r : ℕ) (x : ℝ) :
    recurrenceMap (stagePrime r) (1 / 5) x =
      x * Tail.tailN r / (1 - Tail.tailC r * x) := by
  rw [recurrenceMap, sieveFactor_one_fifth_eq_tailN,
    lossRatio_one_fifth_eq_tailC_mul]

lemma certificate_fixedRecurrence_eq_tail (r : ℕ) (x : ℝ) :
    Certificate.fixedRecurrence (stagePrime r) x =
      x * Tail.tailN r / (1 - Tail.tailC r * x) := by
  rw [Certificate.fixedRecurrence, recurrenceMap_one_fifth_eq_tail]

/-! ## Survival throughout the analytic tail -/

/-- Once the stage-10000 value is below `13000`, the checked analytic budget
simultaneously gives every later denominator and the explicit reciprocal
envelope.  The only input about the concrete sieve is its conditional
one-step recurrence inequality; all analytic estimates have already been
proved in `Tail.tail_budget`. -/
theorem tail_survival
    (f : ℕ → ℝ) (n : ℕ)
    (hf_nonneg : ∀ j ≤ n, 0 ≤ f (10000 + j))
    (hf10000 : f 10000 < 13000)
    (hrec : ∀ j < n,
      0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) →
        f (10000 + j + 1) ≤
          f (10000 + j) * Tail.tailN (10000 + j + 1) /
            (1 - Tail.tailC (10000 + j + 1) * f (10000 + j))) :
    (∀ j < n,
        0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j)) ∧
      f (10000 + n) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000 n /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 n) := by
  exact Tail.survival_after_ten_thousand
    (hf_nonneg 0 (by omega)) hf10000.le hf_nonneg hrec

/-- Positivity of the next tail denominator follows from the envelope at the
current stage and the already checked budget one stage farther. -/
private lemma tail_next_denominator_pos
    {f : ℕ → ℝ} {j : ℕ}
    (henvelope : f (10000 + j) ≤
      13000 * Tail.prefixProduct Tail.tailN 10000 j /
        (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 j)) :
    0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) := by
  have hD : 0 < 1 - (13000 : ℝ) *
      Tail.prefixCost Tail.tailN Tail.tailC 10000 j := by
    linarith [Tail.tail_budget j]
  have hbnext := Tail.tail_budget (j + 1)
  have hcB : Tail.tailC (10000 + j + 1) *
      (13000 * Tail.prefixProduct Tail.tailN 10000 j /
        (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 j)) < 1 := by
    calc
      Tail.tailC (10000 + j + 1) *
          (13000 * Tail.prefixProduct Tail.tailN 10000 j /
            (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 j)) =
        (Tail.tailC (10000 + j + 1) * 13000 *
          Tail.prefixProduct Tail.tailN 10000 j) /
            (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 j) := by
              ring
      _ < 1 := (div_lt_iff₀ hD).2 (by
        rw [Tail.prefixCost] at hbnext
        nlinarith)
  have hcf : Tail.tailC (10000 + j + 1) * f (10000 + j) < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left henvelope (Tail.tailC_nonneg (by omega))) hcB
  linarith

/-- Joint survival induction.  Unlike `tail_survival`, this theorem does not
assume nonnegativity of future normalized values.  A concrete sieve step may
produce that nonnegativity only after denominator validity has been proved;
the induction propagates those two facts together, avoiding circularity. -/
theorem tail_survival_joint
    (f : ℕ → ℝ) (n : ℕ)
    (hf10000_nonneg : 0 ≤ f 10000)
    (hf10000 : f 10000 < 13000)
    (hstep : ∀ j < n,
      0 ≤ f (10000 + j) →
      0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) →
        0 ≤ f (10000 + j + 1) ∧
          f (10000 + j + 1) ≤
            f (10000 + j) * Tail.tailN (10000 + j + 1) /
              (1 - Tail.tailC (10000 + j + 1) * f (10000 + j))) :
    (∀ j ≤ n, 0 ≤ f (10000 + j)) ∧
      (∀ j < n,
        0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j)) ∧
      f (10000 + n) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000 n /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 n) := by
  induction n with
  | zero =>
      constructor
      · intro j hj
        have : j = 0 := by omega
        subst j
        simpa using hf10000_nonneg
      · constructor
        · intro j hj
          omega
        · simpa [Tail.prefixProduct, Tail.prefixCost] using hf10000.le
  | succ n ih =>
      have hprev := ih (fun j hj => hstep j (by omega))
      have hvalid :
          0 < 1 - Tail.tailC (10000 + n + 1) * f (10000 + n) :=
        tail_next_denominator_pos hprev.2.2
      have hnext := hstep n (by omega) (hprev.1 n le_rfl) hvalid
      have hnonneg : ∀ j ≤ n + 1, 0 ≤ f (10000 + j) := by
        intro j hj
        by_cases hle : j ≤ n
        · exact hprev.1 j hle
        · have : j = n + 1 := by omega
          subst j
          exact hnext.1
      have hrec : ∀ j < n + 1,
          0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) →
            f (10000 + j + 1) ≤
              f (10000 + j) * Tail.tailN (10000 + j + 1) /
                (1 - Tail.tailC (10000 + j + 1) * f (10000 + j)) := by
        intro j hj hv
        exact (hstep j hj (hnonneg j hj.le) hv).2
      exact ⟨hnonneg, Tail.survival_after_ten_thousand
        hf10000_nonneg hf10000.le hnonneg hrec⟩

/-- Version of `tail_survival` expressed directly with the fixed-`1/5`
sieve recurrence at `stagePrime`. -/
theorem tail_survival_of_sieve_recurrence
    (f : ℕ → ℝ) (n : ℕ)
    (hf_nonneg : ∀ j ≤ n, 0 ≤ f (10000 + j))
    (hf10000 : f 10000 < 13000)
    (hrec : ∀ j < n,
      0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) →
        f (10000 + j + 1) ≤
          recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
            (f (10000 + j))) :
    (∀ j < n,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (10000 + n) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000 n /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 n) := by
  have htail := tail_survival f n hf_nonneg hf10000 (fun j hj hvalid => by
    rw [← recurrenceMap_one_fifth_eq_tail]
    exact hrec j hj hvalid)
  refine ⟨?_, htail.2⟩
  intro j hj
  rw [lossRatio_one_fifth_eq_tailC_mul]
  linarith [htail.1 j hj]

/-- Joint survival in the native sieve notation.  The step premise may use
denominator validity to establish both nonnegativity and the recurrence bound
for the next normalized value. -/
theorem tail_survival_joint_of_sieve_recurrence
    (f : ℕ → ℝ) (n : ℕ)
    (hf10000_nonneg : 0 ≤ f 10000)
    (hf10000 : f 10000 < 13000)
    (hstep : ∀ j < n,
      0 ≤ f (10000 + j) →
      lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1 →
        0 ≤ f (10000 + j + 1) ∧
          f (10000 + j + 1) ≤
            recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
              (f (10000 + j))) :
    (∀ j ≤ n, 0 ≤ f (10000 + j)) ∧
      (∀ j < n,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (10000 + n) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000 n /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 n) := by
  have htail := tail_survival_joint f n hf10000_nonneg hf10000
    (fun j hj hfcur hvalid => by
      have hsieve : lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1 := by
        rw [lossRatio_one_fifth_eq_tailC_mul]
        linarith
      have h := hstep j hj hfcur hsieve
      refine ⟨h.1, ?_⟩
      rw [← recurrenceMap_one_fifth_eq_tail]
      exact h.2)
  refine ⟨htail.1, ?_, htail.2.2⟩
  intro j hj
  rw [lossRatio_one_fifth_eq_tailC_mul]
  linarith [htail.2.1 j hj]

/-! ## From the finite certificate to a finite stage horizon -/

/-- Consecutive stage recurrence inequalities assemble into the list-shaped
chain consumed by the kernel-checked certificate.  Keeping this elementary
list induction here isolates the certificate computation from the later
stage-indexed sieve. -/
lemma recurrenceChain_stageRange
    (f : ℕ → ℝ) (k n : ℕ)
    (hstep : ∀ r, k < r → r ≤ k + n →
      0 ≤ f r ∧
        f r ≤ Certificate.fixedRecurrence (stagePrime r) (f (r - 1))) :
    Certificate.RecurrenceChain
      ((List.range' (k + 1) n).map stagePrime) (f k) (f (k + n)) := by
  induction n generalizing k with
  | zero =>
      simpa using Certificate.RecurrenceChain.nil (f k)
  | succ n ih =>
      rw [List.range'_succ, List.map_cons]
      have hone := hstep (k + 1) (by omega) (by omega)
      apply Certificate.RecurrenceChain.cons hone.1
      · simpa using hone.2
      · have htail := ih (k := k + 1) (fun r hkr hr => by
          apply hstep r <;> omega)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htail

/-- Nonnegativity stored at each certificate update reaches the endpoint of
the chain. -/
lemma recurrenceChain_end_nonneg
    {ps : List ℕ} {x z : ℝ}
    (hchain : Certificate.RecurrenceChain ps x z) (hx : 0 ≤ x) :
    0 ≤ z := by
  revert hx
  induction hchain with
  | nil =>
      intro hx
      exact hx
  | cons hy0 hy tail ih =>
      intro hx
      exact ih hy0

/-- The exact order theorem for the generated prime certificate turns
stage-indexed updates `4,\ldots,10000` into the certificate's list-shaped
recurrence chain. -/
theorem certificateRecurrenceChain_of_stageSteps
    (f : ℕ → ℝ)
    (hstep : ∀ r, 4 ≤ r → r ≤ 10000 →
      0 ≤ f r ∧
        f r ≤ Certificate.fixedRecurrence (stagePrime r) (f (r - 1))) :
    Certificate.RecurrenceChain
      Certificate.certificatePrimes (f 3) (f 10000) := by
  rw [Certificate.certificatePrimes_eq_stageRange]
  have hchain := recurrenceChain_stageRange f 3 9997 (fun r hrlo hrhi => by
    exact hstep r (by omega) (by omega))
  simpa using hchain

/-- The checked recurrence certificate and the analytic tail together keep
the normalized sequence valid through any requested finite number of stages.
The certificate chain is stated separately so that the concrete stage law can
construct it from the exact list identity for `Certificate.certificatePrimes`.
-/
theorem certificate_and_tail_survival
    (f : ℕ → ℝ) (n : ℕ)
    (hf_nonneg : ∀ r, 0 ≤ f r)
    (hf3 : f 3 ≤ 51 / 20)
    (hcertificate : Certificate.RecurrenceChain
      Certificate.certificatePrimes (f 3) (f 10000))
    (hrec : ∀ j < n,
      0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) →
        f (10000 + j + 1) ≤
          recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
            (f (10000 + j))) :
    (∀ j < n,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (10000 + n) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000 n /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 n) := by
  have hf10000 : f 10000 < 13000 :=
    Certificate.recurrenceChain_certificate_lt_of_le
      (hf_nonneg 3) hf3 hcertificate
  exact tail_survival_of_sieve_recurrence f n
    (fun j hj => hf_nonneg _) hf10000 hrec

/-- Certificate-plus-tail continuation with nonnegativity propagated jointly
with denominator validity.  This is the non-circular form needed when the
normalized quantity is only known to be nonnegative after the remaining mass
at its stage has been proved positive. -/
theorem certificate_and_tail_survival_joint
    (f : ℕ → ℝ) (n : ℕ)
    (hf3_nonneg : 0 ≤ f 3)
    (hf3 : f 3 ≤ 51 / 20)
    (hcertificate : Certificate.RecurrenceChain
      Certificate.certificatePrimes (f 3) (f 10000))
    (hstep : ∀ j < n,
      0 ≤ f (10000 + j) →
      lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1 →
        0 ≤ f (10000 + j + 1) ∧
          f (10000 + j + 1) ≤
            recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
              (f (10000 + j))) :
    (∀ j ≤ n, 0 ≤ f (10000 + j)) ∧
      (∀ j < n,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (10000 + n) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000 n /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000 n) := by
  have hf10000_nonneg : 0 ≤ f 10000 :=
    recurrenceChain_end_nonneg hcertificate hf3_nonneg
  have hf10000 : f 10000 < 13000 :=
    Certificate.recurrenceChain_certificate_lt_of_le
      hf3_nonneg hf3 hcertificate
  exact tail_survival_joint_of_sieve_recurrence f n
    hf10000_nonneg hf10000 hstep

/-- Specialization of the previous theorem to the finite stage horizon of a
covering system's common period. -/
theorem certificate_and_tail_survival_to_horizon
    (Q : ℕ) (f : ℕ → ℝ)
    (hf_nonneg : ∀ r, 0 ≤ f r)
    (hf3 : f 3 ≤ 51 / 20)
    (hcertificate : Certificate.RecurrenceChain
      Certificate.certificatePrimes (f 3) (f 10000))
    (hrec : ∀ j < stageHorizon Q - 10000,
      0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) →
        f (10000 + j + 1) ≤
          recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
            (f (10000 + j))) :
    (∀ j < stageHorizon Q - 10000,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (stageHorizon Q) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000
            (stageHorizon Q - 10000) /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000
            (stageHorizon Q - 10000)) := by
  have h := certificate_and_tail_survival f (stageHorizon Q - 10000)
    hf_nonneg hf3 hcertificate hrec
  have hhor : 10000 + (stageHorizon Q - 10000) = stageHorizon Q := by
    simp [stageHorizon]
  simpa [hhor] using h

/-- Fully stage-indexed form of the certificate-plus-tail bridge.  This is
the interface used by the concrete sieve: the finite recurrence is supplied
for stages `4` through `10000`, while the conditional tail recurrence is
supplied only up to the finite common-period horizon. -/
theorem stage_recurrence_survival_to_horizon
    (Q : ℕ) (f : ℕ → ℝ)
    (hf_nonneg : ∀ r, 0 ≤ f r)
    (hf3 : f 3 ≤ 51 / 20)
    (hfinite : ∀ r, 4 ≤ r → r ≤ 10000 →
      f r ≤ recurrenceMap (stagePrime r) (1 / 5) (f (r - 1)))
    (htail : ∀ j < stageHorizon Q - 10000,
      0 < 1 - Tail.tailC (10000 + j + 1) * f (10000 + j) →
        f (10000 + j + 1) ≤
          recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
            (f (10000 + j))) :
    (∀ j < stageHorizon Q - 10000,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (stageHorizon Q) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000
            (stageHorizon Q - 10000) /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000
            (stageHorizon Q - 10000)) := by
  apply certificate_and_tail_survival_to_horizon Q f hf_nonneg hf3
  · apply certificateRecurrenceChain_of_stageSteps f
    intro r hrlo hrhi
    refine ⟨hf_nonneg r, ?_⟩
    simpa [Certificate.fixedRecurrence] using hfinite r hrlo hrhi
  · exact htail

/-- Joint-propagation version of `stage_recurrence_survival_to_horizon`.
Neither global nonnegativity nor advance knowledge of all tail denominators is
assumed. -/
theorem stage_recurrence_survival_joint_to_horizon
    (Q : ℕ) (f : ℕ → ℝ)
    (hf3_nonneg : 0 ≤ f 3)
    (hf3 : f 3 ≤ 51 / 20)
    (hfinite : ∀ r, 4 ≤ r → r ≤ 10000 →
      0 ≤ f r ∧
        f r ≤ recurrenceMap (stagePrime r) (1 / 5) (f (r - 1)))
    (htail : ∀ j < stageHorizon Q - 10000,
      0 ≤ f (10000 + j) →
      lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1 →
        0 ≤ f (10000 + j + 1) ∧
          f (10000 + j + 1) ≤
            recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
              (f (10000 + j))) :
    (∀ j ≤ stageHorizon Q - 10000, 0 ≤ f (10000 + j)) ∧
      (∀ j < stageHorizon Q - 10000,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (stageHorizon Q) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000
            (stageHorizon Q - 10000) /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000
            (stageHorizon Q - 10000)) := by
  have hcertificate : Certificate.RecurrenceChain
      Certificate.certificatePrimes (f 3) (f 10000) := by
    apply certificateRecurrenceChain_of_stageSteps f
    intro r hrlo hrhi
    have h := hfinite r hrlo hrhi
    exact ⟨h.1, by simpa [Certificate.fixedRecurrence] using h.2⟩
  have h := certificate_and_tail_survival_joint f
    (stageHorizon Q - 10000) hf3_nonneg hf3 hcertificate htail
  have hhor : 10000 + (stageHorizon Q - 10000) = stageHorizon Q := by
    simp [stageHorizon]
  simpa [hhor] using h

/-- The completely conditional finite-certificate and analytic-tail bridge.
At every stage the concrete sieve may use both current nonnegativity and the
denominator guard; neither fact is assumed for any future stage.  The checked
integer certificate proves all finite guards, and the analytic budget then
proves all guards through the common-period horizon. -/
theorem conditional_stage_recurrence_survival_to_horizon
    (Q : ℕ) (f : ℕ → ℝ)
    (hf3_nonneg : 0 ≤ f 3)
    (hf3 : f 3 ≤ 51 / 20)
    (hfinite : ∀ r, 4 ≤ r → r ≤ 10000 →
      0 ≤ f (r - 1) →
      lossRatio (stagePrime r) (1 / 5) (f (r - 1)) < 1 →
        0 ≤ f r ∧
          f r ≤ recurrenceMap (stagePrime r) (1 / 5) (f (r - 1)))
    (htail : ∀ j < stageHorizon Q - 10000,
      0 ≤ f (10000 + j) →
      lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1 →
        0 ≤ f (10000 + j + 1) ∧
          f (10000 + j + 1) ≤
            recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
              (f (10000 + j))) :
    (∀ r, 4 ≤ r → r ≤ 10000 →
        lossRatio (stagePrime r) (1 / 5) (f (r - 1)) < 1) ∧
      (∀ r, 3 ≤ r → r ≤ 10000 → 0 ≤ f r) ∧
      (∀ j ≤ stageHorizon Q - 10000, 0 ≤ f (10000 + j)) ∧
      (∀ j < stageHorizon Q - 10000,
        lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1) ∧
      f (stageHorizon Q) ≤
        13000 * Tail.prefixProduct Tail.tailN 10000
            (stageHorizon Q - 10000) /
          (1 - 13000 * Tail.prefixCost Tail.tailN Tail.tailC 10000
            (stageHorizon Q - 10000)) := by
  let g : ℕ → ℝ := fun i ↦ f (i + 3)
  have hcert := Certificate.conditional_certificate_valid_chain_and_lt
    g (by simpa [g] using hf3_nonneg) (by simpa [g] using hf3) (by
      intro i hgi hvalid
      have hiPrev : (i : ℕ) + 4 - 1 = (i : ℕ) + 3 := by omega
      have hprev : 0 ≤ f ((i : ℕ) + 4 - 1) := by
        simpa [g, hiPrev] using hgi
      have hvalid' : lossRatio (stagePrime ((i : ℕ) + 4)) (1 / 5)
          (f ((i : ℕ) + 4 - 1)) < 1 := by
        simpa [g, hiPrev, Certificate.certificatePrimes_eq_stagePrimes] using hvalid
      have hs := hfinite ((i : ℕ) + 4) (by omega) (by
        have hi : (i : ℕ) < 9997 :=
          lt_of_lt_of_eq i.isLt Certificate.certificatePrimes_length
        omega) hprev hvalid'
      refine ⟨?_, ?_⟩
      · simpa [g] using hs.1
      · simpa [g, Certificate.fixedRecurrence,
          Certificate.certificatePrimes_eq_stagePrimes] using hs.2)
  have hfiniteValid : ∀ r, 4 ≤ r → r ≤ 10000 →
      lossRatio (stagePrime r) (1 / 5) (f (r - 1)) < 1 := by
    intro r hrlo hrhi
    let i : Fin Certificate.certificatePrimes.length :=
      ⟨r - 4, by rw [Certificate.certificatePrimes_length]; omega⟩
    have hv := hcert.1 i
    have hir : (i : ℕ) + 4 = r := by
      dsimp [i]
      omega
    have hrprev : r - 1 = (i : ℕ) + 3 := by omega
    simpa [g, Certificate.certificatePrimes_eq_stagePrimes, hir, hrprev] using hv
  have hfiniteNonneg : ∀ r, 3 ≤ r → r ≤ 10000 → 0 ≤ f r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro hrlo hrhi
        by_cases hr3 : r = 3
        · simpa [hr3] using hf3_nonneg
        · have hr4 : 4 ≤ r := by omega
          have hprev : 0 ≤ f (r - 1) :=
            ih (r - 1) (by omega) (by omega) (by omega)
          exact (hfinite r hr4 hrhi hprev (hfiniteValid r hr4 hrhi)).1
  have hchain : Certificate.RecurrenceChain
      Certificate.certificatePrimes (f 3) (f 10000) := by
    simpa [g, Certificate.certificatePrimes_length] using hcert.2.1
  have hf10000_nonneg : 0 ≤ f 10000 :=
    recurrenceChain_end_nonneg hchain hf3_nonneg
  have hf10000 : f 10000 < 13000 := by
    simpa [g, Certificate.certificatePrimes_length] using hcert.2.2.2
  have htail := tail_survival_joint_of_sieve_recurrence f
    (stageHorizon Q - 10000) hf10000_nonneg hf10000 htail
  have hhor : 10000 + (stageHorizon Q - 10000) = stageHorizon Q := by
    simp [stageHorizon]
  exact ⟨hfiniteValid, hfiniteNonneg, htail.1, htail.2.1,
    by simpa [hhor] using htail.2.2⟩

end

end Erdos586
