import Mathlib

/-!
# Elementary with-high-probability calculus

This file isolates the deterministic real-analysis used when finite event
probabilities are assembled.  It deliberately does not depend on a particular
finite probability space: an application supplies probability functions and
the relevant pointwise bounds (monotonicity, a union bound, or a complement
identity).
-/

open Filter
open scoped Topology

namespace Erdos807
namespace WHP

/-- A sequence of real numbers represents probabilities of events holding
with high probability when it tends to `1`. -/
def WithHighProbability (p : ℕ → ℝ) : Prop :=
  Tendsto p atTop (nhds 1)

/-- A sequence of real numbers is a negligible failure probability when it
tends to `0`. -/
def Negligible (p : ℕ → ℝ) : Prop :=
  Tendsto p atTop (nhds 0)

/-- The elementary range condition satisfied by a sequence of finite event
probabilities. -/
def IsProbabilitySequence (p : ℕ → ℝ) : Prop :=
  ∀ n, p n ∈ Set.Icc (0 : ℝ) 1

theorem IsProbabilitySequence.nonneg {p : ℕ → ℝ}
    (hp : IsProbabilitySequence p) (n : ℕ) : 0 ≤ p n :=
  (hp n).1

theorem IsProbabilitySequence.le_one {p : ℕ → ℝ}
    (hp : IsProbabilitySequence p) (n : ℕ) : p n ≤ 1 :=
  (hp n).2

/-! ## Calculus for real-valued probability sequences -/

/-- The complement of a negligible failure probability holds with high
probability.  An eventual complement identity is enough. -/
theorem whp_of_failure_tendsto_zero {success failure : ℕ → ℝ}
    (hcompl : ∀ᶠ n in atTop, success n = 1 - failure n)
    (hfailure : Negligible failure) : WithHighProbability success := by
  rw [WithHighProbability, Negligible] at *
  have h : Tendsto (fun n : ℕ ↦ (1 : ℝ) - failure n) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hfailure
  simpa only [sub_zero] using h.congr' (hcompl.mono fun _ hn ↦ hn.symm)

/-- The failure probability of a with-high-probability event tends to zero. -/
theorem failure_tendsto_zero_of_whp {success failure : ℕ → ℝ}
    (hcompl : ∀ᶠ n in atTop, failure n = 1 - success n)
    (hsuccess : WithHighProbability success) : Negligible failure := by
  rw [WithHighProbability, Negligible] at *
  have h : Tendsto (fun n : ℕ ↦ (1 : ℝ) - success n) atTop (nhds (1 - 1)) :=
    tendsto_const_nhds.sub hsuccess
  simpa only [sub_self] using h.congr' (hcompl.mono fun _ hn ↦ hn.symm)

/-- Complementation exchanges convergence to one and convergence to zero. -/
theorem whp_iff_failure_tendsto_zero {success failure : ℕ → ℝ}
    (hsuccess : ∀ᶠ n in atTop, success n = 1 - failure n)
    (hfailure : ∀ᶠ n in atTop, failure n = 1 - success n) :
    WithHighProbability success ↔ Negligible failure :=
  ⟨failure_tendsto_zero_of_whp hfailure,
    whp_of_failure_tendsto_zero hsuccess⟩

/-- A sequence squeezed between zero and a negligible sequence is
negligible. -/
theorem negligible_of_eventually_le {p bound : ℕ → ℝ}
    (hp_nonneg : ∀ᶠ n in atTop, 0 ≤ p n)
    (hp_bound : ∀ᶠ n in atTop, p n ≤ bound n)
    (hbound : Negligible bound) : Negligible p := by
  exact squeeze_zero' hp_nonneg hp_bound hbound

/-- Probability monotonicity preserves the with-high-probability property.
The upper bound by one is stated explicitly so that this lemma is usable for
any supplied finite probability function. -/
theorem mono {p q : ℕ → ℝ} (hp : WithHighProbability p)
    (hpq : ∀ᶠ n in atTop, p n ≤ q n)
    (hq_one : ∀ᶠ n in atTop, q n ≤ 1) : WithHighProbability q := by
  exact hp.squeeze' tendsto_const_nhds hpq hq_one

/-- Pointwise domination by another probability sequence preserves the
with-high-probability property. -/
theorem mono_probability {p q : ℕ → ℝ} (hp : WithHighProbability p)
    (hq : IsProbabilitySequence q)
    (hpq : ∀ᶠ n in atTop, p n ≤ q n) : WithHighProbability q :=
  mono hp hpq (Eventually.of_forall hq.le_one)

/-- A two-event union bound turns two negligible failure probabilities into
a negligible combined failure probability. -/
theorem negligible_of_union_bound {p q union : ℕ → ℝ}
    (hunion_nonneg : ∀ᶠ n in atTop, 0 ≤ union n)
    (hunion : ∀ᶠ n in atTop, union n ≤ p n + q n)
    (hp : Negligible p) (hq : Negligible q) : Negligible union := by
  apply negligible_of_eventually_le hunion_nonneg hunion
  rw [Negligible] at hp hq ⊢
  simpa using hp.add hq

/-- The sum of a fixed finite family of negligible sequences is negligible. -/
theorem negligible_finset_sum {I : Type*} (s : Finset I) (p : I → ℕ → ℝ)
    (hp : ∀ i ∈ s, Negligible (p i)) :
    Negligible (fun n ↦ ∑ i ∈ s, p i n) := by
  rw [Negligible]
  simpa using tendsto_finsetSum s fun i hi ↦ hp i hi

/-- A fixed finite union bound yields a negligible failure probability. -/
theorem negligible_of_finset_union_bound {I : Type*} (s : Finset I)
    (p : I → ℕ → ℝ) {union : ℕ → ℝ}
    (hunion_nonneg : ∀ᶠ n in atTop, 0 ≤ union n)
    (hunion : ∀ᶠ n in atTop, union n ≤ ∑ i ∈ s, p i n)
    (hp : ∀ i ∈ s, Negligible (p i)) : Negligible union := by
  exact negligible_of_eventually_le hunion_nonneg hunion
    (negligible_finset_sum s p hp)

/-- A useful varying finite-count form of the union bound.  The application
supplies the number of bad choices and a uniform per-choice error; no
asymptotic relation between them is built into the statement. -/
theorem negligible_of_count_mul_bound {failure error : ℕ → ℝ}
    (count : ℕ → ℕ)
    (hfailure_nonneg : ∀ᶠ n in atTop, 0 ≤ failure n)
    (hfailure : ∀ᶠ n in atTop,
      failure n ≤ (count n : ℝ) * error n)
    (hproduct : Negligible (fun n ↦ (count n : ℝ) * error n)) :
    Negligible failure :=
  negligible_of_eventually_le hfailure_nonneg hfailure hproduct

/-- Bonferroni's lower bound proves that the intersection of two
with-high-probability events is again with high probability. -/
theorem inter_of_probability_lower_bound {p q inter : ℕ → ℝ}
    (hp : WithHighProbability p) (hq : WithHighProbability q)
    (hlower : ∀ᶠ n in atTop, p n + q n - 1 ≤ inter n)
    (hinter_one : ∀ᶠ n in atTop, inter n ≤ 1) :
    WithHighProbability inter := by
  have hlower_tendsto :
      Tendsto (fun n ↦ p n + q n - 1) atTop (nhds 1) := by
    convert (hp.add hq).sub tendsto_const_nhds using 1
    norm_num
  exact hlower_tendsto.squeeze' tendsto_const_nhds hlower hinter_one

/-- Probability-sequence version of the two-event intersection rule. -/
theorem inter {p q inter : ℕ → ℝ}
    (hp : WithHighProbability p) (hq : WithHighProbability q)
    (hinter : IsProbabilitySequence inter)
    (hlower : ∀ᶠ n in atTop, p n + q n - 1 ≤ inter n) :
    WithHighProbability inter :=
  inter_of_probability_lower_bound hp hq hlower
    (Eventually.of_forall hinter.le_one)

/-- If the failure of an intersection satisfies the usual union bound, then
the intersection holds with high probability. -/
theorem inter_of_failure_union_bound
    {pFailure qFailure interFailure inter : ℕ → ℝ}
    (hp : Negligible pFailure) (hq : Negligible qFailure)
    (hinterFailure_nonneg : ∀ᶠ n in atTop, 0 ≤ interFailure n)
    (hunion : ∀ᶠ n in atTop,
      interFailure n ≤ pFailure n + qFailure n)
    (hcompl : ∀ᶠ n in atTop, inter n = 1 - interFailure n) :
    WithHighProbability inter := by
  apply whp_of_failure_tendsto_zero hcompl
  exact negligible_of_union_bound hinterFailure_nonneg hunion hp hq

/-- An event probability tends to zero if it is eventually bounded by the
complement of a with-high-probability strict-improvement event.  This is the
real-valued form used to refute an asymptotic equality conjecture. -/
theorem equality_tendsto_zero_of_le_compl_whp
    {strict equality : ℕ → ℝ}
    (hstrict : WithHighProbability strict)
    (hequality_nonneg : ∀ᶠ n in atTop, 0 ≤ equality n)
    (hcontain : ∀ᶠ n in atTop, equality n ≤ 1 - strict n) :
    Negligible equality := by
  apply negligible_of_eventually_le hequality_nonneg hcontain
  exact failure_tendsto_zero_of_whp (Eventually.of_forall fun _ ↦ rfl) hstrict

/-! ## Event-level consequences for a supplied finite probability function -/

section Events

variable {Omega : ℕ → Type*}
variable (probability : (n : ℕ) → (Omega n → Prop) → ℝ)

/-- Event inclusion preserves with-high-probability statements. -/
theorem event_mono
    (hprob_mono : ∀ {n : ℕ} {P Q : Omega n → Prop},
      (∀ omega, P omega → Q omega) → probability n P ≤ probability n Q)
    (hprob_le_one : ∀ (n : ℕ) (P : Omega n → Prop), probability n P ≤ 1)
    {P Q : (n : ℕ) → Omega n → Prop}
    (hP : WithHighProbability (fun n ↦ probability n (P n)))
    (hPQ : ∀ᶠ n in atTop, ∀ omega, P n omega → Q n omega) :
    WithHighProbability (fun n ↦ probability n (Q n)) := by
  apply mono hP
  · filter_upwards [hPQ] with n hn
    exact hprob_mono hn
  · exact Eventually.of_forall fun n ↦ hprob_le_one n (Q n)

/-- Two event sequences hold simultaneously with high probability, using
only nonnegativity, monotonicity, complementation, and the two-event union
bound of the supplied probability function. -/
theorem event_inter
    (hprob_nonneg : ∀ (n : ℕ) (P : Omega n → Prop), 0 ≤ probability n P)
    (hprob_mono : ∀ {n : ℕ} {P Q : Omega n → Prop},
      (∀ omega, P omega → Q omega) → probability n P ≤ probability n Q)
    (hprob_compl : ∀ (n : ℕ) (P : Omega n → Prop),
      probability n (fun omega ↦ ¬ P omega) = 1 - probability n P)
    (hprob_union : ∀ (n : ℕ) (P Q : Omega n → Prop),
      probability n (fun omega ↦ P omega ∨ Q omega) ≤
        probability n P + probability n Q)
    {P Q : (n : ℕ) → Omega n → Prop}
    (hP : WithHighProbability (fun n ↦ probability n (P n)))
    (hQ : WithHighProbability (fun n ↦ probability n (Q n))) :
    WithHighProbability
      (fun n ↦ probability n (fun omega ↦ P n omega ∧ Q n omega)) := by
  let pFailure : ℕ → ℝ :=
    fun n ↦ probability n (fun omega ↦ ¬ P n omega)
  let qFailure : ℕ → ℝ :=
    fun n ↦ probability n (fun omega ↦ ¬ Q n omega)
  let interFailure : ℕ → ℝ :=
    fun n ↦ probability n (fun omega ↦ ¬ (P n omega ∧ Q n omega))
  apply inter_of_failure_union_bound
      (pFailure := pFailure) (qFailure := qFailure)
      (interFailure := interFailure)
  · apply failure_tendsto_zero_of_whp _ hP
    exact Eventually.of_forall fun n ↦ hprob_compl n (P n)
  · apply failure_tendsto_zero_of_whp _ hQ
    exact Eventually.of_forall fun n ↦ hprob_compl n (Q n)
  · exact Eventually.of_forall fun n ↦
      hprob_nonneg n (fun omega ↦ ¬ (P n omega ∧ Q n omega))
  · apply Eventually.of_forall
    intro n
    calc
      interFailure n ≤
          probability n (fun omega ↦ ¬ P n omega ∨ ¬ Q n omega) := by
        apply hprob_mono
        intro omega hnot
        by_cases hp : P n omega
        · exact Or.inr fun hq ↦ hnot ⟨hp, hq⟩
        · exact Or.inl hp
      _ ≤ pFailure n + qFailure n := hprob_union n _ _
  · exact Eventually.of_forall fun n ↦
      (by
        rw [show interFailure n = 1 -
          probability n (fun omega ↦ P n omega ∧ Q n omega) from
            hprob_compl n (fun omega ↦ P n omega ∧ Q n omega)]
        ring)

/-- If an equality event is eventually contained in the complement of a
with-high-probability strict-improvement event, then the equality event has
probability tending to zero. -/
theorem event_equality_tendsto_zero
    (hprob_nonneg : ∀ (n : ℕ) (P : Omega n → Prop), 0 ≤ probability n P)
    (hprob_mono : ∀ {n : ℕ} {P Q : Omega n → Prop},
      (∀ omega, P omega → Q omega) → probability n P ≤ probability n Q)
    (hprob_compl : ∀ (n : ℕ) (P : Omega n → Prop),
      probability n (fun omega ↦ ¬ P omega) = 1 - probability n P)
    {strict equality : (n : ℕ) → Omega n → Prop}
    (hstrict : WithHighProbability (fun n ↦ probability n (strict n)))
    (hcontain : ∀ᶠ n in atTop,
      ∀ omega, equality n omega → ¬ strict n omega) :
    Negligible (fun n ↦ probability n (equality n)) := by
  apply equality_tendsto_zero_of_le_compl_whp hstrict
  · exact Eventually.of_forall fun n ↦ hprob_nonneg n (equality n)
  · filter_upwards [hcontain] with n hn
    rw [← hprob_compl n (strict n)]
    exact hprob_mono hn

end Events

end WHP
end Erdos807
