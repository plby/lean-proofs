import ErdosProblems.Erdos543.Model
import ErdosProblems.Erdos543.Asymptotics
import ErdosProblems.Erdos543.PrimeSequence

open Filter
open scoped Topology

namespace Erdos543.FinalLogic

/-- The quotient formulation of an `o(log log N)` error term used throughout
the formalization. -/
def IsLittleOLogLog (g : ℕ → ℝ) : Prop :=
  Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)

/-- The literal proposed upper bound in Problem 543, with the exact universal
threshold `Model.universalF` viewed as a real number. -/
def Problem543UpperBound : Prop :=
  ∃ g : ℕ → ℝ,
    IsLittleOLogLog g ∧
    ∀ᶠ N : ℕ in atTop,
      (Model.universalF N : ℝ) ≤ cutoffArgument g N

/-- Integer-rounded form of the proposed upper bound.  This is the form to
which a probabilistic theorem about subsets of a fixed cardinality applies. -/
def Problem543RoundedUpperBound : Prop :=
  ∃ g : ℕ → ℝ,
    IsLittleOLogLog g ∧
    ∀ᶠ N : ℕ in atTop, Model.universalF N ≤ cutoffSize g N

/-- Passing from the literal real inequality to the natural ceiling loses no
information needed for the obstruction argument. -/
lemma universalF_le_cutoffSize_of_cast_le {g : ℕ → ℝ} {N : ℕ}
    (h : (Model.universalF N : ℝ) ≤ cutoffArgument g N) :
    Model.universalF N ≤ cutoffSize g N := by
  rw [cutoffSize]
  exact_mod_cast h.trans (Nat.le_ceil (cutoffArgument g N))

lemma problem543UpperBound_imp_rounded :
    Problem543UpperBound → Problem543RoundedUpperBound := by
  rintro ⟨g, hg, hbound⟩
  refine ⟨g, hg, ?_⟩
  filter_upwards [hbound] with N hN
  exact universalF_le_cutoffSize_of_cast_le hN

/-- Conversely, the rounding error is at most one, and the constant function
`1` is `o(log log N)`.  Thus the rounded formulation is genuinely equivalent
to the literal asymptotic claim. -/
lemma problem543RoundedUpperBound_imp_upperBound :
    Problem543RoundedUpperBound → Problem543UpperBound := by
  rintro ⟨g, hg, hbound⟩
  let g' : ℕ → ℝ := fun N ↦ g N + 1
  have hone : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) / Real.log (Real.log (N : ℝ)))
      atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp tendsto_log_log_nat_atTop
  have hg' : IsLittleOLogLog g' := by
    simpa [IsLittleOLogLog, g', add_div] using hg.add hone
  refine ⟨g', hg', ?_⟩
  filter_upwards [hbound, eventually_cutoffArgument_pos hg] with N hN harg
  have hcast : (Model.universalF N : ℝ) ≤ (cutoffSize g N : ℝ) := by
    exact_mod_cast hN
  calc
    (Model.universalF N : ℝ) ≤ (cutoffSize g N : ℝ) := hcast
    _ ≤ cutoffArgument g N + 1 := (Nat.ceil_lt_add_one harg.le).le
    _ = cutoffArgument g' N := by simp [cutoffArgument, g']; ring

lemma problem543UpperBound_iff_rounded :
    Problem543UpperBound ↔ Problem543RoundedUpperBound :=
  ⟨problem543UpperBound_imp_rounded,
    problem543RoundedUpperBound_imp_upperBound⟩

/-- Failure for a prime modulus, packaged so that the `NeZero p` instance
needed by `ZMod p` is constructed from the primality witness.  For nonprimes
the predicate is vacuous. -/
def PrimeCyclicFailureAt (p k : ℕ) : Prop :=
  ∀ hp : p.Prime,
    letI : NeZero p := ⟨hp.ne_zero⟩
    ¬ Model.HalfComplete (ZMod p) k

/-- The direct "all sufficiently large prime moduli" formulation of the
central obstruction. -/
def EventualPrimeModuliFailure : Prop :=
  ∀ (g : ℕ → ℝ), IsLittleOLogLog g →
    ∀ᶠ p : ℕ in atTop, PrimeCyclicFailureAt p (cutoffSize g p)

/-- The exact prime-sequence formulation of the central probabilistic
obstruction.  It is deliberately just a proposition: the analytic part of
the development must prove it. -/
def EventualPrimeCyclicFailure : Prop :=
  ∀ (g : ℕ → ℝ), IsLittleOLogLog g →
    ∀ᶠ i : ℕ in atTop,
      ¬ Model.HalfComplete (ZMod (PrimeSequence.primeSeq i))
        (cutoffSize g (PrimeSequence.primeSeq i))

/-- An assertion for every sufficiently large prime modulus restricts to the
canonical cofinal prime sequence.  This is where the existence of arbitrarily
large primes enters the final logic. -/
lemma eventualPrimeModuliFailure_imp_eventualPrimeCyclicFailure :
    EventualPrimeModuliFailure → EventualPrimeCyclicFailure := by
  intro hmoduli g hg
  have hseq := PrimeSequence.eventually_primeSeq (hmoduli g hg)
  filter_upwards [hseq] with i hi
  exact hi (PrimeSequence.primeSeq_prime i)

/-- Rounded upper bounds already contradict eventual failure on the prime
sequence.  The strict reverse inequality comes from `Model.universalF`'s
minimality and adjacent-level monotonicity. -/
lemma candidate_rounded_upper_bound_contradicts_prime_cyclic_failure
    {g : ℕ → ℝ}
    (hrounded : ∀ᶠ N : ℕ in atTop,
      Model.universalF N ≤ cutoffSize g N)
    (hfail : ∀ᶠ i : ℕ in atTop,
      ¬ Model.HalfComplete (ZMod (PrimeSequence.primeSeq i))
        (cutoffSize g (PrimeSequence.primeSeq i))) :
    False := by
  have hroundedPrime : ∀ᶠ i : ℕ in atTop,
      Model.universalF (PrimeSequence.primeSeq i) ≤
        cutoffSize g (PrimeSequence.primeSeq i) :=
    PrimeSequence.eventually_primeSeq hrounded
  have hfalse : ∀ᶠ i : ℕ in atTop, False := by
    filter_upwards [hroundedPrime, hfail] with i hle hbad
    have hlt : cutoffSize g (PrimeSequence.primeSeq i) <
        Model.universalF (PrimeSequence.primeSeq i) :=
      Model.not_halfComplete_zmod_imp_lt_universalF hbad
    omega
  rcases hfalse.exists with ⟨i, hi⟩
  exact hi

/-- A single candidate error term cannot simultaneously give the claimed
universal upper bound and have the eventual prime-cyclic failure supplied by
the obstruction theorem. -/
lemma candidate_upper_bound_contradicts_prime_cyclic_failure
    {g : ℕ → ℝ}
    (hbound : ∀ᶠ N : ℕ in atTop,
      (Model.universalF N : ℝ) ≤ cutoffArgument g N)
    (hfail : ∀ᶠ i : ℕ in atTop,
      ¬ Model.HalfComplete (ZMod (PrimeSequence.primeSeq i))
        (cutoffSize g (PrimeSequence.primeSeq i))) :
    False := by
  have hrounded : ∀ᶠ N : ℕ in atTop,
      Model.universalF N ≤ cutoffSize g N := by
    filter_upwards [hbound] with N hN
    exact universalF_le_cutoffSize_of_cast_le hN
  exact candidate_rounded_upper_bound_contradicts_prime_cyclic_failure
    hrounded hfail

/-- The established eventual failure on the cofinal prime sequence refutes
the literal `log₂ N + o(log log N)` upper-bound claim. -/
theorem not_problem543UpperBound_of_eventualPrimeCyclicFailure
    (hobstruction : EventualPrimeCyclicFailure) :
    ¬ Problem543UpperBound := by
  rintro ⟨g, hg, hbound⟩
  exact candidate_upper_bound_contradicts_prime_cyclic_failure hbound
    (hobstruction g hg)

theorem not_problem543RoundedUpperBound_of_eventualPrimeCyclicFailure
    (hobstruction : EventualPrimeCyclicFailure) :
    ¬ Problem543RoundedUpperBound := by
  rintro ⟨g, hg, hbound⟩
  exact candidate_rounded_upper_bound_contradicts_prime_cyclic_failure hbound
    (hobstruction g hg)

/-- Equivalent entry point that accepts the central obstruction directly as
a quantified theorem parameter. -/
theorem not_problem543UpperBound_of_forall_eventual_failure
    (hobstruction : ∀ (g : ℕ → ℝ),
      Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0) →
      ∀ᶠ i : ℕ in atTop,
        ¬ Model.HalfComplete (ZMod (PrimeSequence.primeSeq i))
          (cutoffSize g (PrimeSequence.primeSeq i))) :
    ¬ Problem543UpperBound := by
  apply not_problem543UpperBound_of_eventualPrimeCyclicFailure
  intro g hg
  exact hobstruction g hg

/-- Direct all-large-primes entry point. -/
theorem not_problem543UpperBound_of_eventualPrimeModuliFailure
    (hobstruction : EventualPrimeModuliFailure) :
    ¬ Problem543UpperBound :=
  not_problem543UpperBound_of_eventualPrimeCyclicFailure
    (eventualPrimeModuliFailure_imp_eventualPrimeCyclicFailure hobstruction)

end Erdos543.FinalLogic
