/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixATwoPoint
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAFirstMoment
import ErdosProblems.Erdos1166.Erdos1166HLOZPoissonOscillation
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAExactExit

/-!
# Source-shaped Appendix-A two-point objects

This file instantiates the finite bookkeeping in HLOZ (A.16)--(A.17).
The inner event is the finite union of profile atoms already defined in
`Erdos1166HLOZAppendixAFirstMoment`; the outer fibers are literal fibers of
the annular excursion count.  Consequently their disjointness, the truncated
fiber cover, and the bound of the sum of their masses by the outer-profile
mass are theorems rather than assumptions.

The remaining Harnack comparison is reduced to the exact first-exit kernel
from `Erdos1166HLOZHarnack`.  The only quantitative spatial premises in the
final theorem are the finite potential-kernel difference, boundary range,
and denominator estimates exposed by `Erdos1166HLOZPoissonOscillation`.
-/

namespace Erdos1166.HLOZAppendixATwoPointSource

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open HLOZAppendixAFirstMoment
open HLOZAppendixATwoPoint
open HLOZPropositionA7
open KilledGreen
open HLOZAppendixAExactExit

/-! ## Concrete profile and excursion-count fibers -/

/-- The actual-walk event obtained by taking the finite union of the supplied
annular atoms over a profile family. -/
def annularProfileFiber {Ω : Type*} {N : ℕ}
    (Q : Finset (NatPath N)) (atom : NatPath N → Set Ω) : Set Ω :=
  successfulProfileEvent Q atom

/-- The part of an outer event on which the source annular excursion count is
exactly `m`. -/
def countedOuterFiber {Ω : Type*}
    (outer : Set Ω) (count : Ω → ℕ) (m : ℕ) : Set Ω :=
  outer ∩ {ω | count ω = m}

/-- The literal finite sum in (A.16), with the inner profile family allowed to
depend on the excursion count. -/
def truncatedAnnularPair {Ω : Type*} {N : ℕ}
    (Q : ℕ → Finset (NatPath N))
    (innerAtom : ℕ → NatPath N → Set Ω)
    (outer : Set Ω) (count : Ω → ℕ) (cutoff : ℕ) : Set Ω :=
  ⋃ m ∈ Finset.range (cutoff + 1),
    annularProfileFiber (Q m) (innerAtom m) ∩ countedOuterFiber outer count m

/-- The discarded part of a two-point event.  With this definition the event
split (A.14)--(A.15) is tautologically exhaustive. -/
def discardedAnnularTail {Ω : Type*}
    (Ax Ay truncated : Set Ω) : Set Ω :=
  (Ax ∩ Ay) \ truncated

/-- The genuine exceptional event in (A.14): the two sites are successful,
but the annular excursion count is larger than the truncation cutoff. -/
def largeCountPairTail {Ω : Type*}
    (Ax Ay : Set Ω) (count : Ω → ℕ) (cutoff : ℕ) : Set Ω :=
  Ax ∩ Ay ∩ {ω | cutoff < count ω}

theorem pair_subset_truncated_union_discardedTail {Ω : Type*}
    (Ax Ay truncated : Set Ω) :
    Ax ∩ Ay ⊆ truncated ∪ discardedAnnularTail Ax Ay truncated := by
  intro ω hω
  by_cases ht : ω ∈ truncated
  · exact Or.inl ht
  · exact Or.inr ⟨hω, ht⟩

/-- Once every successful pair with bounded excursion count is represented
by the profile fibers, the only discarded part is the source's large-count
event.  This is the substantive event inclusion behind (A.14), rather than
the tautological set-complement split. -/
theorem pair_subset_truncated_union_largeCountPairTail {Ω : Type*}
    (Ax Ay truncated : Set Ω) (count : Ω → ℕ) (cutoff : ℕ)
    (hbounded : Ax ∩ Ay ∩ {ω | count ω ≤ cutoff} ⊆ truncated) :
    Ax ∩ Ay ⊆ truncated ∪ largeCountPairTail Ax Ay count cutoff := by
  intro ω hω
  by_cases hc : count ω ≤ cutoff
  · exact Or.inl (hbounded ⟨hω, hc⟩)
  · exact Or.inr ⟨hω, Nat.lt_of_not_ge hc⟩

theorem truncatedAnnularPair_fiber_cover {Ω : Type*} {N : ℕ}
    (Q : ℕ → Finset (NatPath N))
    (innerAtom : ℕ → NatPath N → Set Ω)
    (outer : Set Ω) (count : Ω → ℕ) (cutoff : ℕ) :
    truncatedAnnularPair Q innerAtom outer count cutoff ⊆
      ⋃ m ∈ Finset.range (cutoff + 1),
        annularProfileFiber (Q m) (innerAtom m) ∩
          countedOuterFiber outer count m := by
  simpa [truncatedAnnularPair]

theorem pairwiseDisjoint_countedOuterFiber {Ω : Type*}
    (outer : Set Ω) (count : Ω → ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set ℕ) (countedOuterFiber outer count) := by
  intro i hi j hj hij
  change Disjoint (countedOuterFiber outer count i)
    (countedOuterFiber outer count j)
  rw [Set.disjoint_left]
  intro ω hωi hωj
  exact hij (hωi.2.symm.trans hωj.2)

theorem measurableSet_countedOuterFiber {Ω : Type*} [MeasurableSpace Ω]
    {outer : Set Ω} {count : Ω → ℕ} (houter : MeasurableSet outer)
    (hcount : Measurable count) (m : ℕ) :
    MeasurableSet (countedOuterFiber outer count m) := by
  exact houter.inter (hcount (measurableSet_singleton m))

/-- The outer-fiber sum in (A.16) is bounded by the outer-profile event.
There is no separate summation premise. -/
theorem sum_countedOuterFiber_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {outer : Set Ω} {count : Ω → ℕ} (cutoff : ℕ)
    (houter : MeasurableSet outer) (hcount : Measurable count) :
    (∑ m ∈ Finset.range (cutoff + 1),
      μ.real (countedOuterFiber outer count m)) ≤ μ.real outer := by
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.range (cutoff + 1)) : Set ℕ)
        (countedOuterFiber outer count) := by
    intro i hi j hj hij
    exact pairwiseDisjoint_countedOuterFiber outer count
      (Set.mem_univ i) (Set.mem_univ j) hij
  have hmeas : ∀ m ∈ Finset.range (cutoff + 1),
      MeasurableSet (countedOuterFiber outer count m) := by
    intro m hm
    exact measurableSet_countedOuterFiber houter hcount m
  calc
    (∑ m ∈ Finset.range (cutoff + 1),
        μ.real (countedOuterFiber outer count m)) =
        μ.real (⋃ m ∈ Finset.range (cutoff + 1),
          countedOuterFiber outer count m) :=
      (measureReal_biUnion_finset hdisjoint hmeas).symm
    _ ≤ μ.real outer := by
      apply measureReal_mono
      · intro ω hω
        obtain ⟨m, hω⟩ := mem_iUnion.mp hω
        obtain ⟨hm, hωm⟩ := mem_iUnion.mp hω
        exact hωm.1
      · exact measure_ne_top μ outer

/-! ## Potential-kernel control of the exact exit profile -/

/-- A one-sided form of the relative first-exit-kernel estimate. -/
theorem firstExitAtWeight_square_toReal_le_one_add_error_mul
    {R : ℕ} {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {x x' y : Site} (hx : x ∈ squareDisk R) (hx' : x' ∈ squareDisk R)
    (lowerBoundary upperBoundary : Site → ℝ) {denominatorLower error : ℝ}
    (hy : y ∉ squareDisk R) (hdenominatorLower : 0 < denominatorLower)
    (hden : denominatorLower ≤ squareGreenExitKernel R x' y)
    (hboundary : ∀ d : Direction,
      y - directionStep d ∈ squareDisk R →
      ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
        lowerBoundary (y - directionStep d) ≤
            a (w - (y - directionStep d)) ∧
          a (w - (y - directionStep d)) ≤
            upperBoundary (y - directionStep d))
    (hoscillation :
      (squareExitPotentialDifference R a x x' y +
        squareExitBoundaryPotentialRange R lowerBoundary upperBoundary y) /
          denominatorLower ≤ error) :
    (firstExitAtWeight (squareDisk R : Set Site) x y).toReal ≤
      (1 + error) *
        (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal := by
  have hratio :=
    firstExitAtWeight_square_ratio_sub_one_abs_le_potential_boundary
      ha hx hx' lowerBoundary upperBoundary hy hdenominatorLower hden hboundary
  let p := (firstExitAtWeight (squareDisk R : Set Site) x y).toReal
  let q := (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal
  have hq : 0 < q := by
    dsimp [q]
    rw [firstExitAtWeight_square_eq_kernel R x' y hy,
      squareGreenExitKernelENNReal_toReal]
    exact hdenominatorLower.trans_le hden
  have hratioUpper : p / q ≤ 1 + error := by
    have hratio' : |p / q - 1| ≤
        (squareExitPotentialDifference R a x x' y +
          squareExitBoundaryPotentialRange R lowerBoundary upperBoundary y) /
            denominatorLower := by
      simpa [p, q] using hratio
    have hself : p / q - 1 ≤ |p / q - 1| := le_abs_self _
    linarith
  calc
    p = (p / q) * q := by field_simp
    _ ≤ (1 + error) * q :=
      mul_le_mul_of_nonneg_right hratioUpper hq.le

/-- The exit-kernel weighted profile mass.  The coefficient after the exit
site is the finite Appendix-A profile partition, with an additional
nonnegative continuation weight allowed for the truncated inner event. -/
noncomputable def annularProfileKernelMass {N : ℕ}
    (n : ℕ) (delta : ℝ) (Q : Finset (NatPath N))
    (R : ℕ) (start : Site) (exitSites : Finset Site)
    (continuation : Site → NatPath N → ℝ) : ℝ :=
  ∑ z ∈ exitSites,
    (firstExitAtWeight (squareDisk R : Set Site) start z).toReal *
      ∑ q ∈ Q, successfulProfileWeight n delta q * continuation z q

/-! ## Exact strong-Markov expansion of the source annular event -/

/-- The literal annular profile atom beginning at a random outer-path
horizon.  On the restarted walk it exits the square at an allowed boundary
site and then realizes the supplied profile-tail event. -/
abbrev sourceStoppedAnnularProfileAtom {N : ℕ}
    (τ : (ℕ → Direction) → ℕ) (R : ℕ) (start : Site)
    (exitSites : Finset Site)
    (profileTail : Site → NatPath N → Set (ℕ → Direction))
    (q : NatPath N) : Set (ℕ → Direction) :=
  stoppedAnnularProfileAtom τ (squareDisk R : Set Site) start exitSites
    profileTail q

/-- Individual source stopped-profile atoms are measurable as soon as the
stopping horizon and the fresh-walk profile tails are measurable. -/
theorem measurableSet_sourceStoppedAnnularProfileAtom {N : ℕ}
    (τ : (ℕ → Direction) → ℕ) (R : ℕ) (start : Site)
    (exitSites : Finset Site)
    (profileTail : Site → NatPath N → Set (ℕ → Direction))
    (q : NatPath N) (hτ : Measurable τ)
    (hexit : ∀ z ∈ exitSites, z ∉ squareDisk R)
    (hprofileMeasurable : ∀ z ∈ exitSites,
      MeasurableSet (profileTail z q)) :
    MeasurableSet
      (sourceStoppedAnnularProfileAtom τ R start exitSites profileTail q) := by
  unfold sourceStoppedAnnularProfileAtom stoppedAnnularProfileAtom
  apply (measurable_incrementShiftAfter hτ)
  apply Finset.measurableSet_biUnion
  intro z hz
  exact measurableSet_firstExitThenEvent (squareDisk R : Set Site) start z
    (profileTail z q) (hexit z hz) (hprofileMeasurable z hz)

/-- Disjoint fresh-walk profile tails remain disjoint after adjoining the
first-exit site and pulling back by a common stopped shift. -/
theorem pairwiseDisjoint_sourceStoppedAnnularProfileAtom {N : ℕ}
    (τ : (ℕ → Direction) → ℕ) (R : ℕ) (start : Site)
    (exitSites : Finset Site) (Q : Finset (NatPath N))
    (profileTail : Site → NatPath N → Set (ℕ → Direction))
    (hprofileDisjoint : ∀ z ∈ exitSites,
      Set.PairwiseDisjoint (↑Q : Set (NatPath N)) (profileTail z)) :
    Set.PairwiseDisjoint (↑Q : Set (NatPath N))
      (sourceStoppedAnnularProfileAtom τ R start exitSites profileTail) := by
  intro q hq q' hq' hne
  unfold sourceStoppedAnnularProfileAtom stoppedAnnularProfileAtom
  apply Disjoint.preimage
  simp only [Set.disjoint_iUnion_left, Set.disjoint_iUnion_right]
  intro z hz z' hz'
  by_cases hzz : z = z'
  · subst z'
    exact disjoint_firstExitThenEvent_of_tail_disjoint
      (squareDisk R : Set Site) start z
      (hprofileDisjoint z hz hq hq' hne)
  · exact disjoint_firstExitThenEvent_of_exit_ne
      (squareDisk R : Set Site) start
      (profileTail z' q) (profileTail z q') (Ne.symm hzz)

/-- Exact finite first-exit-kernel strong-Markov expansion for the actual
stopped annular profile fiber.  This discharges the structural
`hExactStrongMarkovExitKernelExpansion` premise of the source reduction:
after each finite profile-tail event is identified with its Appendix-A
birth-death weight, only the quantitative potential-kernel/Harnack estimates
remain.

The outer event may have probability zero; no positivity assumption is
needed. -/
theorem exactStrongMarkovExitKernelExpansion
    {N n : ℕ} (delta : ℝ)
    (τ : (ℕ → Direction) → ℕ) (outerFiber : Set (ℕ → Direction))
    (R : ℕ) (start : Site) (exitSites : Finset Site)
    (Q : Finset (NatPath N))
    (profileTail : Site → NatPath N → Set (ℕ → Direction))
    (continuation : Site → NatPath N → ℝ)
    (hτ : Measurable τ)
    (houter : ∀ k, MeasurableSet[
      ProbabilityTheory.iidHistory (X := Direction) k]
      (outerFiber ∩ {ω | τ ω = k}))
    (hexit : ∀ z ∈ exitSites, z ∉ squareDisk R)
    (hprofileMeasurable : ∀ z ∈ exitSites, ∀ q ∈ Q,
      MeasurableSet (profileTail z q))
    (hprofileDisjoint : ∀ z ∈ exitSites,
      Set.PairwiseDisjoint (↑Q : Set (NatPath N)) (profileTail z))
    (hprofileMass : ∀ z ∈ exitSites, ∀ q ∈ Q,
      (incrementLaw (profileTail z q)).toReal =
        successfulProfileWeight n delta q * continuation z q) :
    incrementLaw.real
        (annularProfileFiber Q
          (sourceStoppedAnnularProfileAtom τ R start exitSites profileTail) ∩
            outerFiber) =
      annularProfileKernelMass n delta Q R start exitSites continuation *
        incrementLaw.real outerFiber := by
  have hENN := measure_stoppedAnnularProfileUnion τ outerFiber
    (squareDisk R : Set Site) start exitSites Q profileTail hτ houter
    hexit hprofileMeasurable hprofileDisjoint
  change incrementLaw
      (annularProfileFiber Q
        (sourceStoppedAnnularProfileAtom τ R start exitSites profileTail) ∩
          outerFiber) =
    incrementLaw outerFiber *
      ∑ z ∈ exitSites,
        firstExitAtWeight (squareDisk R : Set Site) start z *
          ∑ q ∈ Q, incrementLaw (profileTail z q) at hENN
  rw [measureReal_def, hENN, ENNReal.toReal_mul]
  rw [mul_comm]
  congr 1
  unfold annularProfileKernelMass
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum]
    · apply congrArg
      exact Finset.sum_congr rfl fun q hq ↦ hprofileMass z hz q hq
    · intro q hq
      exact measure_ne_top incrementLaw (profileTail z q)
  · intro z hz
    apply ENNReal.mul_ne_top
    · rw [firstExitAtWeight_eq_measure (squareDisk R : Set Site)
        start z (hexit z hz)]
      exact measure_ne_top incrementLaw
        (firstExitAtEvent (squareDisk R : Set Site) start z)
    · exact ENNReal.sum_ne_top.2 fun q hq ↦
        measure_ne_top incrementLaw (profileTail z q)

/-- The exact continuation coefficient attached to an actual profile-tail
event.  It records the discrepancy between the auxiliary birth-death
profile weight and the literal simple-random-walk tail mass. -/
noncomputable def eventProfileContinuation {N : ℕ}
    (n : ℕ) (delta : ℝ)
    (profileTail : Site → NatPath N → Set (ℕ → Direction))
    (z : Site) (q : NatPath N) : ℝ :=
  (incrementLaw (profileTail z q)).toReal /
    successfulProfileWeight n delta q

theorem eventProfileContinuation_nonneg {N n : ℕ} (delta : ℝ)
    (profileTail : Site → NatPath N → Set (ℕ → Direction))
    (z : Site) (q : NatPath N)
    (hprofileWeight : 0 ≤ successfulProfileWeight n delta q) :
    0 ≤ eventProfileContinuation n delta profileTail z q := by
  unfold eventProfileContinuation
  exact div_nonneg ENNReal.toReal_nonneg hprofileWeight

/-- Source-exact form with no assumed profile-mass identity.  For positive
selected auxiliary weights, the canonical continuation coefficient makes
the atom identification algebraic.  Thus the only probabilistic premises
are stopping-time measurability and the literal measurable/disjoint profile
partition. -/
theorem exactStrongMarkovExitKernelExpansion_normalized
    {N n : ℕ} (delta : ℝ)
    (τ : (ℕ → Direction) → ℕ) (outerFiber : Set (ℕ → Direction))
    (R : ℕ) (start : Site) (exitSites : Finset Site)
    (Q : Finset (NatPath N))
    (profileTail : Site → NatPath N → Set (ℕ → Direction))
    (hτ : Measurable τ)
    (houter : ∀ k, MeasurableSet[
      ProbabilityTheory.iidHistory (X := Direction) k]
      (outerFiber ∩ {ω | τ ω = k}))
    (hexit : ∀ z ∈ exitSites, z ∉ squareDisk R)
    (hprofileMeasurable : ∀ z ∈ exitSites, ∀ q ∈ Q,
      MeasurableSet (profileTail z q))
    (hprofileDisjoint : ∀ z ∈ exitSites,
      Set.PairwiseDisjoint (↑Q : Set (NatPath N)) (profileTail z))
    (hprofileWeightPos : ∀ q ∈ Q,
      0 < successfulProfileWeight n delta q) :
    incrementLaw.real
        (annularProfileFiber Q
          (sourceStoppedAnnularProfileAtom τ R start exitSites profileTail) ∩
            outerFiber) =
      annularProfileKernelMass n delta Q R start exitSites
          (eventProfileContinuation n delta profileTail) *
        incrementLaw.real outerFiber := by
  apply exactStrongMarkovExitKernelExpansion delta τ outerFiber R start
    exitSites Q profileTail (eventProfileContinuation n delta profileTail)
    hτ houter hexit hprofileMeasurable hprofileDisjoint
  intro z hz q hq
  unfold eventProfileContinuation
  exact (mul_div_cancel₀ _ (ne_of_gt (hprofileWeightPos q hq))).symm

theorem successfulProfileWeight_nonneg {N n : ℕ} (delta : ℝ)
    (hn : 2 ≤ n) (q : NatPath N) :
    0 ≤ successfulProfileWeight n delta q := by
  unfold successfulProfileWeight
  have hi : 0 ≤ initialUpcrossingMass (q 0) := by
    rw [initialUpcrossingMass_eq]
    positivity
  exact mul_nonneg
    (mul_nonneg hi (halfNegBinPathWeight_nonneg q))
    (terminalMass_nonneg delta hn)

theorem annularProfileKernelMass_nonneg {N n : ℕ} (delta : ℝ)
    (hn : 2 ≤ n) (Q : Finset (NatPath N))
    (R : ℕ) (start : Site) (exitSites : Finset Site)
    (continuation : Site → NatPath N → ℝ)
    (hcontinuation : ∀ z ∈ exitSites, ∀ q ∈ Q, 0 ≤ continuation z q) :
    0 ≤ annularProfileKernelMass n delta Q R start exitSites continuation := by
  unfold annularProfileKernelMass
  apply Finset.sum_nonneg
  intro z hz
  apply mul_nonneg ENNReal.toReal_nonneg
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (successfulProfileWeight_nonneg delta hn q)
    (hcontinuation z hz q hq)

/-- Potential-kernel oscillation bounds compare the complete finite profile
mass, not merely one boundary atom. -/
theorem annularProfileKernelMass_le_of_potential_boundary
    {N n R : ℕ} {delta : ℝ} (hn : 2 ≤ n)
    (Q : Finset (NatPath N)) (exitSites : Finset Site)
    (continuation : Site → NatPath N → ℝ)
    {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    {x x' : Site} (hx : x ∈ squareDisk R) (hx' : x' ∈ squareDisk R)
    (lowerBoundary upperBoundary : Site → ℝ)
    (denominatorLower : Site → ℝ) {error : ℝ}
    (hcontinuation : ∀ z ∈ exitSites, ∀ q ∈ Q, 0 ≤ continuation z q)
    (hexit : ∀ z ∈ exitSites, z ∉ squareDisk R)
    (hdenominatorLower : ∀ z ∈ exitSites, 0 < denominatorLower z)
    (hden : ∀ z ∈ exitSites,
      denominatorLower z ≤ squareGreenExitKernel R x' z)
    (hboundary : ∀ z ∈ exitSites, ∀ d : Direction,
      z - directionStep d ∈ squareDisk R →
      ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
        lowerBoundary (z - directionStep d) ≤
            a (w - (z - directionStep d)) ∧
          a (w - (z - directionStep d)) ≤
            upperBoundary (z - directionStep d))
    (hoscillation : ∀ z ∈ exitSites,
      (squareExitPotentialDifference R a x x' z +
        squareExitBoundaryPotentialRange R lowerBoundary upperBoundary z) /
          denominatorLower z ≤ error) :
    annularProfileKernelMass n delta Q R x exitSites continuation ≤
      (1 + error) *
        annularProfileKernelMass n delta Q R x' exitSites continuation := by
  unfold annularProfileKernelMass
  calc
    (∑ z ∈ exitSites,
        (firstExitAtWeight (squareDisk R : Set Site) x z).toReal *
          ∑ q ∈ Q, successfulProfileWeight n delta q * continuation z q) ≤
        ∑ z ∈ exitSites,
          ((1 + error) *
              (firstExitAtWeight (squareDisk R : Set Site) x' z).toReal) *
            ∑ q ∈ Q, successfulProfileWeight n delta q * continuation z q := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_right
      · exact firstExitAtWeight_square_toReal_le_one_add_error_mul
          ha hx hx' lowerBoundary upperBoundary (hexit z hz)
          (hdenominatorLower z hz) (hden z hz) (hboundary z hz)
          (hoscillation z hz)
      · apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (successfulProfileWeight_nonneg delta hn q)
          (hcontinuation z hz q hq)
    _ = (1 + error) *
        ∑ z ∈ exitSites,
          (firstExitAtWeight (squareDisk R : Set Site) x' z).toReal *
            ∑ q ∈ Q, successfulProfileWeight n delta q * continuation z q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring

/-! ### Products of the `m` source excursion kernels -/

/-- The product of the exact first-exit weights along one boundary word of
length `m`. -/
noncomputable def annularExitWordWeight {m : ℕ}
    (radius : Fin m → ℕ) (start exitSite : Fin m → Site) : ℝ :=
  ∏ i : Fin m,
    (firstExitAtWeight (squareDisk (radius i) : Set Site)
      (start i) (exitSite i)).toReal

theorem annularExitWordWeight_nonneg {m : ℕ}
    (radius : Fin m → ℕ) (start exitSite : Fin m → Site) :
    0 ≤ annularExitWordWeight radius start exitSite := by
  unfold annularExitWordWeight
  exact Finset.prod_nonneg fun i hi ↦ ENNReal.toReal_nonneg

/-- Multiplying the pointwise potential-kernel comparisons gives precisely
the `m`-excursion Harnack factor appearing in Lemma A.2. -/
theorem annularExitWordWeight_le_of_potential_boundary
    {m : ℕ} (radius : Fin m → ℕ)
    (actualStart referenceStart exitSite : Fin m → Site)
    {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    (lowerBoundary upperBoundary : Fin m → Site → ℝ)
    (denominatorLower : Fin m → ℝ) {error : ℝ}
    (hactualStart : ∀ i, actualStart i ∈ squareDisk (radius i))
    (hreferenceStart : ∀ i, referenceStart i ∈ squareDisk (radius i))
    (hexit : ∀ i, exitSite i ∉ squareDisk (radius i))
    (hdenominatorLower : ∀ i, 0 < denominatorLower i)
    (hden : ∀ i, denominatorLower i ≤
      squareGreenExitKernel (radius i) (referenceStart i) (exitSite i))
    (hboundary : ∀ i, ∀ d : Direction,
      exitSite i - directionStep d ∈ squareDisk (radius i) →
      ∀ w ∈ squareDisk (radius i + 1), w ∉ squareDisk (radius i) →
        lowerBoundary i (exitSite i - directionStep d) ≤
            a (w - (exitSite i - directionStep d)) ∧
          a (w - (exitSite i - directionStep d)) ≤
            upperBoundary i (exitSite i - directionStep d))
    (hoscillation : ∀ i,
      (squareExitPotentialDifference (radius i) a
          (actualStart i) (referenceStart i) (exitSite i) +
        squareExitBoundaryPotentialRange (radius i)
          (lowerBoundary i) (upperBoundary i) (exitSite i)) /
          denominatorLower i ≤ error) :
    annularExitWordWeight radius actualStart exitSite ≤
      (1 + error) ^ m *
        annularExitWordWeight radius referenceStart exitSite := by
  unfold annularExitWordWeight
  calc
    (∏ i : Fin m,
        (firstExitAtWeight (squareDisk (radius i) : Set Site)
          (actualStart i) (exitSite i)).toReal) ≤
        ∏ i : Fin m,
          ((1 + error) *
            (firstExitAtWeight (squareDisk (radius i) : Set Site)
              (referenceStart i) (exitSite i)).toReal) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact ENNReal.toReal_nonneg
      · intro i hi
        exact firstExitAtWeight_square_toReal_le_one_add_error_mul ha
          (hactualStart i) (hreferenceStart i)
          (lowerBoundary i) (upperBoundary i) (hexit i)
          (hdenominatorLower i) (hden i) (hboundary i) (hoscillation i)
    _ = (1 + error) ^ m *
        ∏ i : Fin m,
          (firstExitAtWeight (squareDisk (radius i) : Set Site)
            (referenceStart i) (exitSite i)).toReal := by
      rw [Finset.prod_mul_distrib]
      simp

/-- A finite mixture of boundary words and Appendix-A profile atoms. -/
noncomputable def annularProfileWordKernelMass {β : Type*} {N m : ℕ}
    (n : ℕ) (delta : ℝ) (Q : Finset (NatPath N)) (words : Finset β)
    (radius : β → Fin m → ℕ) (start exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ) : ℝ :=
  ∑ b ∈ words,
    annularExitWordWeight (radius b) (start b) (exitSite b) *
      ∑ q ∈ Q, successfulProfileWeight n delta q * continuation b q

theorem annularProfileWordKernelMass_le_of_potential_boundary
    {β : Type*} {N n m : ℕ} {delta : ℝ} (hn : 2 ≤ n)
    (Q : Finset (NatPath N)) (words : Finset β)
    (radius : β → Fin m → ℕ)
    (actualStart referenceStart exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ)
    {a : Site → ℝ} (ha : IsPlanarPotentialKernel a)
    (lowerBoundary upperBoundary : β → Fin m → Site → ℝ)
    (denominatorLower : β → Fin m → ℝ) {error : ℝ}
    (hcontinuation : ∀ b ∈ words, ∀ q ∈ Q, 0 ≤ continuation b q)
    (hactualStart : ∀ b ∈ words, ∀ i,
      actualStart b i ∈ squareDisk (radius b i))
    (hreferenceStart : ∀ b ∈ words, ∀ i,
      referenceStart b i ∈ squareDisk (radius b i))
    (hexit : ∀ b ∈ words, ∀ i,
      exitSite b i ∉ squareDisk (radius b i))
    (hdenominatorLower : ∀ b ∈ words, ∀ i,
      0 < denominatorLower b i)
    (hden : ∀ b ∈ words, ∀ i, denominatorLower b i ≤
      squareGreenExitKernel (radius b i) (referenceStart b i) (exitSite b i))
    (hboundary : ∀ b ∈ words, ∀ i, ∀ d : Direction,
      exitSite b i - directionStep d ∈ squareDisk (radius b i) →
      ∀ w ∈ squareDisk (radius b i + 1), w ∉ squareDisk (radius b i) →
        lowerBoundary b i (exitSite b i - directionStep d) ≤
            a (w - (exitSite b i - directionStep d)) ∧
          a (w - (exitSite b i - directionStep d)) ≤
            upperBoundary b i (exitSite b i - directionStep d))
    (hoscillation : ∀ b ∈ words, ∀ i,
      (squareExitPotentialDifference (radius b i) a
          (actualStart b i) (referenceStart b i) (exitSite b i) +
        squareExitBoundaryPotentialRange (radius b i)
          (lowerBoundary b i) (upperBoundary b i) (exitSite b i)) /
          denominatorLower b i ≤ error) :
    annularProfileWordKernelMass n delta Q words radius actualStart exitSite
        continuation ≤
      (1 + error) ^ m *
        annularProfileWordKernelMass n delta Q words radius referenceStart exitSite
          continuation := by
  unfold annularProfileWordKernelMass
  calc
    (∑ b ∈ words,
        annularExitWordWeight (radius b) (actualStart b) (exitSite b) *
          ∑ q ∈ Q, successfulProfileWeight n delta q * continuation b q) ≤
        ∑ b ∈ words,
          ((1 + error) ^ m *
            annularExitWordWeight (radius b) (referenceStart b) (exitSite b)) *
              ∑ q ∈ Q,
                successfulProfileWeight n delta q * continuation b q := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right
      · exact annularExitWordWeight_le_of_potential_boundary
          (radius b) (actualStart b) (referenceStart b) (exitSite b) ha
          (lowerBoundary b) (upperBoundary b) (denominatorLower b)
          (hactualStart b hb) (hreferenceStart b hb) (hexit b hb)
          (hdenominatorLower b hb) (hden b hb) (hboundary b hb)
          (hoscillation b hb)
      · apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (successfulProfileWeight_nonneg delta hn q)
          (hcontinuation b hb q hq)
    _ = (1 + error) ^ m *
        ∑ b ∈ words,
          annularExitWordWeight (radius b) (referenceStart b) (exitSite b) *
            ∑ q ∈ Q, successfulProfileWeight n delta q * continuation b q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-! ## Complete source-shaped reduction -/

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- A checked source-shaped reduction of Proposition A.3(2).

The premise `hExactStrongMarkovExitKernelExpansion` is structural: it is the
exact strong-Markov expansion of a concrete annular profile fiber in the
first-exit weights defined in `Erdos1166HLOZHarnack`.  All quantitative
Harnack input is then reduced to the displayed potential-kernel oscillation
and denominator bounds.  The generic truncation-cover and outer-fiber-sum
premises of `HLOZAppendixATwoPoint` no longer occur. -/
theorem propA3_twoPoint_input_of_source_profiles_and_potential_boundary
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N profileN : ℕ} (hprofileN : 2 ≤ profileN) (delta : ℝ)
    (U : Finset ι) (A : ι → Set Ω) (level : ι → ι → ℕ) (L cutoff : ℕ)
    (profiles : ι → ι → ℕ → Finset (NatPath N))
    (innerAtom : ι → ι → ℕ → NatPath N → Set Ω)
    (outerEvent : ι → ι → Set Ω) (excursionCount : ι → ι → Ω → ℕ)
    (innerBound : ι → ι → ℝ)
    (radius : ι → ι → ℕ → ℕ)
    (actualStart referenceStart : ι → ι → ℕ → Site)
    (exitSites : ι → ι → ℕ → Finset Site)
    (continuation : ι → ι → ℕ → Site → NatPath N → ℝ)
    (a : Site → ℝ) (ha : IsPlanarPotentialKernel a)
    (lowerBoundary upperBoundary : ι → ι → ℕ → Site → ℝ)
    (denominatorLower : ι → ι → ℕ → Site → ℝ)
    {kernelError Eh Ei Eo Et E : ℝ}
    (hkernelFactor0 : 0 ≤ 1 + kernelError)
    (hinnerBound0 : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L → 0 ≤ innerBound x y)
    (houterMeasurable : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      MeasurableSet (outerEvent x y))
    (hcountMeasurable : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      Measurable (excursionCount x y))
    (hcontinuation : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, ∀ z ∈ exitSites x y m,
        ∀ q ∈ profiles x y m, 0 ≤ continuation x y m z q)
    (hactualStart : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, actualStart x y m ∈ squareDisk (radius x y m))
    (hreferenceStart : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, referenceStart x y m ∈ squareDisk (radius x y m))
    (hexit : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, ∀ z ∈ exitSites x y m,
        z ∉ squareDisk (radius x y m))
    (hdenominatorLower : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, ∀ z ∈ exitSites x y m,
        0 < denominatorLower x y m z)
    (hden : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, ∀ z ∈ exitSites x y m,
        denominatorLower x y m z ≤
          squareGreenExitKernel (radius x y m) (referenceStart x y m) z)
    (hboundary : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, ∀ z ∈ exitSites x y m, ∀ d : Direction,
        z - directionStep d ∈ squareDisk (radius x y m) →
        ∀ w ∈ squareDisk (radius x y m + 1),
          w ∉ squareDisk (radius x y m) →
          lowerBoundary x y m (z - directionStep d) ≤
              a (w - (z - directionStep d)) ∧
            a (w - (z - directionStep d)) ≤
              upperBoundary x y m (z - directionStep d))
    (hoscillation : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff, ∀ z ∈ exitSites x y m,
        (squareExitPotentialDifference (radius x y m) a
            (actualStart x y m) (referenceStart x y m) z +
          squareExitBoundaryPotentialRange (radius x y m)
            (lowerBoundary x y m) (upperBoundary x y m) z) /
            denominatorLower x y m z ≤ kernelError)
    (hExactStrongMarkovExitKernelExpansion :
      ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff,
        μ.real (annularProfileFiber (profiles x y m) (innerAtom x y m) ∩
          countedOuterFiber (outerEvent x y) (excursionCount x y) m) =
          annularProfileKernelMass profileN delta (profiles x y m)
              (radius x y m) (actualStart x y m) (exitSites x y m)
              (continuation x y m) *
            μ.real (countedOuterFiber (outerEvent x y)
              (excursionCount x y) m))
    (hReferenceInnerProfileMass :
      ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      ∀ m ≤ cutoff,
        annularProfileKernelMass profileN delta (profiles x y m)
            (radius x y m) (referenceStart x y m) (exitSites x y m)
            (continuation x y m) ≤ innerBound x y)
    (hHarnackFactor : 1 + kernelError ≤ Real.exp Eh)
    (hTruncatedInnerFirstMoment : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      innerBound x y ≤
        Real.exp (2 * (level x y : ℝ) + Ei) * μ.real (A y))
    (hOuterProfileFirstMoment : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (outerEvent x y) ≤ Real.exp Eo * μ.real (A x))
    (hDiscardedExcursionTail : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (discardedAnnularTail (A x) (A y)
        (truncatedAnnularPair (profiles x y) (innerAtom x y)
          (outerEvent x y) (excursionCount x y) cutoff)) ≤
        Real.exp (2 * (level x y : ℝ) + Et) *
          μ.real (A x) * μ.real (A y))
    (hErrorBudget : Real.exp (Eh + Ei + Eo) + Real.exp Et ≤ Real.exp E) :
    ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (A x ∩ A y) ≤
        Real.exp (2 * (level x y : ℝ) + E) *
          μ.real (A x) * μ.real (A y) := by
  intro x hx y hy hxy
  let truncated := truncatedAnnularPair (profiles x y) (innerAtom x y)
    (outerEvent x y) (excursionCount x y) cutoff
  let tail := discardedAnnularTail (A x) (A y) truncated
  let innerFiber : ℕ → Set Ω := fun m ↦
    annularProfileFiber (profiles x y m) (innerAtom x y m)
  let outerFiber : ℕ → Set Ω := fun m ↦
    countedOuterFiber (outerEvent x y) (excursionCount x y) m
  have hconditional : ∀ m ≤ cutoff,
      μ.real (innerFiber m ∩ outerFiber m) ≤
        (1 + kernelError) * innerBound x y * μ.real (outerFiber m) := by
    intro m hm
    have hmass := annularProfileKernelMass_le_of_potential_boundary
      (delta := delta) hprofileN (profiles x y m) (exitSites x y m)
      (continuation x y m) ha
      (hactualStart x hx y hy hxy m hm)
      (hreferenceStart x hx y hy hxy m hm)
      (lowerBoundary x y m) (upperBoundary x y m)
      (denominatorLower x y m)
      (hcontinuation x hx y hy hxy m hm)
      (hexit x hx y hy hxy m hm)
      (hdenominatorLower x hx y hy hxy m hm)
      (hden x hx y hy hxy m hm)
      (hboundary x hx y hy hxy m hm)
      (hoscillation x hx y hy hxy m hm)
    have houter0 : 0 ≤ μ.real (outerFiber m) := measureReal_nonneg
    calc
      μ.real (innerFiber m ∩ outerFiber m) =
          annularProfileKernelMass profileN delta (profiles x y m)
              (radius x y m) (actualStart x y m) (exitSites x y m)
              (continuation x y m) * μ.real (outerFiber m) :=
        hExactStrongMarkovExitKernelExpansion x hx y hy hxy m hm
      _ ≤ ((1 + kernelError) *
          annularProfileKernelMass profileN delta (profiles x y m)
            (radius x y m) (referenceStart x y m) (exitSites x y m)
            (continuation x y m)) * μ.real (outerFiber m) :=
        mul_le_mul_of_nonneg_right hmass houter0
      _ ≤ ((1 + kernelError) * innerBound x y) * μ.real (outerFiber m) := by
        apply mul_le_mul_of_nonneg_right _ houter0
        exact mul_le_mul_of_nonneg_left
          (hReferenceInnerProfileMass x hx y hy hxy m hm) hkernelFactor0
      _ = (1 + kernelError) * innerBound x y * μ.real (outerFiber m) := rfl
  exact propA3_twoPoint_of_conditional_decoupling μ
    (A x) (A y) truncated tail innerFiber outerFiber cutoff (level x y)
    hkernelFactor0 (hinnerBound0 x hx y hy hxy) measureReal_nonneg
    (pair_subset_truncated_union_discardedTail (A x) (A y) truncated)
    (truncatedAnnularPair_fiber_cover (profiles x y) (innerAtom x y)
      (outerEvent x y) (excursionCount x y) cutoff)
    hconditional
    (sum_countedOuterFiber_le μ cutoff
      (houterMeasurable x hx y hy hxy) (hcountMeasurable x hx y hy hxy))
    hHarnackFactor (hTruncatedInnerFirstMoment x hx y hy hxy)
    (hOuterProfileFirstMoment x hx y hy hxy)
    (hDiscardedExcursionTail x hx y hy hxy) hErrorBudget

/-- Source-faithful `m`-excursion version of the preceding reduction.

Unlike the one-exit convenience interface, the Harnack multiplier here is
derived as `(1+kernelError)^m` on the fiber where the annular count is `m`,
and is then bounded by `(1+kernelError)^cutoff`.  This is the finite exact
counterpart of the `1+O(m n⁻³ log n)` factor in HLOZ Lemma A.2.  The event
split uses an explicit bounded-count/profile-cover premise, so the discarded
tail is exactly the large-count event estimated in (A.14). -/
theorem propA3_twoPoint_of_source_exit_words_and_potential_boundary
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {β : Type*} {N profileN : ℕ} (hprofileN : 2 ≤ profileN) (delta : ℝ)
    (Ax Ay outer : Set Ω) (count : Ω → ℕ) (cutoff l : ℕ)
    (profiles : ℕ → Finset (NatPath N))
    (innerAtom : ℕ → NatPath N → Set Ω)
    (words : ℕ → Finset β)
    (radius : (m : ℕ) → β → Fin m → ℕ)
    (actualStart referenceStart exitSite :
      (m : ℕ) → β → Fin m → Site)
    (continuation : ℕ → β → NatPath N → ℝ)
    (a : Site → ℝ) (ha : IsPlanarPotentialKernel a)
    (lowerBoundary upperBoundary :
      (m : ℕ) → β → Fin m → Site → ℝ)
    (denominatorLower : (m : ℕ) → β → Fin m → ℝ)
    {innerBound kernelError Eh Ei Eo Et E : ℝ}
    (hkernelError0 : 0 ≤ kernelError) (hinnerBound0 : 0 ≤ innerBound)
    (houterMeasurable : MeasurableSet outer) (hcountMeasurable : Measurable count)
    (hBoundedCountInclusion :
      Ax ∩ Ay ∩ {ω | count ω ≤ cutoff} ⊆
        truncatedAnnularPair profiles innerAtom outer count cutoff)
    (hcontinuation : ∀ m ≤ cutoff, ∀ b ∈ words m,
      ∀ q ∈ profiles m, 0 ≤ continuation m b q)
    (hactualStart : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
      actualStart m b i ∈ squareDisk (radius m b i))
    (hreferenceStart : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
      referenceStart m b i ∈ squareDisk (radius m b i))
    (hexit : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
      exitSite m b i ∉ squareDisk (radius m b i))
    (hdenominatorLower : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
      0 < denominatorLower m b i)
    (hden : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
      denominatorLower m b i ≤
        squareGreenExitKernel (radius m b i)
          (referenceStart m b i) (exitSite m b i))
    (hboundary : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i, ∀ d : Direction,
      exitSite m b i - directionStep d ∈ squareDisk (radius m b i) →
      ∀ w ∈ squareDisk (radius m b i + 1),
        w ∉ squareDisk (radius m b i) →
        lowerBoundary m b i (exitSite m b i - directionStep d) ≤
            a (w - (exitSite m b i - directionStep d)) ∧
          a (w - (exitSite m b i - directionStep d)) ≤
            upperBoundary m b i (exitSite m b i - directionStep d))
    (hoscillation : ∀ m ≤ cutoff, ∀ b ∈ words m, ∀ i,
      (squareExitPotentialDifference (radius m b i) a
          (actualStart m b i) (referenceStart m b i) (exitSite m b i) +
        squareExitBoundaryPotentialRange (radius m b i)
          (lowerBoundary m b i) (upperBoundary m b i) (exitSite m b i)) /
          denominatorLower m b i ≤ kernelError)
    (hExactStrongMarkovExitWordExpansion : ∀ m ≤ cutoff,
      μ.real (annularProfileFiber (profiles m) (innerAtom m) ∩
        countedOuterFiber outer count m) =
        annularProfileWordKernelMass profileN delta (profiles m) (words m)
            (radius m) (actualStart m) (exitSite m) (continuation m) *
          μ.real (countedOuterFiber outer count m))
    (hReferenceInnerProfileMass : ∀ m ≤ cutoff,
      annularProfileWordKernelMass profileN delta (profiles m) (words m)
          (radius m) (referenceStart m) (exitSite m) (continuation m) ≤
        innerBound)
    (hHarnackFactor : (1 + kernelError) ^ cutoff ≤ Real.exp Eh)
    (hTruncatedInnerFirstMoment :
      innerBound ≤ Real.exp (2 * (l : ℝ) + Ei) * μ.real Ay)
    (hOuterProfileFirstMoment : μ.real outer ≤ Real.exp Eo * μ.real Ax)
    (hDiscardedExcursionTail :
      μ.real (largeCountPairTail Ax Ay count cutoff) ≤
          Real.exp (2 * (l : ℝ) + Et) * μ.real Ax * μ.real Ay)
    (hErrorBudget : Real.exp (Eh + Ei + Eo) + Real.exp Et ≤ Real.exp E) :
    μ.real (Ax ∩ Ay) ≤
      Real.exp (2 * (l : ℝ) + E) * μ.real Ax * μ.real Ay := by
  let truncated := truncatedAnnularPair profiles innerAtom outer count cutoff
  let tail := largeCountPairTail Ax Ay count cutoff
  let innerFiber : ℕ → Set Ω := fun m ↦
    annularProfileFiber (profiles m) (innerAtom m)
  let outerFiber : ℕ → Set Ω := fun m ↦ countedOuterFiber outer count m
  have hfactor0 : 0 ≤ (1 + kernelError) ^ cutoff := by positivity
  have hconditional : ∀ m ≤ cutoff,
      μ.real (innerFiber m ∩ outerFiber m) ≤
        (1 + kernelError) ^ cutoff * innerBound * μ.real (outerFiber m) := by
    intro m hm
    have hmass := annularProfileWordKernelMass_le_of_potential_boundary
      (delta := delta) hprofileN (profiles m) (words m) (radius m)
      (actualStart m) (referenceStart m) (exitSite m) (continuation m) ha
      (lowerBoundary m) (upperBoundary m) (denominatorLower m)
      (hcontinuation m hm) (hactualStart m hm) (hreferenceStart m hm)
      (hexit m hm) (hdenominatorLower m hm) (hden m hm)
      (hboundary m hm) (hoscillation m hm)
    have hpow : (1 + kernelError) ^ m ≤ (1 + kernelError) ^ cutoff := by
      exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + kernelError) hm
    have hmassCutoff :
        annularProfileWordKernelMass profileN delta (profiles m) (words m)
            (radius m) (actualStart m) (exitSite m) (continuation m) ≤
          (1 + kernelError) ^ cutoff *
            annularProfileWordKernelMass profileN delta (profiles m) (words m)
              (radius m) (referenceStart m) (exitSite m) (continuation m) := by
      calc
        annularProfileWordKernelMass profileN delta (profiles m) (words m)
            (radius m) (actualStart m) (exitSite m) (continuation m) ≤
            (1 + kernelError) ^ m *
              annularProfileWordKernelMass profileN delta (profiles m) (words m)
                (radius m) (referenceStart m) (exitSite m) (continuation m) := hmass
        _ ≤ (1 + kernelError) ^ cutoff *
              annularProfileWordKernelMass profileN delta (profiles m) (words m)
                (radius m) (referenceStart m) (exitSite m) (continuation m) := by
          apply mul_le_mul_of_nonneg_right hpow
          unfold annularProfileWordKernelMass
          apply Finset.sum_nonneg
          intro b hb
          apply mul_nonneg (annularExitWordWeight_nonneg _ _ _)
          apply Finset.sum_nonneg
          intro q hq
          exact mul_nonneg (successfulProfileWeight_nonneg delta hprofileN q)
            (hcontinuation m hm b hb q hq)
    have houter0 : 0 ≤ μ.real (outerFiber m) := measureReal_nonneg
    calc
      μ.real (innerFiber m ∩ outerFiber m) =
          annularProfileWordKernelMass profileN delta (profiles m) (words m)
              (radius m) (actualStart m) (exitSite m) (continuation m) *
            μ.real (outerFiber m) :=
        hExactStrongMarkovExitWordExpansion m hm
      _ ≤ ((1 + kernelError) ^ cutoff *
          annularProfileWordKernelMass profileN delta (profiles m) (words m)
            (radius m) (referenceStart m) (exitSite m) (continuation m)) *
          μ.real (outerFiber m) :=
        mul_le_mul_of_nonneg_right hmassCutoff houter0
      _ ≤ ((1 + kernelError) ^ cutoff * innerBound) *
          μ.real (outerFiber m) := by
        apply mul_le_mul_of_nonneg_right _ houter0
        exact mul_le_mul_of_nonneg_left
          (hReferenceInnerProfileMass m hm) hfactor0
      _ = (1 + kernelError) ^ cutoff * innerBound * μ.real (outerFiber m) := rfl
  exact propA3_twoPoint_of_conditional_decoupling μ Ax Ay truncated tail
    innerFiber outerFiber cutoff l hfactor0 hinnerBound0 measureReal_nonneg
    (pair_subset_truncated_union_largeCountPairTail Ax Ay truncated count cutoff
      hBoundedCountInclusion)
    (truncatedAnnularPair_fiber_cover profiles innerAtom outer count cutoff)
    hconditional
    (sum_countedOuterFiber_le μ cutoff houterMeasurable hcountMeasurable)
    hHarnackFactor hTruncatedInnerFirstMoment hOuterProfileFirstMoment
    hDiscardedExcursionTail hErrorBudget

end Erdos1166.HLOZAppendixATwoPointSource
