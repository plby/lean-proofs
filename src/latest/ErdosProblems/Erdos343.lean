/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the all-N formulation of Erdős Problem 343.
https://www.erdosproblems.com/343

Following the cited source, a locally finite infinite multiset is represented
by a nondecreasing sequence. Distinct indices are distinct occurrences,
including when their values are equal. Infinite multiplicity at one value is
the separate immediate case, since its multiples already form an infinite AP.

The displayed problem asks for a universal linear-density threshold and
requires its counting estimate for every N. With this all-N quantifier, the
threshold C = 1 is enough: the nth term is at most n + 1, so Brown's criterion
shows that every natural number is a finite subset sum.

The stronger published Szemerédi--Vu theorem only assumes the counting bound
for all sufficiently large N. Its proof needs their deep finite sumset theorem;
the distinction and the full published proof chain are documented in
tex/343.tex.
-/
import Mathlib

namespace Erdos343

open scoped BigOperators

/-- Finite subset sums of an infinite multiset represented by indexed occurrences. -/
def SubsetSums (A : ℕ → ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, n = ∑ i ∈ s, A i}

/-- A set contains an infinite arithmetic progression with positive difference. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ S

/-- The occurrence-indexed multiset `A` is subcomplete. -/
def IsSubcomplete (A : ℕ → ℕ) : Prop :=
  ContainsInfiniteAP (SubsetSums A)

/--
There are at least `C * N` occurrences of the multiset with value at most `N`.

The finite set is a set of occurrence indices, so repetitions of a value are
counted separately. Finite witnesses also make the definition meaningful when
a value has infinitely many occurrences.
-/
def HasLinearCountingLowerBound (C : ℕ) (A : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ s : Finset ℕ, C * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N

/-- Brown's finite-interval argument for occurrence-indexed subset sums. -/
private lemma brownsCriterion {f : ℕ → ℕ} (hmono : Monotone f) (hzero : f 0 = 1)
    (hgap : ∀ n, f (n + 1) ≤ 1 + ∑ i ∈ Finset.range (n + 1), f i) :
    ∀ n, ∃ s : Finset ℕ, n = ∑ i ∈ s, f i := by
  intro n
  let partialSum : ℕ → ℕ := fun k => ∑ i ∈ Finset.range (k + 1), f i
  have hinterval :
      ∀ k, ∀ m ≤ partialSum k,
        ∃ s : Finset ℕ, s ⊆ Finset.range (k + 1) ∧ m = ∑ i ∈ s, f i := by
    intro k
    induction k with
    | zero =>
        intro m hm
        cases m with
        | zero => exact ⟨∅, by simp⟩
        | succ m =>
            have hmle : m + 1 ≤ 1 := by
              simpa [partialSum, hzero] using hm
            have hmzero : m = 0 := by omega
            subst m
            exact ⟨{0}, by simp [hzero]⟩
    | succ k ih =>
        intro m hm
        by_cases hold : m ≤ partialSum k
        · obtain ⟨s, hsrange, hssum⟩ := ih m hold
          exact ⟨s, hsrange.trans (Finset.range_mono (Nat.le_succ _)), hssum⟩
        · have hsub : m - f (k + 1) ≤ partialSum k := by
            simp only [partialSum, Finset.sum_range_succ] at hm ⊢
            omega
          obtain ⟨s, hsrange, hssum⟩ := ih (m - f (k + 1)) hsub
          refine ⟨s ∪ {k + 1}, ?_, ?_⟩
          · intro i hi
            simp only [Finset.mem_union, Finset.mem_singleton] at hi
            rcases hi with hi | rfl
            · exact Finset.mem_range.mpr
                (lt_of_lt_of_le (Finset.mem_range.mp (hsrange hi)) (Nat.le_succ _))
            · simp
          · have hle : f (k + 1) ≤ m := by
              have hnotle : partialSum k < m := Nat.lt_of_not_ge hold
              have hfgap : f (k + 1) ≤ partialSum k + 1 := by
                simpa [partialSum, add_comm] using hgap k
              omega
            have hnotmem : k + 1 ∉ s := by
              intro hmem
              have := Finset.mem_range.mp (hsrange hmem)
              omega
            rw [Finset.sum_union]
            · simp only [Finset.sum_singleton]
              rw [← hssum]
              exact (Nat.sub_add_cancel hle).symm
            · simp [Finset.disjoint_singleton_right, hnotmem]
  have hlarge : ∃ k, n ≤ partialSum k := by
    refine ⟨n, ?_⟩
    calc
      n ≤ n + 1 := Nat.le_succ n
      _ = ∑ _i ∈ Finset.range (n + 1), 1 := by simp
      _ ≤ ∑ i ∈ Finset.range (n + 1), f i := by
        exact Finset.sum_le_sum fun i _hi => by
          have := hmono (Nat.zero_le i)
          omega
  obtain ⟨k, hk⟩ := hlarge
  obtain ⟨s, _hsrange, hs⟩ := hinterval k n hk
  exact ⟨s, hs⟩

/-- Under the coefficient-one all-N counting bound, every natural is a subset sum. -/
lemma subsetSums_eq_univ_of_countingLowerBound_one
    (A : ℕ → ℕ) (hmono : Monotone A) (hpos : ∀ i, 0 < A i)
    (hcount : HasLinearCountingLowerBound 1 A) :
    SubsetSums A = Set.univ := by
  have hpointwise : ∀ i : ℕ, A i ≤ i + 1 := by
    intro i
    obtain ⟨s, hcard, hs⟩ := hcount (i + 1)
    have hexists : ∃ j ∈ s, i ≤ j := by
      by_contra h
      push Not at h
      have hsubset : s ⊆ Finset.range i := by
        intro j hj
        exact Finset.mem_range.mpr (h j hj)
      have hcardle := Finset.card_le_card hsubset
      simp only [Finset.card_range] at hcardle
      omega
    obtain ⟨j, hjs, hij⟩ := hexists
    exact (hmono hij).trans (hs j hjs)
  have hzero : A 0 = 1 := by
    have hle := hpointwise 0
    have hgt := hpos 0
    omega
  have hgap : ∀ n : ℕ, A (n + 1) ≤ 1 + ∑ i ∈ Finset.range (n + 1), A i := by
    intro n
    have hsum : n + 1 ≤ ∑ i ∈ Finset.range (n + 1), A i := by
      calc
        n + 1 = ∑ _i ∈ Finset.range (n + 1), 1 := by simp
        _ ≤ ∑ i ∈ Finset.range (n + 1), A i := by
          exact Finset.sum_le_sum fun i _hi => hpos i
    have hnext := hpointwise (n + 1)
    omega
  apply Set.eq_univ_of_forall
  intro n
  obtain ⟨s, hs⟩ := brownsCriterion hmono hzero hgap n
  exact ⟨s, hs⟩

/--
Resolution of the all-N formulation of Erdős Problem 343.

There is a universal positive density threshold such that every nondecreasing
multiset of positive integers satisfying the corresponding counting bound for
every `N` is subcomplete.
-/
theorem erdos_343 :
    ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
      Monotone A →
      (∀ i, 0 < A i) →
      HasLinearCountingLowerBound C A →
      IsSubcomplete A := by
  refine ⟨1, by omega, ?_⟩
  intro A hmono hpos hcount
  have hall : SubsetSums A = Set.univ :=
    subsetSums_eq_univ_of_countingLowerBound_one A hmono hpos hcount
  refine ⟨0, 1, by omega, ?_⟩
  intro k
  rw [hall]
  simp

#print axioms erdos_343

end Erdos343
