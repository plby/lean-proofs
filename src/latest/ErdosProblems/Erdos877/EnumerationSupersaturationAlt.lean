/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos877.EnumerationSupersaturation

/-!
# A rank-form supersaturation bound for Schur triples

This is an independent aggregation of the reflection estimate proved in
`EnumerationSupersaturation`.  If `A \subseteq {1, ..., n}`, put
`d = 2 |A| - n` and `r = \lfloor d/2\rfloor`.  We prove the completely finite
inequality

`r^2 \le 2 e(A) + 3 r`,

where `e(A)` is the number of unordered Schur triples with distinct summands.
Consequently `e(A) = o(n^2)` forces `|A| \le n/2 + o(n)`.  The loss of the
diagonal triples `x+x=2x` is absorbed by the additive `2r` term.
-/

open Finset

namespace Erdos877
namespace EnumerationAlt

open Enumeration

/-- Entries of `A` strictly above `z`. -/
noncomputable def above (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  A.filter (fun x ↦ z < x)

@[simp] theorem mem_above {A : Finset ℕ} {z x : ℕ} :
    x ∈ above A z ↔ x ∈ A ∧ z < x := by
  classical
  simp [above]

/-- The increasing enumeration of a finite set. -/
noncomputable def entry (A : Finset ℕ) : Fin A.card → ℕ :=
  A.orderEmbOfFin rfl

@[simp] theorem entry_mem (A : Finset ℕ) (i : Fin A.card) :
    entry A i ∈ A := by
  simp [entry]

theorem entry_strictMono (A : Finset ℕ) : StrictMono (entry A) :=
  (A.orderEmbOfFin rfl).strictMono

/-- Exactly `i` entries precede the entry of rank `i`. -/
theorem card_below_entry (A : Finset ℕ) (i : Fin A.card) :
    (below A (entry A i)).card = i := by
  classical
  let f : Fin A.card ↪ ℕ := (A.orderEmbOfFin rfl).toEmbedding
  have hset : below A (entry A i) =
      (Finset.Iio i).map f := by
    ext x
    simp only [mem_below, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hxA, hxi⟩
      obtain ⟨j, rfl⟩ := by
        have : x ∈ Set.range (A.orderEmbOfFin rfl) := by
          simpa [Finset.range_orderEmbOfFin] using hxA
        exact this
      refine ⟨j, ?_, rfl⟩
      exact (entry_strictMono A).lt_iff_lt.mp hxi
    · rintro ⟨j, hji, rfl⟩
      exact ⟨entry_mem A j, (entry_strictMono A hji)⟩
  rw [hset, Finset.card_map]
  simp

/-- Exactly the remaining `|A|-i-1` entries follow the entry of rank `i`. -/
theorem card_above_entry (A : Finset ℕ) (i : Fin A.card) :
    (above A (entry A i)).card = A.card - i - 1 := by
  classical
  let f : Fin A.card ↪ ℕ := (A.orderEmbOfFin rfl).toEmbedding
  have hset : above A (entry A i) =
      (Finset.Ioi i).map f := by
    ext x
    simp only [mem_above, Finset.mem_map, Finset.mem_Ioi]
    constructor
    · rintro ⟨hxA, hix⟩
      obtain ⟨j, rfl⟩ := by
        have : x ∈ Set.range (A.orderEmbOfFin rfl) := by
          simpa [Finset.range_orderEmbOfFin] using hxA
        exact this
      refine ⟨j, ?_, rfl⟩
      exact (entry_strictMono A).lt_iff_lt.mp hix
    · rintro ⟨j, hij, rfl⟩
      exact ⟨entry_mem A j, (entry_strictMono A hij)⟩
  rw [hset, Finset.card_map, Fin.card_Ioi]
  omega

/-- The rank-`i` entry cannot be too far to the right in `[1,n]`. -/
theorem entry_add_card_le (A : Finset ℕ) (n : ℕ) (hA : A ⊆ interval n)
    (i : Fin A.card) :
    A.card + entry A i ≤ n + i + 1 := by
  classical
  have habove : above A (entry A i) ⊆ Finset.Ioc (entry A i) n := by
    intro x hx
    have hx' := mem_above.mp hx
    exact Finset.mem_Ioc.mpr ⟨hx'.2, (mem_interval.mp (hA hx'.1)).2⟩
  have hcard := Finset.card_le_card habove
  rw [card_above_entry] at hcard
  have hie : (i : ℕ) < A.card := i.isLt
  have hzin : entry A i ≤ n := (mem_interval.mp (hA (entry_mem A i))).2
  simp only [Nat.card_Ioc] at hcard
  omega

/-- Pointwise rank form of the reflection estimate. -/
theorem rank_le_add_pairsAt (A : Finset ℕ) (n : ℕ) (hA : A ⊆ interval n)
    (i : Fin A.card) :
    A.card + i ≤ n + 2 * (pairsAt A (entry A i)).card + 3 := by
  have hreflect := two_mul_card_below_le_add_pairsAt A (entry A i)
  rw [card_below_entry] at hreflect
  have hentry := entry_add_card_le A n hA i
  omega

/-- Half of the excess of `A` over `n/2`. -/
def halfExcess (A : Finset ℕ) (n : ℕ) : ℕ :=
  (2 * A.card - n) / 2

/-- The last `halfExcess A n` ranks in the increasing enumeration of `A`. -/
noncomputable def tailRanks (A : Finset ℕ) (n : ℕ) : Finset (Fin A.card) :=
  Finset.univ.filter fun i ↦ A.card - halfExcess A n ≤ i

@[simp] theorem mem_tailRanks {A : Finset ℕ} {n : ℕ} {i : Fin A.card} :
    i ∈ tailRanks A n ↔ A.card - halfExcess A n ≤ i := by
  classical
  simp [tailRanks]

theorem halfExcess_le_card (A : Finset ℕ) (n : ℕ) :
    halfExcess A n ≤ A.card := by
  unfold halfExcess
  omega

/-- Recover the size excess from `halfExcess`, up to the one unit lost by
integer division. -/
theorem two_mul_card_le_add_halfExcess (A : Finset ℕ) (n : ℕ) :
    2 * A.card ≤ n + 2 * halfExcess A n + 1 := by
  unfold halfExcess
  omega

/-- There are exactly `halfExcess A n` selected tail ranks. -/
theorem card_tailRanks (A : Finset ℕ) (n : ℕ) :
    (tailRanks A n).card = halfExcess A n := by
  classical
  by_cases hr : halfExcess A n = 0
  · simp [tailRanks, hr]
  · have hrpos : 0 < halfExcess A n := Nat.pos_of_ne_zero hr
    have hrle := halfExcess_le_card A n
    let j : Fin A.card := ⟨A.card - halfExcess A n, by omega⟩
    have htail : tailRanks A n = Finset.Ici j := by
      ext i
      rw [mem_tailRanks, Finset.mem_Ici]
      change A.card - halfExcess A n ≤ i.val ↔
        A.card - halfExcess A n ≤ i.val
      rfl
    rw [htail, Fin.card_Ici]
    simp [j]
    omega

/-- Every selected tail rank supports linearly many Schur pairs. -/
theorem halfExcess_le_pairsAt_of_mem_tailRanks
    (A : Finset ℕ) (n : ℕ) (hA : A ⊆ interval n)
    (i : Fin A.card) (hi : i ∈ tailRanks A n) :
    halfExcess A n ≤ 2 * (pairsAt A (entry A i)).card + 3 := by
  have hirank := mem_tailRanks.mp hi
  have hpoint := rank_le_add_pairsAt A n hA i
  unfold halfExcess at hirank ⊢
  omega

/-- The Schur-pair fibers over the selected ranks are pairwise disjoint. -/
theorem pairwiseDisjoint_pairsAt_entry (A : Finset ℕ) (n : ℕ) :
    ((tailRanks A n : Finset (Fin A.card)) : Set (Fin A.card)).PairwiseDisjoint
      (fun i ↦ pairsAt A (entry A i)) := by
  intro i hi j hj hij
  apply pairsAt_disjoint
  exact (entry_strictMono A).injective.ne hij

/-- The union of the selected fibers is contained in all Schur pairs. -/
theorem biUnion_pairsAt_entry_subset_schurPairs (A : Finset ℕ) (n : ℕ) :
    (tailRanks A n).biUnion (fun i ↦ pairsAt A (entry A i)) ⊆ schurPairs A := by
  classical
  intro p hp
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  exact pairsAt_subset_schurPairs (entry_mem A i) hp

/-- Summing the disjoint target fibers never exceeds the total Schur-pair
count. -/
theorem sum_card_pairsAt_entry_le (A : Finset ℕ) (n : ℕ) :
    ∑ i ∈ tailRanks A n, (pairsAt A (entry A i)).card ≤ (schurPairs A).card := by
  classical
  calc
    ∑ i ∈ tailRanks A n, (pairsAt A (entry A i)).card =
        ((tailRanks A n).biUnion (fun i ↦ pairsAt A (entry A i))).card := by
      symm
      exact Finset.card_biUnion (pairwiseDisjoint_pairsAt_entry A n)
    _ ≤ (schurPairs A).card :=
      Finset.card_le_card (biUnion_pairsAt_entry_subset_schurPairs A n)

/-- **Finite Schur supersaturation.**  For `A ⊆ {1,...,n}`, let
`r = ⌊(2|A|-n)/2⌋`.  Then the number `e(A)` of distinct-summand,
unordered Schur pairs satisfies `r² ≤ 2 e(A) + 3r`.

This is the parametric near-half estimate needed by the container argument.
In particular it remains effective when the excess density is as small as
`2⁻³⁵`; no fixed coarse density threshold is built into the statement. -/
theorem halfExcess_sq_le_schurPairs (A : Finset ℕ) (n : ℕ)
    (hA : A ⊆ interval n) :
    halfExcess A n * halfExcess A n ≤
      2 * (schurPairs A).card + 3 * halfExcess A n := by
  classical
  let r := halfExcess A n
  let T := tailRanks A n
  have hpoint : ∀ i ∈ T, r ≤ 2 * (pairsAt A (entry A i)).card + 3 := by
    intro i hi
    exact halfExcess_le_pairsAt_of_mem_tailRanks A n hA i hi
  have hsum : ∑ i ∈ T, r ≤
      ∑ i ∈ T, (2 * (pairsAt A (entry A i)).card + 3) := by
    exact Finset.sum_le_sum fun i hi ↦ hpoint i hi
  have hTcard : T.card = r := by
    exact card_tailRanks A n
  have hfibers : ∑ i ∈ T, (pairsAt A (entry A i)).card ≤
      (schurPairs A).card := by
    exact sum_card_pairsAt_entry_le A n
  have hsum' : r * r ≤
      2 * (∑ i ∈ T, (pairsAt A (entry A i)).card) + 3 * r := by
    simpa [Finset.sum_add_distrib, Finset.mul_sum, hTcard, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using hsum
  exact hsum'.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hfibers) (3 * r))

/-- A compact two-inequality form of supersaturation: `r` controls the size
excess and its square is controlled by the Schur-edge count.  This form is
convenient when a container theorem supplies a bound such as `e(A) ≤ C n` or
`e(A) ≤ ε n²`. -/
theorem exists_excess_certificate (A : Finset ℕ) (n : ℕ)
    (hA : A ⊆ interval n) :
    ∃ r : ℕ,
      2 * A.card ≤ n + 2 * r + 1 ∧
        r * r ≤ 2 * (schurPairs A).card + 3 * r := by
  exact ⟨halfExcess A n, two_mul_card_le_add_halfExcess A n,
    halfExcess_sq_le_schurPairs A n hA⟩

/-- Any explicit lower bound `q` for the half-excess yields an explicit
quadratic lower bound, with only the harmless linear error `3n`. -/
theorem sq_le_two_mul_schurPairs_add_three_mul_n_of_le_halfExcess
    (A : Finset ℕ) (n q : ℕ) (hA : A ⊆ interval n)
    (hq : q ≤ halfExcess A n) :
    q * q ≤ 2 * (schurPairs A).card + 3 * n := by
  have hcard : A.card ≤ n := by
    simpa using Finset.card_le_card hA
  calc
    q * q ≤ halfExcess A n * halfExcess A n := Nat.mul_le_mul hq hq
    _ ≤ 2 * (schurPairs A).card + 3 * halfExcess A n :=
      halfExcess_sq_le_schurPairs A n hA
    _ ≤ 2 * (schurPairs A).card + 3 * n := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left 3 ((halfExcess_le_card A n).trans hcard)) _

/-- The concrete density threshold used in the Erdős 877 argument implies
a concrete lower bound for the half-excess. -/
theorem fixedDensity_halfExcess_lowerBound (A : Finset ℕ) (n : ℕ)
    (h : ((2 : ℕ) ^ 34 + 1) * n ≤ (2 : ℕ) ^ 35 * A.card) :
    n / (2 : ℕ) ^ 35 - 1 ≤ halfExcess A n := by
  unfold halfExcess
  norm_num [pow_succ] at h ⊢
  omega

/-- At the `2⁻³⁵` excess-density threshold, the distinct Schur triples
already satisfy a uniform quadratic lower bound (up to a linear error). -/
theorem fixedDensity_sq_le_schurPairs (A : Finset ℕ) (n : ℕ)
    (hA : A ⊆ interval n)
    (h : ((2 : ℕ) ^ 34 + 1) * n ≤ (2 : ℕ) ^ 35 * A.card) :
    (n / (2 : ℕ) ^ 35 - 1) * (n / (2 : ℕ) ^ 35 - 1) ≤
      2 * (schurPairs A).card + 3 * n := by
  exact sq_le_two_mul_schurPairs_add_three_mul_n_of_le_halfExcess A n _ hA
    (fixedDensity_halfExcess_lowerBound A n h)

end EnumerationAlt
end Erdos877
