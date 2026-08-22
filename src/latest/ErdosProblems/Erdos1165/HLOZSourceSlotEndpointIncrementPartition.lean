/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllSixExactCoordinateProductClosure
import ErdosProblems.Erdos1165.HLOZShellZeroEndpointIncrementPartition

/-!
# Partition of an unrestricted coordinate product by endpoint increment

The actual-delta shell screen partitions a mixed `I₁/I₀` product.  A
Theta marginal instead exposes one coordinate and sums its *entire*
truncated law.  This file gives the corresponding finite partition: every
vector belongs to the unique slice indexed by its literal endpoint count.
-/

open scoped BigOperators

namespace Erdos1165.HLOZSourceSlotEndpointIncrementPartition

open FiniteDominoProductLaw HLOZAllSixExactCoordinateProductClosure
open HLOZShellZeroEndpointIncrementPartition
open TilingShellZeroActualDeltaPartition

noncomputable section

/-- An unrestricted vector refined by its actual endpoint increment. -/
def vectorAtEndpointIncrement
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*}
    (contribution : ∀ c, State c → ℕ) (delta : ℕ)
    (ell : ∀ c, State c) : Prop :=
  endpointIncrementOfVector contribution ell = delta

noncomputable instance instDecidablePredVectorAtEndpointIncrement
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (contribution : ∀ c, State c → ℕ) (delta : ℕ) :
    DecidablePred (vectorAtEndpointIncrement contribution delta) :=
  Classical.decPred _

theorem endpointIncrementOfVector_le_twice_card
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*}
    (contribution : ∀ c, State c → ℕ)
    (hcontribution : ∀ c v, contribution c v ≤ 2)
    (ell : ∀ c, State c) :
    endpointIncrementOfVector contribution ell ≤
      2 * Fintype.card Coordinate := by
  unfold endpointIncrementOfVector
  calc
    ∑ c, contribution c (ell c) ≤ ∑ _c : Coordinate, 2 := by
      exact Finset.sum_le_sum fun c _ ↦ hcontribution c (ell c)
    _ = 2 * Fintype.card Coordinate := by
      simp [mul_comm]

/-- Every vector has a unique bounded actual-increment index. -/
theorem existsUnique_vectorAtEndpointIncrement
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*}
    (contribution : ∀ c, State c → ℕ)
    (hcontribution : ∀ c v, contribution c v ≤ 2)
    (ell : ∀ c, State c) :
    ∃! delta : ReplacementEndpointIncrement (Fintype.card Coordinate) 0,
      vectorAtEndpointIncrement contribution delta ell := by
  have hle := endpointIncrementOfVector_le_twice_card
    contribution hcontribution ell
  let delta : ReplacementEndpointIncrement (Fintype.card Coordinate) 0 :=
    ⟨endpointIncrementOfVector contribution ell, by
      simpa only [replacementMovedCount, Nat.sub_zero] using
        Nat.lt_succ_of_le hle⟩
  refine ⟨delta, rfl, ?_⟩
  intro delta' hdelta'
  exact Fin.ext hdelta'.symm

/-- Exact finite partition of an arbitrary weighted product by its bounded
actual increment. -/
theorem sum_vectorAtEndpointIncrement_eq
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    [Fintype ((c : Coordinate) → State c)]
    (weight : (∀ c, State c) → ℝ)
    (contribution : ∀ c, State c → ℕ)
    (hcontribution : ∀ c v, contribution c v ≤ 2) :
    (∑ delta : ReplacementEndpointIncrement (Fintype.card Coordinate) 0,
      ∑ ell : ∀ c, State c,
        if vectorAtEndpointIncrement contribution delta ell then
          weight ell else 0) =
      ∑ ell : ∀ c, State c, weight ell := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell _
  obtain ⟨delta, hdelta, hunique⟩ :=
    existsUnique_vectorAtEndpointIncrement contribution hcontribution ell
  rw [Finset.sum_eq_single delta]
  · rw [if_pos hdelta]
  · intro delta' _ hne
    rw [if_neg]
    exact fun h ↦ hne (hunique delta' h)
  · intro hnot
    exact (hnot (Finset.mem_univ delta)).elim

/-- The normalized unrestricted product is the sum of its actual-increment
slices. -/
theorem sum_screenMass_vectorAtEndpointIncrement_eq
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (upper : Coordinate → ℕ) (pointMass : Coordinate → ℕ → ℝ)
    (contribution : ∀ c, Fin (upper c) → ℕ)
    (hcontribution : ∀ c v, contribution c v ≤ 2) :
    (∑ delta : ReplacementEndpointIncrement (Fintype.card Coordinate) 0,
      @screenMass Coordinate inferInstance inferInstance pointMass upper
        (vectorAtEndpointIncrement contribution delta)
        (instDecidablePredVectorAtEndpointIncrement contribution delta)) =
      ∑ ell : TruncatedTotals upper,
        normalizedJointMass pointMass upper ell := by
  classical
  unfold screenMass
  exact sum_vectorAtEndpointIncrement_eq
    (normalizedJointMass pointMass upper) contribution hcontribution

/-- If each coordinate mass is normalized, the actual-increment slices have
total mass one. -/
theorem sum_screenMass_vectorAtEndpointIncrement_eq_one
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (upper : Coordinate → ℕ) (pointMass : Coordinate → ℕ → ℝ)
    (contribution : ∀ c, Fin (upper c) → ℕ)
    (hcontribution : ∀ c v, contribution c v ≤ 2)
    (hcoordinate : ∀ c,
      (∑ v : Fin (upper c), coordinateMass pointMass upper c v) = 1) :
    (∑ delta : ReplacementEndpointIncrement (Fintype.card Coordinate) 0,
      @screenMass Coordinate inferInstance inferInstance pointMass upper
        (vectorAtEndpointIncrement contribution delta)
        (instDecidablePredVectorAtEndpointIncrement contribution delta)) = 1 := by
  classical
  rw [sum_screenMass_vectorAtEndpointIncrement_eq upper pointMass contribution
    hcontribution]
  simp_rw [normalizedJointMass_eq_product]
  have hsum := Finset.prod_univ_sum
    (fun c : Coordinate ↦ (Finset.univ : Finset (Fin (upper c))))
    (fun c v ↦ coordinateMass pointMass upper c v)
  rw [Fintype.piFinset_univ] at hsum
  rw [← hsum]
  simp only [hcoordinate, Finset.prod_const_one]

end

end Erdos1165.HLOZSourceSlotEndpointIncrementPartition
