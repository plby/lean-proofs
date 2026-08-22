/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroActualDeltaPartition
import ErdosProblems.Erdos1165.TilingShellZeroFactoredCapScreen

/-!
# Finite partition by actual threshold-endpoint increment

The fixed-central screen chooses `moved = total - central` replacement
coordinates.  Each moved domino can create zero, one, or two new threshold
endpoints.  This file partitions the mixed product screen by the resulting
increment and proves the exact finite-mass identity.
-/

open scoped BigOperators

namespace Erdos1165.HLOZShellZeroEndpointIncrementPartition

open FiniteDominoProductLaw
open TilingShellZeroActualDeltaPartition
open TilingShellZeroFactoredCapScreen

noncomputable section

/-- Total actual endpoint increment carried by a product vector. -/
def endpointIncrementOfVector
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*}
    (contribution : ∀ c, State c → ℕ)
    (ell : ∀ c, State c) : ℕ :=
  ∑ c, contribution c (ell c)

theorem endpointIncrementOfVector_le_twiceMoved
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    (contribution : ∀ c, State c → ℕ)
    {central : ℕ} {ell : ∀ c, State c}
    (hsource_zero : ∀ c v, source c v → contribution c v = 0)
    (hcontribution : ∀ c v, contribution c v ≤ 2)
    (hexact : exactSourceSubsetVector source replacement central ell) :
    endpointIncrementOfVector contribution ell ≤
      2 * (Fintype.card Coordinate - central) := by
  rcases hexact with ⟨A, hAcard, hclass⟩
  have hAsub : A ⊆ (Finset.univ : Finset Coordinate) :=
    (Finset.mem_powersetCard.mp hAcard).1
  have hAcard' : A.card = central :=
    (Finset.mem_powersetCard.mp hAcard).2
  have hzero : ∀ c ∈ A, contribution c (ell c) = 0 := by
    intro c hc
    exact hsource_zero c (ell c) ((hclass c).1 hc)
  calc
    endpointIncrementOfVector contribution ell =
        ∑ c ∈ (Finset.univ : Finset Coordinate) \ A,
          contribution c (ell c) := by
      unfold endpointIncrementOfVector
      rw [← Finset.sum_sdiff hAsub]
      simp only [Finset.sum_eq_zero hzero, add_zero]
    _ ≤ ∑ _c ∈ (Finset.univ : Finset Coordinate) \ A, 2 := by
      exact Finset.sum_le_sum fun c _ ↦ hcontribution c (ell c)
    _ = 2 * (Fintype.card Coordinate - central) := by
      rw [Finset.sum_const, Finset.card_sdiff_of_subset hAsub,
        Finset.card_univ, hAcard']
      simp [mul_comm]

/-- The mixed screen refined by its unique actual endpoint increment. -/
def exactSourceSubsetVectorAtIncrement
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    (contribution : ∀ c, State c → ℕ)
    (central : ℕ) (delta : ℕ) (ell : ∀ c, State c) : Prop :=
  exactSourceSubsetVector source replacement central ell ∧
    endpointIncrementOfVector contribution ell = delta

noncomputable instance instDecidablePredExactSourceSubsetVectorAtIncrement
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (source replacement : ∀ c, State c → Prop)
    (contribution : ∀ c, State c → ℕ)
    (central delta : ℕ) :
    DecidablePred (exactSourceSubsetVectorAtIncrement source replacement
      contribution central delta) :=
  Classical.decPred _

theorem exists_unique_increment
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    (contribution : ∀ c, State c → ℕ)
    {central : ℕ} {ell : ∀ c, State c}
    (hsource_zero : ∀ c v, source c v → contribution c v = 0)
    (hcontribution : ∀ c v, contribution c v ≤ 2)
    (hexact : exactSourceSubsetVector source replacement central ell) :
    ∃! delta : ReplacementEndpointIncrement (Fintype.card Coordinate) central,
      exactSourceSubsetVectorAtIncrement source replacement contribution
        central delta ell := by
  have hle := endpointIncrementOfVector_le_twiceMoved source replacement
    contribution hsource_zero hcontribution hexact
  let delta : ReplacementEndpointIncrement (Fintype.card Coordinate) central :=
    ⟨endpointIncrementOfVector contribution ell, by
      simpa only [replacementMovedCount] using Nat.lt_succ_of_le hle⟩
  refine ⟨delta, ⟨hexact, rfl⟩, ?_⟩
  intro delta' hdelta'
  exact Fin.ext hdelta'.2.symm

/-- Exact partition of an arbitrary weighted mixed screen into actual
endpoint-increment slices. -/
theorem sum_exactSourceSubsetVectorAtIncrement_eq
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (weight : (ell : ∀ c, State c) → ℝ)
    (source replacement : ∀ c, State c → Prop)
    (contribution : ∀ c, State c → ℕ)
    (central : ℕ)
    (hsource_zero : ∀ c v, source c v → contribution c v = 0)
    (hcontribution : ∀ c v, contribution c v ≤ 2) :
    (∑ delta : ReplacementEndpointIncrement
        (Fintype.card Coordinate) central,
      ∑ ell : ∀ c, State c,
        if exactSourceSubsetVectorAtIncrement source replacement contribution
            central delta ell then weight ell else 0) =
      ∑ ell : ∀ c, State c,
        if exactSourceSubsetVector source replacement central ell then
          weight ell else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases hexact : exactSourceSubsetVector source replacement central ell
  · obtain ⟨delta, hdelta, hunique⟩ := exists_unique_increment
      source replacement contribution hsource_zero hcontribution hexact
    rw [if_pos hexact, Finset.sum_eq_single delta]
    · rw [if_pos hdelta]
    · intro delta' _ hne
      rw [if_neg]
      exact fun h ↦ hne (hunique delta' h)
    · intro hnot
      exact (hnot (Finset.mem_univ delta)).elim
  · rw [if_neg hexact]
    apply Finset.sum_eq_zero
    intro delta _
    rw [if_neg]
    exact fun h ↦ hexact h.1

/-- The normalized finite-product mass of the fixed-central screen is the
sum of the masses of its actual-increment slices. -/
theorem sum_screenMass_exactSourceSubsetVectorAtIncrement_eq
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (upper : Coordinate → ℕ) (pointMass : Coordinate → ℕ → ℝ)
    (source replacement : ∀ c, Fin (upper c) → Prop)
    (contribution : ∀ c, Fin (upper c) → ℕ)
    (central : ℕ)
    (hsource_zero : ∀ c v, source c v → contribution c v = 0)
    (hcontribution : ∀ c v, contribution c v ≤ 2) :
    (∑ delta : ReplacementEndpointIncrement
        (Fintype.card Coordinate) central,
      @screenMass Coordinate inferInstance inferInstance pointMass upper
        (exactSourceSubsetVectorAtIncrement source replacement contribution
          central delta)
        (instDecidablePredExactSourceSubsetVectorAtIncrement source replacement
          contribution central delta)) =
      @screenMass Coordinate inferInstance inferInstance pointMass upper
        (exactSourceSubsetVector source replacement central)
        (instDecidablePredExactSourceSubsetVector source replacement central) := by
  unfold screenMass
  exact sum_exactSourceSubsetVectorAtIncrement_eq
    (fun ell ↦ normalizedJointMass pointMass upper ell)
    source replacement contribution central hsource_zero hcontribution

end

end Erdos1165.HLOZShellZeroEndpointIncrementPartition
