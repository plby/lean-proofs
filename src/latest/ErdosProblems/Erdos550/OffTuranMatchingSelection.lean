import Mathlib
import ErdosProblems.Erdos550.OffTuranThresholding
import ErdosProblems.Erdos550.MaximalMatchingPackage
import ErdosProblems.Erdos550.MatchingCoverageBounds

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Heavy-head and matching selection for the direct off-Turán route

The heavy-family counting estimate first supplies a dense edge inside the heavy
family; a maximum matching is then chosen away from its endpoints, with the
exact uncovered-cluster estimate needed downstream.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

/-- **Complete finite selection.**  An independence bound at scale `B`,
together with the cleaned average-degree estimate and the numerical fact that
`B` fits below the guaranteed heavy-family size, produces a heavy head edge and
a maximum matching away from it. -/
theorem exists_heavy_head_and_matching_coverage
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (S : Finset ι) (D : ι → ℝ) (base η N : ℝ) (B : ℕ)
    (hN : 0 < N) (hbase : 0 ≤ base + 80 * η * N)
    (hup : ∀ i ∈ S, D i ≤ N)
    (havg : (base + 100 * η * N) * (S.card : ℝ) ≤ ∑ i ∈ S, D i)
    (hB : (B : ℝ) ≤ (20 * η) * (S.card : ℝ))
    (hα : ∀ A : Finset ι, B ≤ A.card →
      ∃ a ∈ A, ∃ b ∈ A, R.Adj a b) :
    ∃ X Y : ι,
      X ∈ heavyClusterFamily S D base η N ∧
      Y ∈ heavyClusterFamily S D base η N ∧ R.Adj X Y ∧
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
        (cL cR : κ → ι) (U : Finset ι),
        (∀ k, R.Adj (cL k) (cR k)) ∧
        Function.Injective (Sum.elim cL cR) ∧
        (∀ k, cL k ≠ X ∧ cL k ≠ Y ∧ cR k ≠ X ∧ cR k ≠ Y) ∧
        U.card < B ∧
        (∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
          a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR) ∧
        (Finset.univ \ (Finset.univ.image cL ∪ Finset.univ.image cR)).card < B + 2 := by
  have hheavyReal : (B : ℝ) ≤
      ((heavyClusterFamily S D base η N).card : ℝ) :=
    hB.trans (heavyClusterFamily_card_lower S D base η N hN hbase hup havg)
  have hheavy : B ≤ (heavyClusterFamily S D base η N).card := by
    exact_mod_cast hheavyReal
  obtain ⟨X, hX, Y, hY, hXY⟩ :=
    hα (heavyClusterFamily S D base η N) hheavy
  obtain ⟨κ, _, _, cL, cR, U, hedges, hinj, hnotin,
      hUcard, hUdef⟩ :=
    exists_indexed_maximum_matching_away R X Y B hα
  have hcover :
      (Finset.univ \
        (Finset.univ.image cL ∪ Finset.univ.image cR)).card < B + 2 := by
    exact card_compl_matching_endpoints_lt_add_two
      X Y cL cR U B hUdef hUcard
  exact ⟨X, Y, hX, hY, hXY, κ, inferInstance, inferInstance,
    cL, cR, U, hedges, hinj, hnotin, hUcard, hUdef, hcover⟩

end Erdos550
