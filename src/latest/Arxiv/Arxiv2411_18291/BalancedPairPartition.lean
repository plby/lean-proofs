import Arxiv.Arxiv2411_18291.BalancedSubsetCounts
import Arxiv.Arxiv2411_18291.PairNeighbors

/-! # A vertex partition balancing all degrees of a pair family -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_balanced_pair_partition {V : Type*} [DecidableEq V]
    (S : Finset V) (H : Finset (Block V 2)) (hHS : ∀ Q ∈ H, Q.val ⊆ S)
    {c d : ℝ} (hc : 0 ≤ c) (hS : d ≤ (S.card : ℝ))
    (hdegree : ∀ v ∈ S, d ≤ ((H.filter fun Q => v ∈ Q.val).card : ℝ))
    (hsmall : (S.card + 1 : ℝ) * (2 * Real.exp (-(d * c ^ 2 / (4 * (1 + 2 * c))))) < 1) :
    ∃ A : Finset V, A ⊆ S ∧
      |(A.card : ℝ) - (S.card : ℝ) / 2| ≤ c * ((S.card : ℝ) / 2) ∧
      ∀ v ∈ S,
        |((pairNeighbors H v ∩ A).card : ℝ) - ((pairNeighbors H v).card : ℝ) / 2| ≤
          c * (((pairNeighbors H v).card : ℝ) / 2) := by
  classical
  let s : Option S → Finset V := fun i => match i with
    | none => S
    | some v => pairNeighbors H v.val
  have hsub (i : Option S) (_ : i ∈ (univ : Finset (Option S))) : s i ⊆ S := by
    cases i with
    | none => exact Subset.rfl
    | some v =>
      intro w hw
      obtain ⟨Q, hQ, hQval⟩ := (mem_pairNeighbors H v.val w).mp hw
      exact hHS Q hQ (by simp [hQval])
  have hlower (i : Option S) (_ : i ∈ (univ : Finset (Option S))) : d ≤ ((s i).card : ℝ) := by
    cases i with
    | none => exact hS
    | some v => simpa only [s, card_pairNeighbors] using hdegree v.val v.property
  have hfail : ((univ : Finset (Option S)).card : ℝ) *
      (2 * Real.exp (-(d * c ^ 2 / (4 * (1 + 2 * c))))) < 1 := by
    simpa only [card_univ, Fintype.card_option, Fintype.card_coe, Nat.cast_add, Nat.cast_one]
      using hsmall
  obtain ⟨A, hAS, hcounts⟩ := exists_balanced_subset_family S univ s hsub hc hlower hfail
  refine ⟨A, hAS, ?_, ?_⟩
  · simpa only [s, inter_eq_left.mpr hAS] using hcounts none (mem_univ _)
  · intro v hv
    simpa only [s, inter_comm] using hcounts (some ⟨v, hv⟩) (mem_univ _)

end Arxiv2411_18291
