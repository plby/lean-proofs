import Arxiv.Arxiv2411_18291.VariableSplittingFamily
import Arxiv.Arxiv2411_18291.SplittingSigns

/-! # Fixed splitting signs with a separate capacity at each root

The sign families are fixed before choosing a represented leave. Every
coefficient vector within the individual capacities splits inside them.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ : ℝ}

def VariableSplittingFamily.positiveCliques
    (F : VariableSplittingFamily S D B C θ) : Finset (Block V q) :=
  univ.biUnion fun s => (S.map (F.embedding s)).positiveReplacement s.2.1

def VariableSplittingFamily.negativeCliques
    (F : VariableSplittingFamily S D B C θ) : Finset (Block V q) :=
  univ.biUnion fun s => (S.map (F.embedding s)).negativeReplacement s.2.1

theorem VariableSplittingFamily.signs_disjoint
    (F : VariableSplittingFamily S D B C θ) (hqr : r + 1 ≤ q) :
    Disjoint F.positiveCliques F.negativeCliques := by
  apply disjoint_left.mpr
  intro Q hQP hQN
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp hQP
  obtain ⟨t, _, ht⟩ := mem_biUnion.mp hQN
  by_cases hst : s = t
  · subst t
    exact disjoint_left.mp ((S.map (F.embedding s)).replacement_signs_disjoint s.2.1) hs ht
  · exact disjoint_left.mp (F.replacements_disjoint hqr hst)
      ((S.map (F.embedding s)).positiveReplacement_subset _ hs)
      ((S.map (F.embedding t)).negativeReplacement_subset _ ht)

theorem VariableSplittingFamily.signed_representation_with_signs
    (F : VariableSplittingFamily S D B C θ)
    (hqr : r + 1 ≤ q) (Φ : Block V q → ℤ) (hΦ : ∀ Q, |Φ Q| ≤ C Q)
    (hs : ∀ Q, Q ∉ D → Φ Q = 0) :
    ∃ P N : Finset (Block V q), P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧
      Disjoint P N ∧ boundary (r + 1) (indicator P - indicator N) = boundary (r + 1) Φ := by
  let T := fun s : VariableCliqueSlots D C => S.map (F.embedding s)
  let c := fun s : VariableCliqueSlots D C => signedSlotWeight (Φ s.1.val) s.2
  obtain ⟨P, N, _, _, hdis, hχ⟩ := signed_sets_of_unit_coefficients (exchangeSum T c)
    (exchangeSum_abs_le_one T c (F.replacements_disjoint hqr)
      (fun s => signedSlotWeight_abs_le _ _))
    (exchangeSupport T) (exchangeSum_support T c)
  refine ⟨P, N, ?_, ?_, hdis, ?_⟩
  · intro Q hQP
    by_contra hQ
    have hnonpos : exchangeSum T c Q ≤ 0 := by
      rw [exchangeSum, Finset.sum_apply]
      apply sum_nonpos
      intro s _
      apply signedSlot_replacement_nonpos (T s) (Φ s.1.val) s.2 Q
      intro h
      exact hQ (mem_biUnion.mpr ⟨s, mem_univ _, h⟩)
    have hval : exchangeSum T c Q = 1 := by
      rw [hχ, Pi.sub_apply, indicator_apply_of_mem hQP,
        indicator_apply_of_notMem (fun h => disjoint_left.mp hdis hQP h), sub_zero]
    rw [hval] at hnonpos
    norm_num at hnonpos
  · intro Q hQN
    by_contra hQ
    have hnonneg : 0 ≤ exchangeSum T c Q := by
      rw [exchangeSum, Finset.sum_apply]
      apply sum_nonneg
      intro s _
      apply signedSlot_replacement_nonneg (T s) (Φ s.1.val) s.2 Q
      intro h
      exact hQ (mem_biUnion.mpr ⟨s, mem_univ _, h⟩)
    have hval : exchangeSum T c Q = -1 := by
      rw [hχ, Pi.sub_apply, indicator_apply_of_notMem (fun h => disjoint_left.mp hdis h hQN),
        indicator_apply_of_mem hQN]
      norm_num
    rw [hval] at hnonneg
    norm_num at hnonneg
  · rw [← hχ, boundary_exchangeSum]
    have hroot (s : VariableCliqueSlots D C) : (T s).base = s.1.val := F.base s
    simp only [hroot, c]
    exact variableCliqueSlots_boundary D C Φ hΦ hs

end Arxiv2411_18291
