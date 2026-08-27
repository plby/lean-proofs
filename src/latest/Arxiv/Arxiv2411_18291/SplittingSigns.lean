import Arxiv.Arxiv2411_18291.SplittingFamily

/-!
# Fixed signs of the splitting cliques

Positive and negative root slots use opposite orientations of an exchange.
Their allowed positive and negative replacement families are fixed before
the coefficient vector is chosen. Every bounded representation splits
inside these fixed families, which are disjoint as sets of cliques.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r C : ℕ}

def ExchangeSystem.positiveReplacement (S : ExchangeSystem V q r) (b : Bool) :=
  if b then S.negative else S.positive.erase S.base

def ExchangeSystem.negativeReplacement (S : ExchangeSystem V q r) (b : Bool) :=
  if b then S.positive.erase S.base else S.negative

theorem ExchangeSystem.positiveReplacement_subset (S : ExchangeSystem V q r) (b : Bool) :
    S.positiveReplacement b ⊆ S.replacementCliques := by
  cases b
  · exact subset_union_right
  · exact subset_union_left

theorem ExchangeSystem.negativeReplacement_subset (S : ExchangeSystem V q r) (b : Bool) :
    S.negativeReplacement b ⊆ S.replacementCliques := by
  cases b
  · exact subset_union_left
  · exact subset_union_right

theorem ExchangeSystem.replacement_signs_disjoint (S : ExchangeSystem V q r) (b : Bool) :
    Disjoint (S.positiveReplacement b) (S.negativeReplacement b) := by
  have h := Disjoint.mono_left (erase_subset S.base S.positive) S.disjoint
  cases b
  · exact h
  · exact h.symm

theorem signedSlot_replacement_nonpos (S : ExchangeSystem V q r) (a : ℤ)
    (s : Bool × Fin C) (Q : Block V q) (hQ : Q ∉ S.positiveReplacement s.1) :
    signedSlotWeight a s * S.replacementVector Q ≤ 0 := by
  rcases signedSlotWeight_sign a s with hc | ⟨hb, hc⟩ | ⟨hb, hc⟩
  · rw [hc, zero_mul]
  · have hN : Q ∉ S.negative := by simpa [ExchangeSystem.positiveReplacement, hb] using hQ
    simp only [hc, one_mul, ExchangeSystem.replacementVector, Pi.sub_apply,
      indicator_apply_of_notMem hN]
    unfold indicator
    split_ifs <;> norm_num
  · have hP : Q ∉ S.positive.erase S.base := by
      simpa [ExchangeSystem.positiveReplacement, hb] using hQ
    simp only [hc, neg_one_mul, ExchangeSystem.replacementVector, Pi.sub_apply,
      indicator_apply_of_notMem hP, sub_zero]
    unfold indicator
    split_ifs <;> norm_num

theorem signedSlot_replacement_nonneg (S : ExchangeSystem V q r) (a : ℤ)
    (s : Bool × Fin C) (Q : Block V q) (hQ : Q ∉ S.negativeReplacement s.1) :
    0 ≤ signedSlotWeight a s * S.replacementVector Q := by
  rcases signedSlotWeight_sign a s with hc | ⟨hb, hc⟩ | ⟨hb, hc⟩
  · rw [hc, zero_mul]
  · have hP : Q ∉ S.positive.erase S.base := by
      simpa [ExchangeSystem.negativeReplacement, hb] using hQ
    simp only [hc, one_mul, ExchangeSystem.replacementVector, Pi.sub_apply,
      indicator_apply_of_notMem hP, sub_zero]
    unfold indicator
    split_ifs <;> norm_num
  · have hN : Q ∉ S.negative := by simpa [ExchangeSystem.negativeReplacement, hb] using hQ
    simp only [hc, neg_one_mul, ExchangeSystem.replacementVector, Pi.sub_apply,
      indicator_apply_of_notMem hN]
    unfold indicator
    split_ifs <;> norm_num

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

def SplittingFamily.positiveCliques (F : SplittingFamily S D B C θ) : Finset (Block V q) :=
  univ.biUnion fun s => (S.map (F.embedding s)).positiveReplacement s.2.1

def SplittingFamily.negativeCliques (F : SplittingFamily S D B C θ) : Finset (Block V q) :=
  univ.biUnion fun s => (S.map (F.embedding s)).negativeReplacement s.2.1

theorem SplittingFamily.signs_disjoint (F : SplittingFamily S D B C θ) (hqr : r + 1 ≤ q) :
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

theorem SplittingFamily.signed_representation_with_signs (F : SplittingFamily S D B C θ)
    (hqr : r + 1 ≤ q) (Φ : Block V q → ℤ) (hΦ : ∀ Q, |Φ Q| ≤ C)
    (hs : ∀ Q, Q ∉ D → Φ Q = 0) :
    ∃ P N : Finset (Block V q), P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧
      Disjoint P N ∧ boundary (r + 1) (indicator P - indicator N) = boundary (r + 1) Φ := by
  let T := fun s : SignedCliqueSlots D C => S.map (F.embedding s)
  let c := fun s : SignedCliqueSlots D C => signedSlotWeight (Φ s.1.val) s.2
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
    have hroot (s : SignedCliqueSlots D C) : (T s).base = s.1.val := F.base s
    simp only [hroot, c]
    exact signedCliqueSlots_boundary D Φ hΦ hs

end Arxiv2411_18291
