import ErdosProblems.Erdos118.BodySuffixCounts
import ErdosProblems.Erdos118.CutOrder

/-! Restrict the exact gap/selected-pair bijection to the ordinary suffix
starting at a selected leaf, including that current selected entry. -/

namespace Erdos118.LeafSuffixCounts

open Negative Negative.Exact LabelledExtensions LabelCoarsening CutIndices
open GapCounts GapPrefixes SelectedGapCounts

theorem interior_length_le_iff {P Q : InteriorWords.Position} {w : List ℕ}
    (hP : P.word <+: w) (hQ : Q.word <+: w) :
    P.word.length ≤ Q.word.length ↔ P.done.length < Q.done.length ∨
      P.done.length = Q.done.length ∧ P.entries.length ≤ Q.entries.length := by
  constructor
  · intro hlen
    have h := CutOrder.interior_prefix_counts (List.prefix_of_prefix_length_le hP hQ hlen)
    rcases lt_or_eq_of_le h.1 with hlt | he
    · exact Or.inl hlt
    · exact Or.inr ⟨he, (h.2 he).2.2.length_le⟩
  · intro hindex
    by_contra hn
    have hlen : Q.word.length < P.word.length := Nat.lt_of_not_ge hn
    have h := CutOrder.interior_prefix_counts (List.prefix_of_prefix_length_le hQ hP hlen.le)
    rcases hindex with hi | ⟨hi, hj⟩
    · omega
    · have hj' := (h.2 hi.symm).2.2.length_le
      have he := SkippedCuts.interior_common_prefix_same_indices hP hQ hi
        (le_antisymm hj hj')
      subst Q
      exact (Nat.lt_irrefl _ hlen)

def remaining (S : Stem) (i j : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (selected S).filter (fun a ↦ i < a.1 ∨ i = a.1 ∧ j ≤ a.2)

theorem interior_suffix_cutoff {P Q : InteriorWords.Position} {w : List ℕ}
    (hP : P.word <+: w) (hQ : Q.word <+: w) {k : ℕ} (hlen : Q.word.length = k + 1) :
    P.word.length - 1 ≤ k ↔ P.done.length < Q.done.length ∨
      P.done.length = Q.done.length ∧ P.entries.length ≤ Q.entries.length := by
  have hp : 0 < P.word.length := by
    simp only [InteriorWords.Position.word, PartialWordResponses.partialWord, List.length_cons]
    omega
  rw [← interior_length_le_iff hP hQ, hlen]
  omega

theorem gaps_filtered_card (S T : Stem) (hfull : S.done.length = S.root)
    (hd : S.ordinary.Disjoint T.ordinary) (hinterior : InteriorCuts S T)
    (hexact : ExactAnnotations S T) (P : InteriorWords.Position) (hP : P.word <+: S.ordinary) :
    ((gaps S.ordinary T.ordinary).filter (P.word.length - 1 ≤ ·)).card =
      (remaining S P.done.length P.entries.length).card := by
  classical
  have exists_parse : ∀ k, k ∈ gaps S.ordinary T.ordinary → ∃ Q : InteriorWords.Position,
      Q.word <+: S.ordinary ∧ Q.word.length = k + 1 ∧
        Cut S T Q.done.length Q.entries.length := by
    intro k hk
    exact (gap_iff_cut_length S T hd hinterior k).mp ((mem_gaps _ _ _).mp hk)
  let parse := fun k hk ↦ (exists_parse k hk).choose
  have spec : ∀ k hk, (parse k hk).word <+: S.ordinary ∧ (parse k hk).word.length = k + 1 ∧
      Cut S T (parse k hk).done.length (parse k hk).entries.length := by
    intro k hk
    exact (exists_parse k hk).choose_spec
  apply Finset.card_bij (fun k hk ↦
    ⟨(parse k (Finset.mem_filter.mp hk).1).done.length,
      (parse k (Finset.mem_filter.mp hk).1).entries.length⟩)
  · intro k hk
    obtain ⟨hkg, hkm⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_selected _ _ _).mpr
      have hi := interior_prefix_body_bound hfull (spec k hkg).1
      exact ⟨hi, (hexact.body _ hi _).mpr (spec k hkg).2.2⟩
    · exact (interior_suffix_cutoff hP (spec k hkg).1 (spec k hkg).2.1).mp hkm
  · intro k hk l hl he
    have hi := congrArg Sigma.fst he
    have hj := congrArg (fun x : Σ _ : ℕ, ℕ ↦ x.2) he
    have hQ := SkippedCuts.interior_common_prefix_same_indices
      (spec k (Finset.mem_filter.mp hk).1).1 (spec l (Finset.mem_filter.mp hl).1).1 hi hj
    have hlen := congrArg (fun Q : InteriorWords.Position ↦ Q.word.length) hQ
    rw [(spec k (Finset.mem_filter.mp hk).1).2.1,
      (spec l (Finset.mem_filter.mp hl).1).2.1] at hlen
    omega
  · intro a ha
    obtain ⟨has, ham⟩ := Finset.mem_filter.mp ha
    obtain ⟨hi, hj⟩ := (mem_selected S a.1 a.2).mp has
    obtain ⟨y, hy, hproper, Q, hQ, hqi, hqj⟩ := (hexact.body _ hi _).mp hj
    have hp : Q.word <+: S.ordinary := by
      rw [hQ]
      exact List.takeWhile_prefix _
    have hpos : 0 < Q.word.length := by
      simp only [InteriorWords.Position.word, PartialWordResponses.partialWord, List.length_cons]
      omega
    let k := Q.word.length - 1
    have hlen : Q.word.length = k + 1 := by dsimp [k]; omega
    have hcut : Cut S T Q.done.length Q.entries.length :=
      ⟨y, hy, hproper, Q, hQ, rfl, rfl⟩
    have hkg : k ∈ gaps S.ordinary T.ordinary :=
      (mem_gaps _ _ _).mpr ((gap_iff_cut_length S T hd hinterior k).mpr ⟨Q, hp, hlen, hcut⟩)
    have hkm : P.word.length - 1 ≤ k := (interior_suffix_cutoff hP hp hlen).mpr
      (by simpa only [hqi, hqj] using ham)
    have hk := Finset.mem_filter.mpr ⟨hkg, hkm⟩
    refine ⟨k, hk, ?_⟩
    have he := interior_prefix_length_injective (spec k hkg).1 hp
      ((spec k hkg).2.1.trans hlen.symm)
    change (⟨(parse k hkg).done.length, (parse k hkg).entries.length⟩ : Σ _ : ℕ, ℕ) = a
    rw [he, hqi, hqj]

theorem suffix_gaps_card (S T : Stem) (hfull : S.done.length = S.root)
    (hd : S.ordinary.Disjoint T.ordinary) (hinterior : InteriorCuts S T)
    (hexact : ExactAnnotations S T) (P : InteriorWords.Position) (hP : P.word <+: S.ordinary) :
    (gaps (S.ordinary.drop (P.word.length - 1)) T.ordinary).card =
      (remaining S P.done.length P.entries.length).card := by
  rw [gaps_drop_card]
  exact gaps_filtered_card S T hfull hd hinterior hexact P hP

end Erdos118.LeafSuffixCounts
