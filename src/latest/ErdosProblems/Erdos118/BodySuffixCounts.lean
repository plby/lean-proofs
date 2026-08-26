import ErdosProblems.Erdos118.SelectedGapCounts

/-!
Finite ordinary suffixes at body markers. An interior parse's body index
locates its gap relative to every body marker, and the parsing bijection
restricts to these suffixes.
-/

namespace Erdos118.BodySuffixCounts

open Negative Negative.Exact LabelledExtensions LabelCoarsening CutIndices
open GapCounts GapPrefixes SelectedGapCounts

theorem partial_prefix_length_cutoff {p s : G2} {n : ℕ} {u : List ℕ}
    (hu : u.length < n) (hp : p.flatMap levelWord ++ n :: u <+: s.flatMap levelWord) (m : ℕ) :
    ((s.take m).flatMap levelWord).length < (p.flatMap levelWord ++ n :: u).length ↔
      m ≤ p.length := by
  induction p generalizing s m with
  | nil =>
    cases s with
    | nil => simp at hp
    | cons a s =>
      have hn : n = a.length := (List.cons_prefix_cons.mp hp).1
      cases m with
      | zero => simp
      | succ m =>
        simp only [List.take_succ_cons, List.flatMap_cons, List.flatMap_nil, List.nil_append,
          List.length_append, levelWord, List.length_cons, List.length_nil]
        omega
  | cons a p ih =>
    cases s with
    | nil => simp [levelWord] at hp
    | cons b s =>
      have hp' : levelWord a ++ (p.flatMap levelWord ++ n :: u) <+:
          levelWord b ++ s.flatMap levelWord := by
        simpa only [List.flatMap_cons, List.append_assoc] using hp
      obtain ⟨hab, htail⟩ := WordResponses.levelWord_prefix_cancel hp'
      subst b
      cases m with
      | zero => simp [levelWord]
      | succ m =>
        simpa only [List.take_succ_cons, List.flatMap_cons, List.length_append,
          Nat.add_lt_add_iff_left, List.length_cons, Nat.add_le_add_iff_right,
          List.append_assoc] using ih htail m

def offset (S : Stem) (m : ℕ) : ℕ := 1 + ((S.done.take m).flatMap Body.ordinary).length

theorem interior_length_cutoff {P : InteriorWords.Position} {S : Stem}
    (hp : P.word <+: S.ordinary) {k : ℕ} (hlen : P.word.length = k + 1) (m : ℕ) :
    offset S m ≤ k ↔ m ≤ P.done.length := by
  have htail : P.done.flatMap levelWord ++ P.size :: P.entries <+:
      (S.done.map Body.values).flatMap levelWord := by
    rw [List.flatMap_map]
    exact (List.cons_prefix_cons.mp hp).2
  have h := partial_prefix_length_cutoff P.unfinished htail m
  have he : ((S.done.map Body.values).take m).flatMap levelWord =
      (S.done.take m).flatMap Body.ordinary := by
    rw [← List.map_take, List.flatMap_map]
    rfl
  rw [he] at h
  have hlen' : (P.done.flatMap levelWord ++ P.size :: P.entries).length = k := by
    simpa only [InteriorWords.Position.word, PartialWordResponses.partialWord,
      List.length_cons, Nat.add_right_cancel_iff] using hlen
  rw [hlen'] at h
  unfold offset
  omega

theorem gaps_filtered_card (S T : Stem) (hfull : S.done.length = S.root)
    (hd : S.ordinary.Disjoint T.ordinary) (hinterior : InteriorCuts S T)
    (hexact : ExactAnnotations S T) (m : ℕ) :
    ((gaps S.ordinary T.ordinary).filter (offset S m ≤ ·)).card =
      ((selected S).filter (fun a ↦ m ≤ a.1)).card := by
  classical
  have exists_parse : ∀ k, k ∈ gaps S.ordinary T.ordinary → ∃ P : InteriorWords.Position,
      P.word <+: S.ordinary ∧ P.word.length = k + 1 ∧
        Cut S T P.done.length P.entries.length := by
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
    · exact (interior_length_cutoff (spec k hkg).1 (spec k hkg).2.1 m).mp hkm
  · intro k hk l hl he
    have hi := congrArg Sigma.fst he
    have hj := congrArg (fun x : Σ _ : ℕ, ℕ ↦ x.2) he
    have hP := SkippedCuts.interior_common_prefix_same_indices
      (spec k (Finset.mem_filter.mp hk).1).1 (spec l (Finset.mem_filter.mp hl).1).1 hi hj
    have hlen := congrArg (fun P : InteriorWords.Position ↦ P.word.length) hP
    rw [(spec k (Finset.mem_filter.mp hk).1).2.1,
      (spec l (Finset.mem_filter.mp hl).1).2.1] at hlen
    omega
  · intro a ha
    obtain ⟨has, ham⟩ := Finset.mem_filter.mp ha
    obtain ⟨hi, hj⟩ := (mem_selected S a.1 a.2).mp has
    obtain ⟨y, hy, hproper, P, hP, hpi, hpj⟩ := (hexact.body _ hi _).mp hj
    have hp : P.word <+: S.ordinary := by
      rw [hP]
      exact List.takeWhile_prefix _
    have hpos : 0 < P.word.length := by
      simp only [InteriorWords.Position.word, PartialWordResponses.partialWord, List.length_cons]
      omega
    let k := P.word.length - 1
    have hlen : P.word.length = k + 1 := by dsimp [k]; omega
    have hcut : Cut S T P.done.length P.entries.length :=
      ⟨y, hy, hproper, P, hP, rfl, rfl⟩
    have hkg : k ∈ gaps S.ordinary T.ordinary :=
      (mem_gaps _ _ _).mpr ((gap_iff_cut_length S T hd hinterior k).mpr ⟨P, hp, hlen, hcut⟩)
    have hkm : offset S m ≤ k := (interior_length_cutoff hp hlen m).mpr (hpi ▸ ham)
    have hk := Finset.mem_filter.mpr ⟨hkg, hkm⟩
    refine ⟨k, hk, ?_⟩
    have he := interior_prefix_length_injective (spec k hkg).1 hp
      ((spec k hkg).2.1.trans hlen.symm)
    change (⟨(parse k hkg).done.length, (parse k hkg).entries.length⟩ : Σ _ : ℕ, ℕ) = a
    rw [he, hpi, hpj]

theorem suffix_gaps_card (S T : Stem) (hfull : S.done.length = S.root)
    (hd : S.ordinary.Disjoint T.ordinary) (hinterior : InteriorCuts S T)
    (hexact : ExactAnnotations S T) (m : ℕ) :
    (gaps (S.ordinary.drop (offset S m)) T.ordinary).card =
      ((selected S).filter (fun a ↦ m ≤ a.1)).card := by
  rw [gaps_drop_card]
  exact gaps_filtered_card S T hfull hd hinterior hexact m

end Erdos118.BodySuffixCounts
