import ErdosProblems.Erdos118.LabelledFrames
import ErdosProblems.Erdos118.WordResponses

/-!
Exact response fronts at a fixed body-decision stem. The prescribed positive
label cardinality and its first coordinate determine the stopping point.
These fronts do not yet define the full adaptive two-word game.
-/

namespace Erdos118.BodyResponses

open LabelledExtensions Negative Negative.Exact Erdos590.Larson

def newWord (P : Position) : List ℕ := P.label ++ P.size :: P.entries

structure Setup (S : Stem) (k : ℕ) where
  position : Position
  stem_eq : position.stem = S
  label_length : position.label.length = k + 1
  entries_length : position.entries.length = position.label.headD 0

theorem newWord_pairwise (P : Position) : (newWord P).Pairwise (· < ·) :=
  (List.pairwise_append.mp P.increasing).2.1

theorem newWord_prefix_cancel {S : Stem} {k : ℕ} (P Q : Setup S k)
    (h : newWord P.position <+: newWord Q.position) :
    P.position.label = Q.position.label ∧ P.position.size = Q.position.size ∧
      P.position.entries = Q.position.entries := by
  obtain ⟨v, hv⟩ := h
  have hlen : P.position.label.length = Q.position.label.length :=
    P.label_length.trans Q.label_length.symm
  have he : P.position.label ++ (P.position.size :: (P.position.entries ++ v)) =
      Q.position.label ++ (Q.position.size :: Q.position.entries) := by
    simpa only [newWord, List.append_assoc, List.cons_append] using hv
  obtain ⟨hD, htail⟩ := List.append_inj he hlen
  obtain ⟨hn, hu⟩ := List.cons.inj htail
  refine ⟨hD, hn, (show P.position.entries <+: Q.position.entries from ⟨v, hu⟩).eq_of_length ?_⟩
  rw [P.entries_length, Q.entries_length, hD]

theorem setup_eq_of_prefix {S : Stem} {k : ℕ} (P Q : Setup S k)
    (h : newWord P.position <+: newWord Q.position) : P = Q := by
  obtain ⟨hD, hn, hu⟩ := newWord_prefix_cancel P Q h
  have hstem : P.position.stem = Q.position.stem := P.stem_eq.trans Q.stem_eq.symm
  have hpos : P.position = Q.position := by
    cases hP : P.position
    cases hQ : Q.position
    simp_all
  cases P
  cases Q
  simp_all

def support {S : Stem} {k : ℕ} (P : Setup S k) : Finset ℕ :=
  (newWord P.position).toFinset

theorem support_injective (S : Stem) (k : ℕ) : Function.Injective (support (S := S) (k := k)) := by
  intro P Q hPQ
  have hw : newWord P.position = newWord Q.position := by
    rw [← sort_toFinset_eq_self_of_pairwise (newWord_pairwise P.position),
      ← sort_toFinset_eq_self_of_pairwise (newWord_pairwise Q.position)]
    exact congrArg (fun a : Finset ℕ ↦ a.sort (· ≤ ·)) hPQ
  exact setup_eq_of_prefix P Q (hw ▸ List.prefix_rfl)

def family (S : Stem) (k : ℕ) : Set (Finset ℕ) := Set.range (support (S := S) (k := k))

theorem family_thin (S : Stem) (k : ℕ) : NashWilliams.FinThin (family S k) := by
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩ hPQ
  have hp := (pairwise_isPrefix_iff_initSeg (newWord_pairwise P.position)
    (newWord_pairwise Q.position)).2 hPQ
  exact congrArg support (setup_eq_of_prefix P Q hp)

theorem setup_above (S : Stem) (k : ℕ) (hroom : S.done.length + 1 < S.root)
    {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ P : Setup S k, ∀ x ∈ newWord P.position, x ∈ H ∧ b < x := by
  obtain ⟨P, v, hS, hD, hu, _, _, hdec, _, _, hfresh⟩ := start_body S hH b k hroom
  have hw : P.label ++ v = newWord P := by
    have he : S.decorated ++ (P.label ++ v) = S.decorated ++ newWord P := by
      rw [← hdec]
      change P.stem.decorated ++ newWord P = _
      rw [hS]
    exact List.append_cancel_left he
  exact ⟨⟨P, hS, hD, hu⟩, fun x hx ↦ hfresh x (hw ▸ hx)⟩

theorem family_hits (S : Stem) (k : ℕ) (hroom : S.done.length + 1 < S.root)
    {H : Set ℕ} (hH : H.Infinite) :
    ∃ a ∈ family S k, (↑a : Set ℕ) ⊆ H := by
  obtain ⟨P, hP⟩ := setup_above S k hroom hH 0
  exact ⟨support P, ⟨P, rfl⟩, fun x hx ↦ (hP x (List.mem_toFinset.mp hx)).1⟩

def responseFamily (S : Stem) (k : ℕ) (hroom : S.done.length + 1 < S.root) :
    RamseyGame.ResponseFamily where
  members := family S k
  thin := family_thin S k
  hits := fun _ hH ↦ family_hits S k hroom hH

noncomputable def supportEquiv (S : Stem) (k : ℕ) : Setup S k ≃ family S k :=
  Equiv.ofInjective support (support_injective S k)

@[simp] theorem supportEquiv_apply {S : Stem} {k : ℕ} (P : Setup S k) :
    (supportEquiv S k P).1 = support P := rfl

@[simp] theorem support_symm {S : Stem} {k : ℕ} (a : family S k) :
    support ((supportEquiv S k).symm a) = a.1 :=
  congrArg Subtype.val ((supportEquiv S k).apply_symm_apply a)

theorem setup_decorated {S : Stem} {k : ℕ} (P : Setup S k) :
    P.position.decorated = S.decorated ++ newWord P.position := by
  change P.position.stem.decorated ++ newWord P.position = _
  rw [P.stem_eq]

theorem setup_ordinary {S : Stem} {k : ℕ} (P : Setup S k) :
    P.position.ordinary = S.ordinary ++ P.position.size :: P.position.entries := by
  change P.position.stem.ordinary ++ _ = _
  rw [P.stem_eq]

end Erdos118.BodyResponses
