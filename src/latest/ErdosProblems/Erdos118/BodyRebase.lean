import ErdosProblems.Erdos118.BodyResponses

/-! Keep a literal body response word and install it on an exact new stem.
The new stem's decorations must precede the entire response. -/

namespace Erdos118.BodyRebase

open LabelledExtensions BodyResponses

def setup {S : Stem} {k : ℕ} (A : Setup S k) (E : Stem)
    (hroom : E.done.length + 1 < E.root)
    (hbefore : ∀ x ∈ E.decorated, ∀ y ∈ newWord A.position, x < y) : Setup E k where
  position :=
    { stem := E, size := A.position.size, label := A.position.label
      entries := A.position.entries, room := hroom
      started := A.position.started, unfinished := A.position.unfinished
      increasing := List.pairwise_append.mpr
        ⟨E.increasing, newWord_pairwise A.position, hbefore⟩ }
  stem_eq := rfl
  label_length := A.label_length
  entries_length := A.entries_length

theorem setup_ordinary {S : Stem} {k : ℕ} (A : Setup S k) (E : Stem)
    (hroom : E.done.length + 1 < E.root)
    (hbefore : ∀ x ∈ E.decorated, ∀ y ∈ newWord A.position, x < y)
    (hord : E.ordinary = S.ordinary) : (setup A E hroom hbefore).position.ordinary =
      A.position.ordinary := by
  change E.ordinary ++ _ = A.position.stem.ordinary ++ _
  rw [A.stem_eq, hord]
  rfl

theorem setup_newWord {S : Stem} {k : ℕ} (A : Setup S k) (E : Stem)
    (hroom : E.done.length + 1 < E.root)
    (hbefore : ∀ x ∈ E.decorated, ∀ y ∈ newWord A.position, x < y) :
    newWord (setup A E hroom hbefore).position = newWord A.position := rfl

end Erdos118.BodyRebase
