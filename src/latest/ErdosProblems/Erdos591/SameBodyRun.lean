import ErdosProblems.Erdos591.TargetLeaf
import ErdosProblems.Erdos591.CutPersistence

/-!
# Exact leaf counts along an unchanged body-label prefix

After the root is fixed, a legal atomic run with no increase in the
number of body labels cannot contain a body-marker read. Every atom is
therefore a leaf read, so its length is exactly the leaf-counter increase.
This recovers the coordinate prefix used in last--first leaf gluing.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem LegalRun.leafIndex_of_body_length {w v : LabeledWord}
    {xs : List (Finset ℕ × ℕ)} (h : LegalRun w xs v) (hw : w.parser ≠ .start)
    (hlen : v.bodyLabels.length = w.bodyLabels.length) :
    v.leafIndex = w.leafIndex + xs.length := by
  induction h with
  | nil => simp
  | cons w D n u xs v _ hr ht ih =>
      cases hp : w.parser with
      | start => exact (hw hp).elim
      | blocks r =>
          cases r with
          | zero => simp [LabeledWord.read, hp, Parser.step] at hr
          | succ r =>
              have heq : w.record D n (Parser.normalize r n) = u := by
                simpa [LabeledWord.read, hp, Parser.step] using hr
              have hle := (ht.bodyLabels_prefix (read_parser_ne_start hr)).length_le
              rw [← heq] at hle
              simp only [record, hp, List.length_append, List.length_singleton] at hle
              omega
      | leaves r k =>
          have heq : w.record D n (Parser.normalize r k) = u := by
            simpa [LabeledWord.read, hp, Parser.step] using hr
          have hbody : u.bodyLabels = w.bodyLabels := by simp [← heq, record, hp]
          have hleaf : u.leafIndex = w.leafIndex + 1 := by simp [← heq, record, hp]
          have hc : v.bodyLabels.length = u.bodyLabels.length := by simpa [hbody] using hlen
          have hi := ih (read_parser_ne_start hr) hc
          simp only [List.length_cons]
          omega

theorem LegalRun.same_body_coordinates {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hw : w.parser ≠ .start)
    (hlen : v.bodyLabels.length = w.bodyLabels.length) :
    ∃ xs, v.coordinates = w.coordinates ++ xs ∧
      v.leafIndex = w.leafIndex + xs.length ∧ ∀ x ∈ xs, ∃ a ∈ as, a.2 = x := by
  refine ⟨as.map Prod.snd, runAtoms_coordinates h.run, ?_, ?_⟩
  · simpa using h.leafIndex_of_body_length hw hlen
  · intro x hx
    exact List.mem_map.mp hx

#print axioms LegalRun.leafIndex_of_body_length

end Erdos591.Positive.Game.LabeledWord
