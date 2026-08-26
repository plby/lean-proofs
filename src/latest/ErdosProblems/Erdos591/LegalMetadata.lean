import ErdosProblems.Erdos591.LegalAtoms
import ErdosProblems.Erdos591.AtomicTrace

/-!
# Persistence and recovery of labels along legal words

Once the root is read, body labels only accumulate. Thus a marker's
label is recoverable from its fixed slot in every later cursor. Together
with empty leaf labels, this proves that the final coordinate word and
final root/body labels determine the entire legal atomic run.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem read_bodyLabels_prefix {w v : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (hr : w.read D n = some v) (hw : w.parser ≠ .start) :
    List.IsPrefix w.bodyLabels v.bodyLabels := by
  cases hs : Parser.step w.parser n with
  | none => simp [LabeledWord.read, hs] at hr
  | some p =>
      have heq : w.record D n p = v := by simpa [LabeledWord.read, hs] using hr
      subst v
      cases hp : w.parser with
      | start => exact (hw hp).elim
      | blocks r =>
          cases r with
          | zero => simp [hp, Parser.step] at hs
          | succ r => simp [record, hp]
      | leaves r k => exact ⟨[], by simp [record, hp]⟩

theorem LegalRun.bodyLabels_prefix {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hw : w.parser ≠ .start) :
    List.IsPrefix w.bodyLabels v.bodyLabels := by
  induction h with
  | nil => exact ⟨[], by simp⟩
  | cons w D n u xs last _ hr _ ih =>
      exact (read_bodyLabels_prefix hr hw).trans (ih (read_parser_ne_start hr))

theorem getD_of_prefix_singleton {α : Type*} (d : α) {pre xs : List α} {a : α}
    (h : List.IsPrefix (pre ++ [a]) xs) : xs.getD pre.length d = a := by
  obtain ⟨rest, rfl⟩ := h
  rw [List.append_assoc, List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem rootLabel_after_read {w u v : LabeledWord} {D : Finset ℕ} {n : ℕ}
    {xs : List (Finset ℕ × ℕ)} (hr : w.read D n = some u)
    (h : LegalRun u xs v) (hs : w.parser = .start) : v.rootLabel = D := by
  rw [h.rootLabel_eq (read_parser_ne_start hr)]
  have heq : w.record D n (.blocks n) = u := by
    simpa [LabeledWord.read, hs, Parser.step] using hr
  subst u
  simp [record, hs]

theorem bodyLabel_after_read {w u v : LabeledWord} {D : Finset ℕ} {n r : ℕ}
    {xs : List (Finset ℕ × ℕ)} (hr : w.read D n = some u)
    (h : LegalRun u xs v) (hs : w.parser = .blocks (r + 1)) :
    v.bodyLabels.getD w.bodyLabels.length ∅ = D := by
  have heq : w.record D n (Parser.normalize r n) = u := by
    simpa [LabeledWord.read, hs, Parser.step] using hr
  have hp := h.bodyLabels_prefix (read_parser_ne_start hr)
  rw [← heq] at hp
  have hp' : List.IsPrefix (w.bodyLabels ++ [D]) v.bodyLabels := by
    simpa [record, hs] using hp
  exact getD_of_prefix_singleton ∅ hp'

theorem LegalRun.values_eq {w v u : LabeledWord} {xs ys : List (Finset ℕ × ℕ)}
    (hx : LegalRun w xs v) (hy : LegalRun w ys u) (hc : v.coordinates = u.coordinates) :
    xs.map Prod.snd = ys.map Prod.snd := by
  have hx' := runAtoms_coordinates hx.run
  have hy' := runAtoms_coordinates hy.run
  exact List.append_cancel_left (hx'.symm.trans (hc.trans hy'))

/-- No label information can be silently changed when replacing a
legal run by a canonical one with the same final data. -/
theorem LegalRun.atoms_unique {w v u : LabeledWord} {xs ys : List (Finset ℕ × ℕ)}
    (hx : LegalRun w xs v) (hy : LegalRun w ys u)
    (hc : v.coordinates = u.coordinates) (hroot : v.rootLabel = u.rootLabel)
    (hbody : v.bodyLabels = u.bodyLabels) : xs = ys := by
  have hv := hx.values_eq hy hc
  induction hx generalizing ys u with
  | nil w =>
      have heq : ys = [] := List.map_eq_nil_iff.mp hv.symm
      exact heq.symm
  | cons w D n a xs v hD hr htail ih =>
      cases hy with
      | nil => simp at hv
      | cons w E m c ys u hE hs htail' =>
          have hnm : n = m := (List.cons.inj hv).1
          subst m
          have hDE : D = E := by
            cases hp : w.parser with
            | start =>
                exact (rootLabel_after_read hr htail hp).symm.trans
                  (hroot.trans (rootLabel_after_read hs htail' hp))
            | blocks r =>
                cases r with
                | zero => simp [LabeledWord.read, hp, Parser.step] at hr
                | succ r =>
                    exact (bodyLabel_after_read hr htail hp).symm.trans
                      ((congrArg (fun ls => ls.getD w.bodyLabels.length ∅) hbody).trans
                        (bodyLabel_after_read hs htail' hp))
            | leaves r k =>
                have hd : D = ∅ := by simpa [AllowedLabel, hp] using hD.2
                have he : E = ∅ := by simpa [AllowedLabel, hp] using hE.2
                exact hd.trans he.symm
          subst E
          have hac : a = c := Option.some.inj (hr.symm.trans hs)
          subst c
          have htailEq := ih htail' hc hroot hbody (List.cons.inj hv).2
          exact congrArg (List.cons (D, n)) htailEq

#print axioms LegalRun.bodyLabels_prefix
#print axioms bodyLabel_after_read
#print axioms LegalRun.atoms_unique

end Erdos591.Positive.Game.LabeledWord
