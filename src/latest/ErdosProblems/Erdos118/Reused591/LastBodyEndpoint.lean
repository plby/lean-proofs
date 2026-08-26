import ErdosProblems.Erdos118.Reused591.SameBodyRun
import ErdosProblems.Erdos118.Reused591.NextLeafReplay

namespace Erdos118.Reused591

/-!
# Recovering an exhausted selected leaf in the already last selected body

A relaxed endpoint selects a root index. If all those indices were
already read at the start, monotonicity forces the body count to stay
constant. This recovers the full body-label list, its marker, and the
last leaf index used by a delayed upper next-leaf response.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem LegalRun.bodyMarker_of_body_length {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hw : w.parser ≠ .start)
    (hlen : v.bodyLabels.length = w.bodyLabels.length) : v.bodyMarker = w.bodyMarker := by
  induction h with
  | nil => rfl
  | cons w D n u as v _ hr ht ih =>
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
          have hmarker : u.bodyMarker = w.bodyMarker := by simp [← heq, record, hp]
          exact (ih (read_parser_ne_start hr) (by simpa [hbody] using hlen)).trans hmarker

theorem LegalRun.last_body_relaxed_labels {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hw : w.parser ≠ .start)
    (hroot : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length)
    (hrel : v.relaxed = true) :
    v.bodyLabels = w.bodyLabels ∧ v.bodyMarker = w.bodyMarker := by
  have hrootEq := h.rootLabel_eq hw
  have hupper := hroot _ (hrootEq ▸ (of_decide_eq_true hrel).2.1)
  have hpre := h.bodyLabels_prefix hw
  have hlen : v.bodyLabels.length = w.bodyLabels.length := le_antisymm hupper hpre.length_le
  exact ⟨(hpre.eq_of_length hlen.symm).symm, h.bodyMarker_of_body_length hw hlen⟩

theorem LegalRun.last_body_relaxed_endpoint {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hw : w.parser ≠ .start)
    (hroot : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length)
    (hrel : v.relaxed = true) (hlast : ¬ Macro.Pending v) :
    v.bodyLabels = w.bodyLabels ∧ v.bodyMarker = w.bodyMarker ∧
      v.leafIndex = w.currentLabel.sup id := by
  have hrootEq := h.rootLabel_eq hw
  have hdata := of_decide_eq_true hrel
  have hupper := hroot _ (hrootEq ▸ hdata.2.1)
  have hpre := h.bodyLabels_prefix hw
  have hlen : v.bodyLabels.length = w.bodyLabels.length := le_antisymm hupper hpre.length_le
  obtain ⟨tail, htail⟩ := hpre
  have htailLen : tail.length = 0 := by
    have he := congrArg List.length htail
    simp only [List.length_append] at he
    omega
  have hlabels : v.bodyLabels = w.bodyLabels := by
    simpa only [List.length_eq_zero_iff.mp htailLen, List.append_nil] using htail.symm
  have hcurrent : v.currentLabel = w.currentLabel := by simp [currentLabel, hlabels]
  have hlastIndex : v.leafIndex = v.currentLabel.sup id := by
    apply le_antisymm (Finset.le_sup (f := id) hdata.2.2)
    apply Finset.sup_le
    intro j hj
    by_contra hn
    exact hlast (Or.inr ⟨hdata.2.1, j, hj, lt_of_not_ge hn⟩)
  exact ⟨hlabels, h.bodyMarker_of_body_length hw hlen, hcurrent ▸ hlastIndex⟩

#print axioms LegalRun.bodyMarker_of_body_length
#print axioms LegalRun.last_body_relaxed_labels
#print axioms LegalRun.last_body_relaxed_endpoint

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
