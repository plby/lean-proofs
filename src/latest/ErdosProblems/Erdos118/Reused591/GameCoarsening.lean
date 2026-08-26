import ErdosProblems.Erdos118.Reused591.LabeledWord
import Mathlib.Data.List.Forall2

namespace Erdos118.Reused591

/-!
# Deleting labels does not create decision events

Coarsening keeps the literal word and its parser counters unchanged and
only deletes root or body label values. It preserves the cursor
invariants and cannot introduce a new relaxed or selected-marker event.
-/

namespace Erdos591.Positive.Game.LabeledWord

structure Coarsens (c f : LabeledWord) : Prop where
  parser_eq : c.parser = f.parser
  coordinates_eq : c.coordinates = f.coordinates
  root_subset : c.rootLabel ⊆ f.rootLabel
  body_relation : List.Forall₂ (fun D E : Finset ℕ => D ⊆ E) c.bodyLabels f.bodyLabels
  leaf_eq : c.leafIndex = f.leafIndex
  rootMarker_eq : c.rootMarker = f.rootMarker
  bodyMarker_eq : c.bodyMarker = f.bodyMarker

theorem forall₂_last_subset {cs fs : List (Finset ℕ)}
    (h : List.Forall₂ (fun D E : Finset ℕ => D ⊆ E) cs fs)
    {D E : Finset ℕ} (hDE : D ⊆ E) : cs.getLastD D ⊆ fs.getLastD E := by
  induction h generalizing D E with
  | nil => exact hDE
  | cons hhead htail ih =>
      rw [List.getLastD_cons, List.getLastD_cons]
      exact ih hhead

theorem Coarsens.body_length {c f : LabeledWord} (h : Coarsens c f) :
    c.bodyLabels.length = f.bodyLabels.length := h.body_relation.length_eq

theorem Coarsens.current_subset {c f : LabeledWord} (h : Coarsens c f) :
    c.currentLabel ⊆ f.currentLabel :=
  forall₂_last_subset h.body_relation (Finset.Subset.refl ∅)

theorem Coarsens.refl (w : LabeledWord) : Coarsens w w :=
  ⟨rfl, rfl, Finset.Subset.refl _, List.forall₂_same.mpr (fun _ _ => Finset.Subset.refl _),
    rfl, rfl, rfl⟩

theorem Coarsens.terminal_eq {c f : LabeledWord} (h : Coarsens c f) :
    c.terminal = f.terminal := by
  simp [terminal, h.parser_eq]

theorem Coarsens.relaxed_mono {c f : LabeledWord} (h : Coarsens c f)
    (hc : c.relaxed = true) : f.relaxed = true := by
  have hc' : 0 < c.leafIndex ∧ c.bodyLabels.length ∈ c.rootLabel ∧
      c.leafIndex ∈ c.currentLabel := by simpa [relaxed] using hc
  have hr := h.root_subset hc'.2.1
  have hd := h.current_subset hc'.2.2
  have hp := hc'.1
  rw [h.body_length] at hr
  rw [h.leaf_eq] at hd hp
  simpa [relaxed] using (show 0 < f.leafIndex ∧ f.bodyLabels.length ∈ f.rootLabel ∧
    f.leafIndex ∈ f.currentLabel from ⟨hp, hr, hd⟩)

theorem Coarsens.marker_mono {c f : LabeledWord} (h : Coarsens c f)
    (hc : c.markerEvent = true) : f.markerEvent = true := by
  cases hs : f.parser with
  | start => simp [markerEvent, h.parser_eq, hs] at hc
  | leaves r b => simp [markerEvent, h.parser_eq, hs] at hc
  | blocks r =>
      cases r with
      | zero => simp [markerEvent, h.parser_eq, hs] at hc
      | succ r =>
          have hi : c.bodyLabels.length + 1 ∈ c.rootLabel := by
            simpa [markerEvent, h.parser_eq, hs] using hc
          have hf := h.root_subset hi
          rw [h.body_length] at hf
          simpa [markerEvent, hs] using hf

theorem Coarsens.event_mono {c f : LabeledWord} (h : Coarsens c f)
    (hc : c.event = true) : f.event = true := by
  have he : c.terminal = true ∨ c.relaxed = true ∨ c.markerEvent = true := by
    simpa [event, or_assoc] using hc
  have hf : f.terminal = true ∨ f.relaxed = true ∨ f.markerEvent = true := by
    rcases he with ht | hr | hm
    · exact Or.inl (h.terminal_eq ▸ ht)
    · exact Or.inr (Or.inl (h.relaxed_mono hr))
    · exact Or.inr (Or.inr (h.marker_mono hm))
  simpa [event, or_assoc] using hf

theorem Coarsens.cursorInvariant {c f : LabeledWord} (h : Coarsens c f)
    (hf : f.CursorInvariant) : c.CursorInvariant := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Parsed, h.coordinates_eq, h.parser_eq] using hf.1
  · simpa only [Counters, h.body_length, h.parser_eq, h.leaf_eq,
      h.rootMarker_eq, h.bodyMarker_eq] using hf.2.1
  · refine ⟨?_, ?_⟩
    · intro i hi
      simpa only [h.rootMarker_eq] using hf.2.2.1 i (h.root_subset hi)
    · intro j hj
      simpa only [h.bodyMarker_eq] using hf.2.2.2 j (h.current_subset hj)

theorem Coarsens.record {c f : LabeledWord} (h : Coarsens c f)
    {D E : Finset ℕ} (hDE : D ⊆ E) (n : ℕ) (s : Parser.State) :
    Coarsens (c.record D n s) (f.record E n s) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [LabeledWord.record, h.coordinates_eq]
  · cases hs : f.parser <;>
      simp only [LabeledWord.record, h.parser_eq, hs]
    · exact hDE
    · exact h.root_subset
    · exact h.root_subset
  · cases hs : f.parser with
    | start => simp [LabeledWord.record, h.parser_eq, hs]
    | leaves r b => simpa only [LabeledWord.record, h.parser_eq, hs] using h.body_relation
    | blocks r =>
        cases r with
        | zero => simpa only [LabeledWord.record, h.parser_eq, hs] using h.body_relation
        | succ r =>
            simpa only [LabeledWord.record, h.parser_eq, hs] using
              List.rel_append h.body_relation (List.Forall₂.cons hDE List.Forall₂.nil)
  · cases hs : f.parser <;> simp [LabeledWord.record, h.parser_eq, hs, h.leaf_eq]
  · cases hs : f.parser <;> simp [LabeledWord.record, h.parser_eq, hs, h.rootMarker_eq]
  · cases hs : f.parser with
    | start => simp [LabeledWord.record, h.parser_eq, hs]
    | leaves r b => simp [LabeledWord.record, h.parser_eq, hs, h.bodyMarker_eq]
    | blocks r =>
        cases r <;> simp [LabeledWord.record, h.parser_eq, hs, h.bodyMarker_eq]

theorem Coarsens.read {c f c' f' : LabeledWord} (h : Coarsens c f)
    {D E : Finset ℕ} {n : ℕ} (hDE : D ⊆ E)
    (hc : c.read D n = some c') (hf : f.read E n = some f') : Coarsens c' f' := by
  cases hs : Parser.step f.parser n with
  | none => simp [LabeledWord.read, hs] at hf
  | some s =>
      have hce : c.record D n s = c' := by
        simpa [LabeledWord.read, h.parser_eq, hs] using hc
      have hfe : f.record E n s = f' := by
        simpa [LabeledWord.read, hs] using hf
      subst c'
      subst f'
      exact h.record hDE n s

#print axioms Coarsens.event_mono
#print axioms Coarsens.read

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
