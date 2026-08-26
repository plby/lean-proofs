import ErdosProblems.Erdos591.LeafGluing

/-!
# Shared completion tails without changing previously read labels

Two cursors may have identical structural data and different labels.
Any complete coordinate continuation of one is a complete continuation
of the other with empty new labels. This preserves the latter's old
labels, and uses its actual finish parser. Once it has no pending
selected index, the existing command equivalence also covers advance.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

structure SameStructure (c f : LabeledWord) : Prop where
  parser_eq : c.parser = f.parser
  coordinates_eq : c.coordinates = f.coordinates
  body_length : c.bodyLabels.length = f.bodyLabels.length
  leaf_eq : c.leafIndex = f.leafIndex
  rootMarker_eq : c.rootMarker = f.rootMarker
  bodyMarker_eq : c.bodyMarker = f.bodyMarker

theorem SameStructure.refl (w : LabeledWord) : SameStructure w w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameStructure.symm {c f : LabeledWord} (h : SameStructure c f) : SameStructure f c :=
  ⟨h.parser_eq.symm, h.coordinates_eq.symm, h.body_length.symm, h.leaf_eq.symm,
    h.rootMarker_eq.symm, h.bodyMarker_eq.symm⟩

theorem SameStructure.trans {c f v : LabeledWord} (h : SameStructure c f)
    (g : SameStructure f v) : SameStructure c v :=
  ⟨h.parser_eq.trans g.parser_eq, h.coordinates_eq.trans g.coordinates_eq,
    h.body_length.trans g.body_length, h.leaf_eq.trans g.leaf_eq,
    h.rootMarker_eq.trans g.rootMarker_eq, h.bodyMarker_eq.trans g.bodyMarker_eq⟩

theorem SameStructure.record {c f : LabeledWord} (h : SameStructure c f)
    (D E : Finset ℕ) (n : ℕ) (s : Parser.State) :
    SameStructure (c.record D n s) (f.record E n s) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [LabeledWord.record, h.coordinates_eq]
  · cases hp : f.parser with
    | start => simp [LabeledWord.record, h.parser_eq, hp]
    | leaves r k => simpa [LabeledWord.record, h.parser_eq, hp] using h.body_length
    | blocks r =>
        cases r <;> simp [LabeledWord.record, h.parser_eq, hp, h.body_length]
  · cases hp : f.parser <;> simp [LabeledWord.record, h.parser_eq, hp, h.leaf_eq]
  · cases hp : f.parser <;> simp [LabeledWord.record, h.parser_eq, hp, h.rootMarker_eq]
  · cases hp : f.parser with
    | start => simp [LabeledWord.record, h.parser_eq, hp]
    | leaves r k => simpa [LabeledWord.record, h.parser_eq, hp] using h.bodyMarker_eq
    | blocks r =>
        cases r <;> simp [LabeledWord.record, h.parser_eq, hp, h.bodyMarker_eq]

theorem SameStructure.erase_run {c f v : LabeledWord} (h : SameStructure c f)
    {xs : List (Finset ℕ × ℕ)} (hr : f.runAtoms xs = some v) :
    ∃ z, c.runAtoms ((xs.map Prod.snd).map fun n => (∅, n)) = some z ∧ SameStructure z v := by
  induction xs generalizing c f with
  | nil =>
      have heq : f = v := Option.some.inj hr
      exact ⟨c, rfl, heq ▸ h⟩
  | cons a xs ih =>
      cases hf : f.read a.1 a.2 with
      | none => simp [runAtoms, hf] at hr
      | some u =>
          have ht : u.runAtoms xs = some v := by simpa [runAtoms, hf] using hr
          have hstep := (read_spec hf).1
          have hfu : f.record a.1 a.2 u.parser = u := by
            simpa [LabeledWord.read, hstep] using hf
          let d := c.record ∅ a.2 u.parser
          have hc : c.read ∅ a.2 = some d := by
            simp [LabeledWord.read, h.parser_eq, hstep, d]
          have hdu : SameStructure d u := by
            rw [← hfu]
            exact h.record ∅ a.1 a.2 u.parser
          obtain ⟨z, hz, hlast⟩ := ih hdu ht
          exact ⟨z, by simpa [runAtoms, hc] using hz, hlast⟩

theorem SameStructure.of_runs {c f v u : LabeledWord} (h : SameStructure c f)
    {xs ys : List (Finset ℕ × ℕ)} (hx : c.runAtoms xs = some v)
    (hy : f.runAtoms ys = some u) (hvalues : xs.map Prod.snd = ys.map Prod.snd) :
    SameStructure v u := by
  obtain ⟨z, hz, hzv⟩ := (SameStructure.refl c).erase_run hx
  obtain ⟨t, ht, htu⟩ := h.erase_run hy
  rw [hvalues] at hz
  have heq : z = t := Option.some.inj (hz.symm.trans ht)
  subst t
  exact hzv.symm.trans htu

theorem sameStructure_of_initial_runs {v u : LabeledWord}
    {xs ys : List (Finset ℕ × ℕ)} (hx : initial.runAtoms xs = some v)
    (hy : initial.runAtoms ys = some u) (hcoords : v.coordinates = u.coordinates) :
    SameStructure v u := by
  have hvalues : xs.map Prod.snd = ys.map Prod.snd := by
    simpa [initial] using (runAtoms_coordinates hx).symm.trans
      (hcoords.trans (runAtoms_coordinates hy))
  exact (SameStructure.refl initial).of_runs hx hy hvalues

theorem finish_of_zero_atoms {w v : LabeledWord} {xs : List ℕ}
    (hr : w.runAtoms (xs.map fun n => (∅, n)) = some v) (hv : v.terminal = true) :
    finishParser.run w xs = some v := by
  apply response_eq_of_endpoint_parser finishParser (fun _ _ => rfl) hr hv
  intro _front _tail u _hxs hu _ht
  have hu' : u.parser = .blocks 0 := by
    simpa [finishParser, terminal] using finishParser.run_stopped hu
  have hv' : v.parser = .blocks 0 := by simpa [terminal] using hv
  exact hu'.trans hv'.symm

theorem SameStructure.finish_from_run {c f v : LabeledWord} (h : SameStructure c f)
    {xs : List (Finset ℕ × ℕ)} (hr : f.runAtoms xs = some v) (hv : v.terminal = true) :
    ∃ z, finishParser.run c (xs.map Prod.snd) = some z ∧ SameStructure z v := by
  obtain ⟨z, hz, hsame⟩ := h.erase_run hr
  have hterm : z.terminal = true := by simpa [terminal, hsame.parser_eq] using hv
  exact ⟨z, finish_of_zero_atoms hz hterm, hsame⟩

theorem rootRelabel_sameStructure (C : Finset ℕ) (w : LabeledWord) :
    SameStructure (rootRelabel C w) w := by
  exact ⟨rfl, rfl, List.length_replicate, rfl, rfl, rfl⟩

theorem SameStructure.bodyLeafCursor {w v : LabeledWord} (h : SameStructure w v)
    (D E : Finset ℕ) (n r : ℕ) (xs : List ℕ) :
    SameStructure (bodyLeafCursor w D n r xs) (bodyLeafCursor v E n r xs) := by
  refine ⟨rfl, ?_, ?_, rfl, h.rootMarker_eq, rfl⟩
  · simp [LabeledWord.bodyLeafCursor, h.coordinates_eq]
  · simp [LabeledWord.bodyLeafCursor, h.body_length]

end LabeledWord

theorem Reply.finish_shared_tail (board : Board) (side : Bool)
    {f v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (hlegal : (board.get side).terminal = false)
    (hsame : LabeledWord.SameStructure (board.get side) f)
    (hr : f.runAtoms xs = some v) (hv : v.terminal = true)
    (hinc : (xs.map Prod.snd).Pairwise (· < ·)) :
    ∃ z, Reply board ⟨side, .finish⟩ (xs.map Prod.snd).toFinset (board.update side z) ∧
      LabeledWord.SameStructure z v := by
  obtain ⟨z, hz, hlast⟩ := hsame.finish_from_run hr hv
  refine ⟨z, Reply.finish side _ z hlegal ?_, hlast⟩
  simpa only [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc] using hz

theorem Reply.not_pending_shared_tail (board : Board) (r : Request)
    {f v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (hlegal : r.Legal board) (hstart : (board.get r.side).parser ≠ .start)
    (hp : ¬ Macro.Pending (board.get r.side))
    (hsame : LabeledWord.SameStructure (board.get r.side) f)
    (hr : f.runAtoms xs = some v) (hv : v.terminal = true)
    (hinc : (xs.map Prod.snd).Pairwise (· < ·)) :
    ∃ z, Reply board r (xs.map Prod.snd).toFinset (board.update r.side z) ∧
      LabeledWord.SameStructure z v := by
  have hlive : (board.get r.side).terminal = false := by
    cases hc : r.command with
    | finish => simpa [Request.Legal, hc] using hlegal
    | advance d => exact (show (board.get r.side).AllowedSize d by
        simpa [Request.Legal, hc] using hlegal).1
  obtain ⟨z, hz, hlast⟩ := Reply.finish_shared_tail board r.side hlive
    hsame hr hv hinc
  exact ⟨z, (Reply.not_pending_iff_finish board r _ _ hlegal hstart hp).mpr hz, hlast⟩

#print axioms LabeledWord.SameStructure.finish_from_run
#print axioms Reply.not_pending_shared_tail

end Erdos591.Positive.Game
