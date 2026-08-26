import ErdosProblems.Erdos591.MacroParser
import ErdosProblems.Erdos591.AtomicInterleave
import ErdosProblems.Erdos591.FastSequence

/-!
# Faithful atomic certificates for macro-extensions

The parser's numerical input is recovered exactly as labeled atoms.
Every read is legal, its label has the prescribed size, and no proper
nonempty prefix stops at a selected leaf or at completion.
-/

namespace Erdos591.Positive.Game

namespace Atomic

def tag (side : Bool) (xs : List (Finset ℕ × ℕ)) : List Atom :=
  xs.map fun a => ⟨side, a.1, a.2⟩

@[simp] theorem tag_nil (side : Bool) : tag side [] = [] := rfl

@[simp] theorem tag_cons (side : Bool) (D : Finset ℕ) (n : ℕ) (xs : List (Finset ℕ × ℕ)) :
    tag side ((D, n) :: xs) = ⟨side, D, n⟩ :: tag side xs := rfl

@[simp] theorem tag_append (side : Bool) (xs ys : List (Finset ℕ × ℕ)) :
    tag side (xs ++ ys) = tag side xs ++ tag side ys := List.map_append

end Atomic

namespace Macro

inductive Extension (q : ℕ) : LabeledWord → List (Finset ℕ × ℕ) → LabeledWord → Prop
  | stop (w : LabeledWord) (D : Finset ℕ) (n : ℕ) (v : LabeledWord)
      (hlabel : w.AllowedLabel D n) (hread : w.read D n = some v)
      (hsize : D.card = labelSize q w)
      (hend : v.terminal = true ∨ v.relaxed = true) : Extension q w [(D, n)] v
  | more (w : LabeledWord) (D : Finset ℕ) (n : ℕ) (v : LabeledWord)
      (xs : List (Finset ℕ × ℕ)) (last : LabeledWord)
      (hlabel : w.AllowedLabel D n) (hread : w.read D n = some v)
      (hsize : D.card = labelSize q w)
      (hcontinue : ¬ (v.terminal = true ∨ v.relaxed = true))
      (htail : Extension q v xs last) : Extension q w ((D, n) :: xs) last

theorem Extension.legal {q : ℕ} {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q w xs v) : LabeledWord.LegalRun w xs v := by
  induction h with
  | stop w D n v hl hr _ _ => exact .cons w D n v [] v hl hr (.nil v)
  | more w D n v xs last hl hr _ _ _ ih => exact .cons w D n v xs last hl hr ih

theorem Extension.end {q : ℕ} {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q w xs v) : v.terminal = true ∨ v.relaxed = true := by
  induction h with
  | stop _ _ _ _ _ _ _ hv => exact hv
  | more _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem Extension.nonempty {q : ℕ} {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q w xs v) : xs ≠ [] := by
  cases h <;> simp

theorem Extension.label_sizes {q : ℕ} {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q w xs v) : ∀ a ∈ xs, a.1.card ≤ q := by
  induction h with
  | stop w D n v _ _ hsize _ =>
      intro a ha
      have heq : a = (D, n) := by simpa using ha
      subst a
      exact hsize ▸ labelSize_le q w
  | more w D n v xs last _ _ hsize _ _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hsize ▸ labelSize_le q w
      · exact ih a ha

theorem Extension.decreases {q : ℕ} {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q w xs v) : Parser.potential v.parser < Parser.potential w.parser := by
  induction h with
  | stop _ _ _ _ _ hr _ _ => exact LabeledWord.read_decreases hr
  | more _ _ _ _ _ _ _ hr _ _ _ ih => exact ih.trans (LabeledWord.read_decreases hr)

theorem Extension.increasing {q : ℕ} {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q w xs v) (side : Bool) (hw : w.coordinates.Pairwise (· < ·))
    (hxs : (Atomic.inputs (Atomic.tag side xs)).Pairwise (· < ·))
    (hsep : ∀ x ∈ w.coordinates, ∀ y ∈ Atomic.inputs (Atomic.tag side xs), x < y) :
    v.coordinates.Pairwise (· < ·) := by
  have hsub : List.Sublist (xs.map Prod.snd) (Atomic.inputs (Atomic.tag side xs)) := by
    simpa [Atomic.tag, List.map_map, Function.comp_def] using
      Atomic.values_sublist_inputs (Atomic.tag side xs)
  rw [LabeledWord.runAtoms_coordinates h.legal.run]
  exact List.pairwise_append.mpr ⟨hw, hxs.sublist hsub,
    fun x hx y hy => hsep x hx y (hsub.subset hy)⟩

theorem run_extension (q : ℕ) (side : Bool) (w : Unfinished) (xs : List ℕ)
    (last : LabeledWord) (hinc : xs.Pairwise (· < ·)) (hpos : ∀ x ∈ xs, 0 < x)
    (h : (parser q).run (start q w) xs = some (.done last)) :
    ∃ atoms, Extension q w.val atoms last ∧ xs = Atomic.inputs (Atomic.tag side atoms) := by
  obtain ⟨labels, n, rest, v, hxs, hlen, hr, ht⟩ :=
    run_prelude q w (labelSize q w.val) [] xs (.done last) h
  have hp : (labels ++ n :: rest).Pairwise (· < ·) := hxs ▸ hinc
  have hlabels := (List.pairwise_append.mp hp).1
  have hrest := (List.pairwise_cons.mp (List.pairwise_append.mp hp).2.1).2
  have hcard : labels.toFinset.card = labelSize q w.val :=
    (List.toFinset_card_of_nodup hlabels.nodup).trans hlen
  have hbound : ∀ i ∈ labels.toFinset, 0 < i ∧ i < n := by
    intro i hi
    have hi' : i ∈ labels := List.mem_toFinset.mp hi
    refine ⟨hpos i ?_, (List.pairwise_append.mp hp).2.2 i hi' n (by simp)⟩
    rw [hxs]
    exact List.mem_append_left _ hi'
  have hlegal : w.val.AllowedLabel labels.toFinset n :=
    LabeledWord.allowedLabel_of_size (labelSize_allowed q w) hcard hbound
  have hread : w.val.read labels.toFinset n = some v := by simpa using hr
  have hsort : labels.toFinset.sort (· ≤ ·) = labels :=
    Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hlabels
  by_cases hstop : v.terminal = true ∨ v.relaxed = true
  · have ht' : (parser q).run (.done v) rest = some (.done last) := by
      simpa [resume, hstop] using ht
    have hnil : rest = [] := (parser q).run_nil_of_stopped rfl ht'
    subst rest
    have hlast : v = last := by
      simpa [ResponseParser.run, parser, stopped] using ht'
    subst last
    refine ⟨[(labels.toFinset, n)], .stop w.val _ n v hlegal hread hcard hstop, ?_⟩
    simpa [Atomic.tag, Atomic.inputs, Atomic.Atom.inputs, hsort] using hxs
  · have hv : v.terminal = false := by cases hh : v.terminal <;> simp_all
    have ht' : (parser q).run (start q ⟨v, hv⟩) rest = some (.done last) := by
      simpa [resume, hstop, start] using ht
    have hpos' : ∀ x ∈ rest, 0 < x := by
      intro x hx
      apply hpos x
      rw [hxs]
      exact List.mem_append_right _ (List.mem_cons_of_mem n hx)
    obtain ⟨atoms, hext, hraw⟩ := run_extension q side ⟨v, hv⟩ rest last hrest hpos' ht'
    refine ⟨(labels.toFinset, n) :: atoms,
      .more w.val _ n v atoms last hlegal hread hcard hstop hext, ?_⟩
    simpa [Atomic.Atom.inputs, hsort, hraw, List.append_assoc] using hxs
termination_by xs.length
decreasing_by
  have hlen' := congrArg List.length hxs
  simp only [List.length_append, List.length_cons] at hlen'
  omega

/-- An uninterrupted macro-extension exists on every infinite pool.
Its complete numerical input is exactly the flattened atom list. -/
theorem extension_exists (q : ℕ) (side : Bool) (w : Unfinished) {H : Set ℕ}
    (hH : H.Infinite) (hpos : ∀ x ∈ H, 0 < x) :
    ∃ atoms last,
      Extension q w.val atoms last ∧
      (Atomic.inputs (Atomic.tag side atoms)).Pairwise (· < ·) ∧
      (∀ x ∈ Atomic.inputs (Atomic.tag side atoms), x ∈ H) := by
  obtain ⟨u, ⟨t, ht⟩, huH⟩ := responses_exist q w hH
  obtain ⟨last, heq, _⟩ := run_end q w (labelSize q w.val) [] (u.sort (· ≤ ·)) t ht
  rw [heq] at ht
  have hinc := (Finset.sortedLT_sort u).pairwise
  have hpos' : ∀ x ∈ u.sort (· ≤ ·), 0 < x := by
    intro x hx
    exact hpos x (huH (by simpa only [Finset.mem_coe, Finset.mem_sort] using hx))
  obtain ⟨atoms, hext, hraw⟩ := run_extension q side w (u.sort (· ≤ ·)) last hinc hpos' ht
  refine ⟨atoms, last, hext, hraw ▸ hinc, ?_⟩
  intro x hx
  apply huH
  simpa only [Finset.mem_coe, ← hraw, Finset.mem_sort] using hx

/-- A finite macro-extension can be chosen above all old construction
inputs and all retrospective history bounds. The old finite support
and label-size parameter remain explicit in the result. -/
theorem spaced_extension_exists {N H : Set ℕ} (hH : H.Infinite)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) (q : ℕ) (side : Bool) (w : Unfinished) :
    ∃ atoms last,
      Extension q w.val atoms last ∧
      (Atomic.inputs (Atomic.tag side atoms)).Pairwise (· < ·) ∧
      (∀ x ∈ Atomic.inputs (Atomic.tag side atoms), x ∈ H) ∧
      (∀ x ∈ Atomic.inputs (Atomic.tag side atoms), F.sup id < x) ∧
      Atomic.Spaced b F (Atomic.tag side atoms) := by
  obtain ⟨f, hf, hfH, hb, hfresh⟩ :=
    FastSequence.exists_retrospective_sequence hH b F q
  have hM : (Set.range f).Infinite := Set.infinite_range_of_injective hf.injective
  have hMpos : ∀ x ∈ Set.range f, 0 < x := by
    rintro x ⟨n, rfl⟩
    exact (Nat.zero_le _).trans_lt (hfresh n)
  obtain ⟨atoms, last, hext, hinc, hmem⟩ := extension_exists q side w hM hMpos
  refine ⟨atoms, last, hext, hinc, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := hmem x hx
    exact hfH n
  · intro x hx
    obtain ⟨n, rfl⟩ := hmem x hx
    exact hfresh n
  · apply Atomic.spaced_of_fast_sequence b F q f hf hb _ hinc hmem
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact hext.label_sizes p hp

#print axioms run_extension
#print axioms extension_exists
#print axioms spaced_extension_exists

end Macro

end Erdos591.Positive.Game
