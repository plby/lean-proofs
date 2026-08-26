import ErdosProblems.Erdos118.Reused591.ReplyRuns
import ErdosProblems.Erdos118.Reused591.WordPositions

namespace Erdos118.Reused591

/-!
# Permanent cuts and selected labels

Once both endpoints of a coordinate interval have been read, later
fresh responses cannot alter whether that interval is a cut. In a clear
terminal pair, an earlier relaxed cursor must end at such a cut. An
empty label at a selected body is likewise an irreparable obstruction.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

theorem LegalRun.parser_ne_start {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hw : w.parser ≠ .start) : v.parser ≠ .start := by
  induction h with
  | nil => exact hw
  | cons w D n u xs v _ hr _ ih => exact ih (read_parser_ne_start hr)

theorem LegalRun.body_getD_eq {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hw : w.parser ≠ .start) {i : ℕ}
    (hi : i < w.bodyLabels.length) : v.bodyLabels.getD i ∅ = w.bodyLabels.getD i ∅ := by
  obtain ⟨rest, heq⟩ := h.bodyLabels_prefix hw
  rw [← heq]
  exact List.getD_append _ _ _ _ hi

theorem currentLabel_eq_getD {w : LabeledWord} {i : ℕ}
    (hi : w.bodyLabels.length = i + 1) : w.currentLabel = w.bodyLabels.getD i ∅ := by
  simp only [currentLabel, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.getD_eq_getElem?_getD, hi, Nat.add_sub_cancel]

theorem relaxed_ne_start {w : LabeledWord} (hw : w.CursorInvariant)
    (hr : w.relaxed = true) : w.parser ≠ .start := by
  have hout := relaxed_outstanding hw.2.1 hw.2.2 hr
  intro heq
  simp [heq, outstandingBodies, outstandingLeaves] at hout

end LabeledWord

namespace Payoff

open Erdos591.Negative.Exact

theorem cut_append_iff {xs ys us vs : List ℕ} {k B : ℕ}
    (hk : k + 1 < xs.length) (hb : xs.getD (k + 1) 0 ≤ B)
    (hv : ∀ y ∈ vs, B < y) : Cut (xs ++ us) (ys ++ vs) k ↔ Cut xs ys k := by
  have hxk : k < xs.length := by omega
  simp only [Cut, List.getD_append _ _ _ _ hxk, List.getD_append _ _ _ _ hk]
  constructor
  · rintro ⟨_, y, hy, hlo, hhi⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨hk, y, hy, hlo, hhi⟩
    · exact (not_lt_of_ge hb (lt_trans (hv y hy) hhi)).elim
  · rintro ⟨_, y, hy, hlo, hhi⟩
    exact ⟨by simp only [List.length_append]; omega,
      y, List.mem_append_left _ hy, hlo, hhi⟩

theorem history_cut_iff {N : Set ℕ} {p q : Concrete.Hist N}
    (h : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    (side : Bool) {k : ℕ} (hk : k + 1 < (p.position.board.get side).coordinates.length) :
    Cut (q.position.board.get side).coordinates (q.position.board.get (!side)).coordinates k ↔
      Cut (p.position.board.get side).coordinates (p.position.board.get (!side)).coordinates k := by
  obtain ⟨_, hext⟩ := History.reachable_word_extension h
  obtain ⟨as, has, _⟩ := hext side
  obtain ⟨bs, hbs, hbf⟩ := hext (!side)
  rw [LabeledWord.runAtoms_coordinates has.run, LabeledWord.runAtoms_coordinates hbs.run]
  apply cut_append_iff hk (B := p.position.bound)
  · apply ((Position.history_dataInvariant p).1 _ ?_).2.2
    apply p.position.board.get_support_subset side
    apply LabeledWord.coordinate_mem_support
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    exact hbf a ha

theorem ClearSide.selected_body_label_nonempty {w u v : LabeledWord} {s t : G}
    {D : Finset ℕ} {n r : ℕ} {xs : List (Finset ℕ × ℕ)}
    (hclear : ClearSide v s t) (hread : w.read D n = some u)
    (htail : LabeledWord.LegalRun u xs v) (hp : w.parser = .blocks (r + 1))
    (hsel : w.bodyLabels.length + 1 ∈ w.rootLabel) : D.Nonempty := by
  have hstart : w.parser ≠ .start := by simp [hp]
  have hroot := (htail.rootLabel_eq (LabeledWord.read_parser_ne_start hread)).trans
    (LabeledWord.read_rootLabel_eq hread hstart)
  have hpre := htail.bodyLabels_prefix (LabeledWord.read_parser_ne_start hread)
  have heq : w.record D n (Parser.normalize r n) = u := by
    simpa [LabeledWord.read, hp, Parser.step] using hread
  have hi : w.bodyLabels.length < s.val.length := by
    have hlen := hpre.length_le
    rw [← heq] at hlen
    simpa [LabeledWord.record, hp, hclear.labels_length] using hlen
  have hmem : w.bodyLabels.length + 1 ∈ v.rootLabel := by rw [hroot]; exact hsel
  have hnon := (hclear.root_mem_iff_body_nonempty hi).mp hmem
  simpa only [LabeledWord.bodyLabel_after_read hread htail hp] using hnon

theorem ClearSide.cut_of_relaxed_prefix {w v : LabeledWord} {s t : G}
    {as bs : List (Finset ℕ × ℕ)} {k : ℕ}
    (hclear : ClearSide v s t) (hw : LabeledWord.LegalRun LabeledWord.initial as w)
    (htail : LabeledWord.LegalRun w bs v) (hlen : w.coordinates.length = k + 1)
    (hr : w.relaxed = true) : Cut (word s.val) (word t.val) k := by
  have hpref : List.IsPrefix w.coordinates (word s.val) := by
    simpa only [hclear.coordinates] using htail.coordinates_prefix
  have hk : k < (word s.val).length := by
    have hh := hpref.length_le
    omega
  have hcoords : w.coordinates = (word s.val).take (k + 1) := by
    simpa only [hlen] using List.prefix_iff_eq_take.mp hpref
  obtain ⟨i, j, hi, _, hI, hJ, _, _, hpos⟩ :=
    LabeledCode.relaxed_prefix_indices hw s.val k hcoords hk hr
  have hsel : 0 < w.leafIndex ∧ w.bodyLabels.length ∈ w.rootLabel ∧
      w.leafIndex ∈ w.currentLabel := by simpa [LabeledWord.relaxed] using hr
  have hstart := LabeledWord.relaxed_ne_start
    (hw.cursorInvariant LabeledWord.cursorInvariant_initial) hr
  have hD : j + 1 ∈ v.bodyLabels.getD i ∅ := by
    rw [htail.body_getD_eq hstart (by omega), ← LabeledWord.currentLabel_eq_getD hI, ← hJ]
    exact hsel.2.2
  have hcut := (hclear.body_exact i hi j).mp hD
  exact hpos ▸ hcut.2.2

theorem ClearSide.relaxed_of_cut_prefix {w v : LabeledWord} {s t : G}
    {as bs : List (Finset ℕ × ℕ)} {k : ℕ}
    (hclear : ClearSide v s t) (hw : LabeledWord.LegalRun LabeledWord.initial as w)
    (htail : LabeledWord.LegalRun w bs v) (hlen : w.coordinates.length = k + 1)
    (hcut : Cut (word s.val) (word t.val) k) : w.relaxed = true := by
  obtain ⟨i, j, hij, hpos⟩ := hclear.all_cuts_leaves k hcut
  have hpref : List.IsPrefix w.coordinates (word s.val) := by
    simpa only [hclear.coordinates] using htail.coordinates_prefix
  have hcoords : w.coordinates = (word s.val).take (leafPosition s.val i j + 1) := by
    simpa only [hlen, hpos] using List.prefix_iff_eq_take.mp hpref
  have hvalues : as.map Prod.snd = w.coordinates := by
    simpa [LabeledWord.initial] using (LabeledWord.runAtoms_coordinates hw.run).symm
  obtain ⟨z, hz, hI, hJ⟩ := LabeledCode.leaf_prefix_counters s.val i j hij.1 hij.2.1
  have hcomp : LabeledWord.Coarsens z w :=
    (LabeledWord.Coarsens.refl LabeledWord.initial).compare_erased hw.run
      (by rw [hvalues, hcoords]; exact hz)
  have hI' : w.bodyLabels.length = i + 1 := hcomp.body_length.symm.trans hI
  have hJ' : w.leafIndex = j + 1 := hcomp.leaf_eq.symm.trans hJ
  have hstart : w.parser ≠ .start := by
    cases hw with
    | nil => simp [LabeledWord.initial] at hI'
    | cons w D n u as v _ hr ht => exact ht.parser_ne_start (LabeledWord.read_parser_ne_start hr)
  have hroot : w.bodyLabels.length ∈ w.rootLabel := by
    rw [hI', ← htail.rootLabel_eq hstart]
    exact (hclear.root_exact i).mpr ⟨j, hij⟩
  have hbody : w.leafIndex ∈ w.currentLabel := by
    rw [hJ', LabeledWord.currentLabel_eq_getD hI',
      ← htail.body_getD_eq hstart (by omega)]
    exact (hclear.body_exact i hij.1 j).mpr hij
  apply decide_eq_true
  exact ⟨by omega, hroot, hbody⟩

#print axioms ClearSide.selected_body_label_nonempty
#print axioms history_cut_iff
#print axioms ClearSide.cut_of_relaxed_prefix
#print axioms ClearSide.relaxed_of_cut_prefix

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
