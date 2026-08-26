import ErdosProblems.Erdos118.Reused591.LegalAtoms
import ErdosProblems.Erdos118.Reused591.CutPrefix

namespace Erdos118.Reused591

/-!
# Interleaving canonical cut-labeled words

Projection to one side retains its exact labeled atom list. A switch
from an unfinished word creates a coordinate cut, so the canonical
cut-prefix theorem supplies the required decision event.
-/

namespace Erdos591.Positive.Game

namespace Board

theorem get_update_ne (b : Board) {side other : Bool} (h : other ≠ side) (w : LabeledWord) :
    (b.update side w).get other = b.get other := by
  cases side <;> cases other <;> simp_all [get, update]

theorem ext_get {b c : Board} (h : ∀ side, b.get side = c.get side) : b = c := by
  have hl := h false
  have hr := h true
  cases b
  cases c
  simp only [get] at hl hr
  cases hl
  cases hr
  rfl

end Board

namespace Payoff

theorem cut_append_pair (pre rest other : List ℕ) (a b y : ℕ)
    (hy : y ∈ other) (hay : a < y) (hyb : y < b) :
    Cut (pre ++ a :: b :: rest) other pre.length := by
  refine ⟨by simp, y, hy, ?_, ?_⟩
  · rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simpa using hay
  · rw [List.getD_append_right _ _ _ _ (Nat.le_succ _)]
    simpa using hyb

end Payoff

namespace Atomic

def project : List Atom → Bool → List (Finset ℕ × ℕ)
  | [], _ => []
  | a :: xs, side => if a.side = side then (a.label, a.value) :: project xs side
      else project xs side

@[simp] theorem project_nil (side : Bool) : project [] side = [] := rfl

theorem project_cons_same (a : Atom) (xs : List Atom) :
    project (a :: xs) a.side = (a.label, a.value) :: project xs a.side := by
  simp [project]

theorem project_cons_ne (a : Atom) (xs : List Atom) {side : Bool} (h : a.side ≠ side) :
    project (a :: xs) side = project xs side := by simp [project, h]

@[simp] theorem project_append (xs ys : List Atom) (side : Bool) :
    project (xs ++ ys) side = project xs side ++ project ys side := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases ha : a.side = side <;> simp [project, ih, ha]

theorem mem_project {xs : List Atom} {side : Bool} {p : Finset ℕ × ℕ}
    (hp : p ∈ project xs side) : ∃ a ∈ xs, a.side = side ∧ (a.label, a.value) = p := by
  induction xs with
  | nil => simp [project] at hp
  | cons a xs ih =>
      by_cases ha : a.side = side
      · have hh : p = (a.label, a.value) ∨ p ∈ project xs side := by
          simpa [project, ha] using hp
        rcases hh with rfl | hh
        · exact ⟨a, by simp, ha, rfl⟩
        · obtain ⟨b, hb, hbs, hbp⟩ := ih hh
          exact ⟨b, List.mem_cons_of_mem a hb, hbs, hbp⟩
      · have hh : p ∈ project xs side := by simpa [project, ha] using hp
        obtain ⟨b, hb, hbs, hbp⟩ := ih hh
        exact ⟨b, List.mem_cons_of_mem a hb, hbs, hbp⟩

theorem pair_mem_project {xs : List Atom} (a : Atom) (ha : a ∈ xs) :
    (a.label, a.value) ∈ project xs a.side := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [project]
      · have hh := ih ha
        by_cases hb : b.side = a.side <;> simp_all [project]

theorem value_mem_project {xs : List Atom} (a : Atom) (ha : a ∈ xs) :
    a.value ∈ (project xs a.side).map Prod.snd :=
  List.mem_map.mpr ⟨(a.label, a.value), pair_mem_project a ha, rfl⟩

theorem values_sublist_inputs (xs : List Atom) :
    List.Sublist (xs.map Atom.value) (inputs xs) := by
  induction xs with
  | nil => exact List.Sublist.refl []
  | cons a xs ih =>
      exact (List.sublist_append_right (a.label.sort (· ≤ ·)) [a.value]).append ih

theorem projected_values_disjoint (xs : List Atom)
    (hinc : (xs.map Atom.value).Pairwise (· < ·)) :
    Disjoint ((project xs false).map Prod.snd).toFinset
      ((project xs true).map Prod.snd).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz₀ hz₁
  obtain ⟨p, hp, hpz⟩ := List.mem_map.mp (List.mem_toFinset.mp hz₀)
  obtain ⟨q, hq, hqz⟩ := List.mem_map.mp (List.mem_toFinset.mp hz₁)
  obtain ⟨a, ha, haSide, hap⟩ := mem_project hp
  obtain ⟨b, hb, hbSide, hbq⟩ := mem_project hq
  have hav : a.value = z := (congrArg Prod.snd hap).trans hpz
  have hbv : b.value = z := (congrArg Prod.snd hbq).trans hqz
  have hab : a = b := List.inj_on_of_nodup_map hinc.nodup ha hb (hav.trans hbv.symm)
  simp [hab, hbSide] at haSide

/-- Every actual coordinate cut is a decision event in the exact
canonical prefix execution. This property is independent of a play. -/
def CutEvents (program : Bool → List (Finset ℕ × ℕ)) : Prop :=
  ∀ side n w,
    Payoff.Cut ((program side).map Prod.snd) ((program (!side)).map Prod.snd) n →
    LabeledWord.initial.runAtoms ((program side).take (n + 1)) = some w →
    w.event = true

/-- Switching sides immediately after this atom either leaves a
completed word or witnesses an actual cut before its next coordinate. -/
theorem event_after_switch (program : Bool → List (Finset ℕ × ℕ))
    (hevents : CutEvents program) (pre : List Atom) (a next : Atom) (xs : List Atom)
    (w last : LabeledWord)
    (hparts : ∀ side, program side = project pre side ++ project (a :: next :: xs) side)
    (horder : ((pre ++ a :: next :: xs).map Atom.value).Pairwise (· < ·))
    (hnext : next.side ≠ a.side)
    (hpast : LabeledWord.initial.runAtoms
      (project pre a.side ++ [(a.label, a.value)]) = some w)
    (htail : LabeledWord.LegalRun w (project (next :: xs) a.side) last)
    (hterm : last.terminal = true) : w.event = true := by
  cases hw : w.terminal with
  | true => simp [LabeledWord.event, hw]
  | false =>
      have htail' : LabeledWord.LegalRun w (project xs a.side) last := by
        simpa [project, hnext] using htail
      cases hp : project xs a.side with
      | nil =>
          have heq : w = last := (LabeledWord.legalRun_nil_iff _ _).1 (hp ▸ htail')
          simp [heq, hterm] at hw
      | cons p ps =>
          obtain ⟨D, n⟩ := p
          obtain ⟨c, hc, _, hcp⟩ := mem_project
            (show (D, n) ∈ project xs a.side by rw [hp]; simp)
          have hcv : c.value = n := congrArg Prod.snd hcp
          have ho : (a.value :: next.value :: xs.map Atom.value).Pairwise (· < ·) :=
            (List.pairwise_append.mp (by simpa using horder)).2.1
          have han : a.value < next.value := (List.pairwise_cons.mp ho).1 _ (by simp)
          have hnc : next.value < n := by
            have hh := (List.pairwise_cons.mp (List.pairwise_cons.mp ho).2).1
              c.value (List.mem_map.mpr ⟨c, hc, rfl⟩)
            simpa [hcv] using hh
          have hnside : next.side = !a.side := by
            cases h₁ : a.side <;> cases h₂ : next.side <;> simp_all
          have hy : next.value ∈ ((program (!a.side)).map Prod.snd) := by
            rw [hparts (!a.side), List.map_append]
            apply List.mem_append_right
            simpa [hnside] using value_mem_project next
              (show next ∈ a :: next :: xs by simp)
          have hcode : program a.side =
              project pre a.side ++ (a.label, a.value) :: (D, n) :: ps := by
            simpa [project, hnext, hp] using hparts a.side
          have hcut : Payoff.Cut ((program a.side).map Prod.snd)
              ((program (!a.side)).map Prod.snd) (project pre a.side).length := by
            rw [hcode, List.map_append, List.map_cons, List.map_cons]
            simpa using Payoff.cut_append_pair
              ((project pre a.side).map Prod.snd) (ps.map Prod.snd)
              ((program (!a.side)).map Prod.snd) a.value n next.value hy han hnc
          apply hevents a.side (project pre a.side).length w hcut
          have hcode' : program a.side =
              (project pre a.side ++ [(a.label, a.value)]) ++ (D, n) :: ps := by
            simpa [List.append_assoc] using hcode
          rw [hcode', show (project pre a.side).length + 1 =
            (project pre a.side ++ [(a.label, a.value)]).length by simp, List.take_left]
          exact hpast

/-- Induct through the chronological atom list. The two projections
record the exact past and remaining cursor programs. -/
theorem trace_of_split (program : Bool → List (Finset ℕ × ℕ))
    (hevents : CutEvents program) (last : Board)
    (hterminal : ∀ side, (last.get side).terminal = true)
    (pre xs : List Atom) (b : Board)
    (hparts : ∀ side, program side = project pre side ++ project xs side)
    (horder : ((pre ++ xs).map Atom.value).Pairwise (· < ·))
    (hpast : ∀ side, LabeledWord.initial.runAtoms (project pre side) = some (b.get side))
    (htails : ∀ side, LabeledWord.LegalRun (b.get side) (project xs side) (last.get side)) :
    Trace b xs last := by
  induction xs generalizing pre b with
  | nil =>
      have hb : b = last := Board.ext_get fun side =>
        (LabeledWord.legalRun_nil_iff _ _).1 (htails side)
      rw [hb]
      exact .nil last
  | cons a xs ih =>
      have hthis : LabeledWord.LegalRun (b.get a.side)
          ((a.label, a.value) :: project xs a.side) (last.get a.side) := by
        simpa only [project_cons_same] using htails a.side
      obtain ⟨w, hlabel, hread, hrest⟩ := (LabeledWord.legalRun_cons_iff ..).1 hthis
      have hparts' : ∀ side,
          program side = project (pre ++ [a]) side ++ project xs side := by
        intro side
        by_cases ha : a.side = side <;>
          simpa [project, ha, List.append_assoc] using hparts side
      have horder' : (((pre ++ [a]) ++ xs).map Atom.value).Pairwise (· < ·) := by
        simpa only [List.append_assoc, List.singleton_append] using horder
      have hpast' : ∀ side, LabeledWord.initial.runAtoms (project (pre ++ [a]) side) =
          some ((b.update a.side w).get side) := by
        intro side
        by_cases hs : side = a.side
        · subst side
          rw [project_append, project_cons_same, project_nil, Board.get_update,
            LabeledWord.runAtoms_append, hpast a.side]
          simp [LabeledWord.runAtoms, hread]
        · rw [Board.get_update_ne b hs]
          simpa [project, Ne.symm hs] using hpast side
      have htails' : ∀ side, LabeledWord.LegalRun
          ((b.update a.side w).get side) (project xs side) (last.get side) := by
        intro side
        by_cases hs : side = a.side
        · subst side
          simpa only [Board.get_update] using hrest
        · rw [Board.get_update_ne b hs]
          simpa only [project_cons_ne a xs (Ne.symm hs)] using htails side
      have hready : Ready (b.update a.side w) a.side xs := by
        cases xs with
        | nil => simp [Ready]
        | cons next xs =>
            intro z hz he
            have hz' : z = next := by simpa [eq_comm] using hz
            subst z
            by_contra hn
            have hev := event_after_switch program hevents pre a next xs w
              (last.get a.side) hparts horder hn
              (by simpa [project] using hpast' a.side) hrest (hterminal a.side)
            have hw : w.event = false := by simpa only [Board.get_update] using he
            simp [hw] at hev
      exact .cons b a w xs last hlabel hread hready
        (ih (pre ++ [a]) (b.update a.side w) hparts' horder' hpast' htails')

theorem trace_of_projections (program : Bool → List (Finset ℕ × ℕ))
    (hevents : CutEvents program) (last : Board)
    (hterminal : ∀ side, (last.get side).terminal = true)
    (hlegal : ∀ side, LabeledWord.LegalRun LabeledWord.initial (program side) (last.get side))
    (xs : List Atom) (hproj : ∀ side, project xs side = program side)
    (horder : (xs.map Atom.value).Pairwise (· < ·)) : Trace Board.initial xs last := by
  apply trace_of_split program hevents last hterminal [] xs Board.initial
  · intro side
    simpa only [project_nil, List.nil_append] using (hproj side).symm
  · exact horder
  · intro side
    cases side <;> rfl
  · intro side
    rw [hproj side]
    cases side <;> exact hlegal _

noncomputable def cutProgram (s t : List (List ℕ)) : Bool → List (Finset ℕ × ℕ)
  | false => LabeledCode.atoms (CutLabels.root s t) (CutLabels.bodies s t)
  | true => LabeledCode.atoms (CutLabels.root t s) (CutLabels.bodies t s)

noncomputable def cutBoard (s t : List (List ℕ)) : Board :=
  ⟨CutLabels.cursor s t, CutLabels.cursor t s⟩

theorem event_of_cut {s t : List (List ℕ)} (h : CutLabels.Admissible s t)
    (k : ℕ) (w : LabeledWord) (hc : Payoff.Cut
      (Erdos591.Negative.Exact.word s) (Erdos591.Negative.Exact.word t) k)
    (hw : LabeledWord.initial.runAtoms
      ((LabeledCode.atoms (CutLabels.root s t) (CutLabels.bodies s t)).take (k + 1)) =
        some w) : w.event = true := by
  obtain ⟨i, j, hij, rfl⟩ := h.leaves k hc
  obtain ⟨v, hv, hrel, _⟩ := CutLabels.cut_is_relaxed hij
  have heq : w = v := Option.some.inj (hw.symm.trans hv)
  simp [heq, LabeledWord.event, hrel]

theorem canonical_cutEvents {s t : List (List ℕ)}
    (hs : CutLabels.Admissible s t) (ht : CutLabels.Admissible t s) :
    CutEvents (cutProgram s t) := by
  intro side k w hc hw
  cases side with
  | false =>
      apply event_of_cut hs k w _ hw
      simpa only [cutProgram, Bool.not_false, LabeledCode.atoms_coordinates,
        CutLabels.erase_bodies] using hc
  | true =>
      apply event_of_cut ht k w _ hw
      simpa only [cutProgram, Bool.not_true, LabeledCode.atoms_coordinates,
        CutLabels.erase_bodies] using hc

/-- The geometric cut conditions suffice for the complete interleaved
legal trace; its scheduling is proved, not an extra assumption. -/
theorem canonical_trace {s t : List (List ℕ)}
    (hs : CutLabels.Admissible s t) (ht : CutLabels.Admissible t s)
    (xs : List Atom) (hproj : ∀ side, project xs side = cutProgram s t side)
    (hinc : (inputs xs).Pairwise (· < ·)) : Trace Board.initial xs (cutBoard s t) := by
  apply trace_of_projections (cutProgram s t) (canonical_cutEvents hs ht) (cutBoard s t)
  · intro side
    cases side <;> rfl
  · intro side
    cases side
    · exact CutLabels.legal_atoms hs
    · exact CutLabels.legal_atoms ht
  · exact hproj
  · exact hinc.sublist (values_sublist_inputs xs)

#print axioms event_after_switch
#print axioms canonical_trace

end Atomic

end Erdos591.Positive.Game

end Erdos118.Reused591
