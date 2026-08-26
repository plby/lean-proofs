import ErdosProblems.Erdos591.FinishBodyLabels

/-!
# A finish response crosses each pending selected leaf

The current body's literal remaining-leaf count bounds the accepted
completion input from below. Every selected index strictly ahead of the
current counter and strictly below the body marker is consequently met
at a proper, nonempty atomic prefix of that response.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem LegalRun.parser_run {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) : Parser.run w.parser (xs.map Prod.snd) = some v.parser := by
  induction h with
  | nil => rfl
  | cons w D n u xs v _ hr _ ih =>
      simpa [Parser.run, (read_spec hr).1] using ih

theorem finish_parser_run {w v : LabeledWord} {xs : List ℕ}
    (h : finishParser.run w xs = some v) : Parser.run w.parser xs = some (.blocks 0) := by
  have ht : v.parser = .blocks 0 := by
    simpa [finishParser, terminal] using finishParser.run_stopped h
  have hl := (zero_run_legal finishParser (fun _ _ => rfl) h).parser_run
  simpa [List.map_map, ht] using hl

theorem finish_pending_leaf_prefix {w v : LabeledWord} {xs : List ℕ}
    (hw : w.CursorInvariant) (hfinish : finishParser.run w xs = some v)
    (hsel : w.bodyLabels.length ∈ w.rootLabel) {j : ℕ}
    (hj : j ∈ w.currentLabel) (hfuture : w.leafIndex < j) :
    ∃ k z, 0 < k ∧ k < xs.length ∧
      LegalRun w ((xs.take k).map fun n => (∅, n)) z ∧
      LegalRun z ((xs.drop k).map fun n => (∅, n)) v ∧ z.relaxed = true := by
  have hjbound := (hw.2.2.2 j hj).2
  have hcount := hw.2.1.2
  have hout : 0 < outstandingLeaves w.parser := by omega
  have hparser : ∃ r b, w.parser = .leaves r b := by
    cases hp : w.parser with
    | start => simp [hp, outstandingLeaves] at hout
    | blocks r => simp [hp, outstandingLeaves] at hout
    | leaves r b => exact ⟨r, b, rfl⟩
  obtain ⟨r, b, hp⟩ := hparser
  have hc : w.leafIndex + (b + 1) = w.bodyMarker := by
    simpa [hp, outstandingLeaves] using hcount
  have hrun : Parser.run (Parser.normalize r (b + 1)) xs = some (.blocks 0) := by
    simpa [Parser.normalize, hp] using finish_parser_run hfinish
  obtain ⟨a, ys, hxs, ha, _⟩ := Parser.split_leaves r (b + 1) xs hrun
  have hlen : b + 1 ≤ xs.length := by rw [hxs, List.length_append, ha]; omega
  let k := j - w.leafIndex
  have hkpos : 0 < k := by omega
  have hkb : k < b + 1 := by omega
  have hklen : k < xs.length := hkb.trans_le hlen
  have htake : (xs.take k).length = k := by simp [Nat.min_eq_left hklen.le]
  have hstep : w.parser = Parser.normalize r ((xs.take k).length + (b + 1 - k)) := by
    rw [htake]
    have heq : k + (b + 1 - k) = b + 1 := by omega
    rw [heq]
    exact hp
  let z : LabeledWord := {w with
    parser := Parser.normalize r (b + 1 - k)
    coordinates := w.coordinates ++ xs.take k
    leafIndex := w.leafIndex + (xs.take k).length}
  have hzrun : w.runAtoms ((xs.take k).map fun n => (∅, n)) = some z :=
    runAtoms_leaves_part w r (b + 1 - k) (xs.take k) hstep
  have hlegal := zero_run_legal finishParser (fun _ _ => rfl) hfinish
  have hsplit : LegalRun w
      (((xs.take k).map fun n => (∅, n)) ++ ((xs.drop k).map fun n => (∅, n))) v := by
    simpa only [← List.map_append, List.take_append_drop] using hlegal
  obtain ⟨u, hu, ht⟩ := hsplit.split
  have heq : u = z := Option.some.inj (hu.run.symm.trans hzrun)
  subst u
  refine ⟨k, z, hkpos, hklen, hu, ht, ?_⟩
  have hjcounter : w.leafIndex + (xs.take k).length = j := by rw [htake]; omega
  simp only [relaxed, z, hjcounter, currentLabel, decide_eq_true_eq]
  exact ⟨by omega, hsel, hj⟩

#print axioms finish_pending_leaf_prefix

end Erdos591.Positive.Game.LabeledWord
