import ErdosProblems.Erdos591.FirstLeafGluingHistory
import ErdosProblems.Erdos591.SameBodyRun

/-! # Exact structural continuation of a partially read body prefix -/

namespace Erdos591.Positive.Game.LabeledWord

theorem bodyLeafCursor_extend (w : LabeledWord) (D : Finset ℕ) (n r : ℕ)
    (xs ys : List ℕ) (hlen : (xs ++ ys).length ≤ n) :
    (bodyLeafCursor w D n r xs).runAtoms (ys.map fun y => (∅, y)) =
      some (bodyLeafCursor w D n r (xs ++ ys)) := by
  have he : n - xs.length = ys.length + (n - (xs ++ ys).length) := by
    simp only [List.length_append] at hlen ⊢
    omega
  have hr := runAtoms_leaves_part (bodyLeafCursor w D n r xs) r
    (n - (xs ++ ys).length) ys (by simp [bodyLeafCursor, he])
  simpa [bodyLeafCursor, List.length_append, List.append_assoc] using hr

theorem SameStructure.of_run_coordinates {c f v u : LabeledWord}
    (h : SameStructure c f) {xs ys : List (Finset ℕ × ℕ)}
    (hx : c.runAtoms xs = some v) (hy : f.runAtoms ys = some u)
    (hcoords : v.coordinates = u.coordinates) : SameStructure v u := by
  have he : c.coordinates ++ xs.map Prod.snd = c.coordinates ++ ys.map Prod.snd := by
    rw [← runAtoms_coordinates hx, h.coordinates_eq, ← runAtoms_coordinates hy]
    exact hcoords
  exact h.of_runs hx hy (List.append_cancel_left he)

theorem LegalRun.bodyLeafCursor_prefix {w v : LabeledWord} {D : Finset ℕ} {n r : ℕ}
    {xs : List ℕ} {as : List (Finset ℕ × ℕ)}
    (h : LegalRun (bodyLeafCursor w D n r xs) as v)
    (hp : w.parser = .blocks (r + 1))
    (hcount : v.bodyLabels.length = w.bodyLabels.length + 1) (hleaf : v.leafIndex ≤ n) :
    (xs ++ as.map Prod.snd).length = v.leafIndex ∧
      v.coordinates = w.coordinates ++ n :: (xs ++ as.map Prod.snd) ∧
      SameStructure v (bodyLeafCursor w D n r (xs ++ as.map Prod.snd)) := by
  have hstart : (bodyLeafCursor w D n r xs).parser ≠ .start := by
    cases hn : n - xs.length <;> simp [bodyLeafCursor, Parser.normalize, hn]
  have hlen := h.leafIndex_of_body_length hstart (by simpa [bodyLeafCursor] using hcount)
  have hlength : (xs ++ as.map Prod.snd).length = v.leafIndex := by
    simpa [bodyLeafCursor] using hlen.symm
  have hcoords : v.coordinates = w.coordinates ++ n :: (xs ++ as.map Prod.snd) := by
    simpa [bodyLeafCursor, List.append_assoc] using runAtoms_coordinates h.run
  have hxs : xs.length ≤ n := by
    simp only [List.length_append, List.length_map] at hlength
    omega
  have hfirst := bodyLeafCursor_run w D n r xs hp hxs
  have hwhole : w.runAtoms (((D, n) :: xs.map fun x => (∅, x)) ++ as) = some v := by
    simp only [runAtoms_append, hfirst, Option.bind_some, h.run]
  have hcanon := bodyLeafCursor_run w D n r (xs ++ as.map Prod.snd) hp
    (hlength.trans_le hleaf)
  exact ⟨hlength, hcoords, (SameStructure.refl w).of_run_coordinates hwhole hcanon
    (by simpa [bodyLeafCursor] using hcoords)⟩

#print axioms bodyLeafCursor_extend
#print axioms SameStructure.of_run_coordinates
#print axioms LegalRun.bodyLeafCursor_prefix

end Erdos591.Positive.Game.LabeledWord
