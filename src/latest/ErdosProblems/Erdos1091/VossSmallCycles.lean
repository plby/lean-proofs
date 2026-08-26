/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.Voss

/-! # Explicit small odd cycles used in Voss's exceptional cases -/

open SimpleGraph

namespace Erdos1091.Voss

/-- A five-cycle with the two displayed chords is an explicit forbidden
odd cycle. Distinctness is asserted for all five vertices, not inferred
from a drawing. -/
theorem odd_two_chords_of_five_cycle {V : Type*} {G : SimpleGraph V}
    {a b c d e : V} (hdist : ([a, b, c, d, e] : List V).Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) (hac : G.Adj a c) (hce : G.Adj c e) :
    HasOddCycleWithTwoChords G := by
  have hne := hdist
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, not_false_eq_true, and_true, not_or] at hne
  let q := Walk.cons hbc (Walk.cons hcd (Walk.cons hde (Walk.cons hea Walk.nil)))
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    have hrot : ([a, b, c, d, e].rotate 1).Nodup := List.nodup_rotate.mpr hdist
    simpa [q] using hrot
  have hclosing : s(a, b) ∉ q.edges := by
    intro he
    have hbe := hq.eq_penultimate_of_mem_edges he
    have hbe' : b = e := by simpa [q] using hbe
    tauto
  let p := Walk.cons hab q
  have hp : p.IsCycle := (Walk.cons_isCycle_iff q hab).mpr ⟨hq, hclosing⟩
  have hchord₁ : p.IsChord s(a, c) := by
    refine ⟨hac, ?_, by simp [p, q], by simp [p, q]⟩
    simp only [p, q, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false, Sym2.eq_iff]
    tauto
  have hchord₂ : p.IsChord s(c, e) := by
    refine ⟨hce, ?_, by simp [p, q], by simp [p, q]⟩
    simp only [p, q, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false, Sym2.eq_iff]
    tauto
  have hchordsNe : s(a, c) ≠ s(c, e) := by
    intro heq
    have hcases := Sym2.eq_iff.mp heq
    tauto
  exact ⟨a, p, hp, by norm_num [p, q], s(a, c), s(c, e), hchordsNe, hchord₁, hchord₂⟩

end Erdos1091.Voss
