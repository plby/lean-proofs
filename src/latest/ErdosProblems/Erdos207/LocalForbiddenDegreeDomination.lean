/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalForbiddenConfiguration
import ErdosProblems.Erdos207.FiniteHypergraphDegrees
import ErdosProblems.Erdos207.RootedThreatAbsorberBound

/-! # Actual local degrees inject into selected mixed source witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localForbidden_degree_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (available initial later : TripleSystemOn V)
    (huniform : ∀ E ∈ F, E.card = j' - 2) (hj : 4 ≤ j) (hjj : j ≤ j')
    (hterminal : ∀ U ∈ available, W.level U = Fin.last ell)
    (hedges : ∀ U ∈ available, ∀ e ∈ tripleEdgeFinset U,
      e ∈ graphEdges G ∧ e ∉ (coveredGraph initial).edgeSet) (T : TripleOn V) :
    (finiteHypergraphDegree (localForbiddenConfigurations F available (initial ∪ later) j) T : ℝ≥0) ≤
      selectedCount (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
        (sourceGraphMixedSelected G (fun _ : Unit ↦ initial) (fun _ ↦ later) ()) := by
  classical
  let D := (localForbiddenConfigurations F available (initial ∪ later) j).filter (fun S ↦ T ∈ S)
  have hdata : ∀ S : D, S.1 ⊆ available ∧ S.1.card = j - 2 ∧ T ∈ S.1 ∧
      ∃ E ∈ F, S.1 ⊆ E ∧ E \ S.1 ⊆ initial ∪ later := by
    intro S
    have hm := mem_filter.mp S.2
    have hd := (mem_localForbiddenConfigurations_iff F available (initial ∪ later) S.1 j).mp hm.1
    exact ⟨hd.1, hd.2.1, hm.2, hd.2.2⟩
  choose ext hEF hSE hOld using (fun S : D ↦ (hdata S).2.2.2)
  let code : D → sourceNibbleCodes W F T j j' := fun S ↦
    ⟨(ext S, ext S \ S.1), localForbidden_sourceNibbleCode W F huniform hj hjj T S.1 (ext S)
      (hEF S) (hSE S) (hdata S).2.1 (hdata S).2.2.1 (fun U hU ↦ hterminal U ((hdata S).1 hU))⟩
  have hinj : Function.Injective code := by
    intro S S' heq
    have hfirst : ext S = ext S' := congrArg (fun x : sourceNibbleCodes W F T j j' ↦ x.1.1) heq
    have hsecond : ext S \ S.1 = ext S' \ S'.1 := congrArg (fun x : sourceNibbleCodes W F T j j' ↦ x.1.2) heq
    apply Subtype.ext
    calc
      S.1 = ext S \ (ext S \ S.1) := (Finset.sdiff_sdiff_eq_self (hSE S)).symm
      _ = ext S' \ (ext S' \ S'.1) := congrArg₂ (fun A B : TripleSystemOn V ↦ A \ B) hfirst hsecond
      _ = S'.1 := Finset.sdiff_sdiff_eq_self (hSE S')
  have hselected : ∀ S : D, sourceNibbleCoordinates T (code S).1 ⊆
      sourceGraphMixedSelected G (fun _ : Unit ↦ initial) (fun _ ↦ later) () := by
    intro S
    exact localForbidden_sourceNibbleCoordinates_selected G initial later T S.1 (ext S) (hSE S) (hOld S)
      (fun U hU ↦ hedges U ((hdata S).1 hU))
  have hsum := sum_le_sum_of_injective_code code hinj (fun _ ↦ (1 : ℝ≥0))
    (fun x ↦ if sourceNibbleCoordinates T x.1 ⊆
      sourceGraphMixedSelected G (fun _ : Unit ↦ initial) (fun _ ↦ later) () then 1 else 0)
    (fun S ↦ by rw [if_pos (hselected S)])
  simpa only [selectedCount, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one,
    D, finiteHypergraphDegree] using hsum

end

end Erdos207
