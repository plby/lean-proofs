/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossInnerCycle
import ErdosProblems.Erdos1091.VossPrism

/-! # The triangular inner cycle in the vertex-critical endgame -/

open SimpleGraph

namespace Erdos1091.Voss

theorem triangle_adj_of_mem_support
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : C.IsCycle) (hlen : C.length = 3) {a b : V}
    (ha : a ∈ C.support) (hb : b ∈ C.support) (hab : a ≠ b) : G.Adj a b := by
  classical
  let R := C.rotate a ha
  have hR : R.IsCycle := hC.rotate ha
  have hRlen : R.length = 3 := by simpa [R] using hlen
  have hbR : b ∈ R.support := by simpa [R] using hb
  obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hbR
  have hi0 : i ≠ 0 := by
    intro heq
    exact hab (by simpa only [heq, Walk.getVert_zero] using hi)
  have hi3 : i ≠ 3 := by
    intro heq
    have hir : i = R.length := heq.trans hRlen.symm
    exact hab (by simpa only [hir, Walk.getVert_length] using hi)
  have hi12 : i = 1 ∨ i = 2 := by omega
  rcases hi12 with rfl | rfl
  · have hadj := R.adj_snd hR.not_nil
    simpa only [Walk.snd, hi] using hadj
  · have hadj := (R.adj_penultimate hR.not_nil).symm
    simpa only [Walk.penultimate, hRlen, Nat.reduceSub, hi] using hadj

/-- An inner triangle arising from a maximum ear extends any coloring
after a single vertex deletion. This excludes the prism configuration
inside a vertex-critical obstruction. -/
theorem colorable_of_maximal_ear_length_four
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : E.walk.length = 4)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    (hdelete : ∀ v, (G.induce ({v}ᶜ : Set V)).Colorable 3) : G.Colorable 3 := by
  classical
  have he := E.inner_closing_chord C hC hno (by omega) hmax hdegree
  let D := E.innerCycle (by omega : 2 ≤ E.walk.length) (Walk.isChord_sym2Mk.mp he).1
  have hD : D.IsCycle := E.innerCycle_isCycle (by omega) he
  have hDlen : D.length = 3 := by
    have hd := E.innerCycle_length (by omega) (Walk.isChord_sym2Mk.mp he).1
    change D.length = E.walk.length - 1 at hd
    omega
  have hDout : ∀ v ∈ D.support, v ∉ C.support := fun v hv => E.innerCycle_notMem _ _ hv
  have hClen : C.length = 3 := by
    have hle := hC.2.2 _ D hD (by rw [hDlen]; norm_num)
    have hge := hC.1.three_le_length
    omega
  obtain ⟨a, haAdj, haC, haE⟩ := E.innerCycle_third_attachment C hC hno (by omega) hmax hdegree he
  have haA : a ≠ E.start := fun heq => haE (by rw [heq]; exact E.walk.start_mem_support)
  have haB : a ≠ E.finish := fun heq => haE (by rw [heq]; exact E.walk.end_mem_support)
  have hDY : D.getVert 1 = E.walk.penultimate := E.innerCycle_snd _ _
  have hBY : G.Adj E.finish (D.getVert 1) := by
    rw [hDY]
    exact (E.walk.adj_penultimate E.not_nil).symm
  let F := CycleArc.spokeEar D hD hDout (i := 1) (by omega)
    E.finish_mem haC haB hBY haAdj
  have hFlen : F.walk.length = 4 := by
    have hf := CycleArc.spokeEar_length D hD hDout (i := 1) (by omega)
      E.finish_mem haC haB hBY haAdj
    change F.walk.length = D.length + 1 at hf
    omega
  have hFmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ F.walk.length := by
    intro P
    have hp := hmax P
    omega
  have hFZ : F.walk.penultimate = D.getVert 2 := CycleArc.spokeEar_penultimate _ _ _ _ _ _ _ _ _
  have hEYdegree : G.degree E.walk.penultimate ≤ 3 := by
    have hrlen : 3 ≤ E.reverse.walk.length := by simp only [Ear.reverse, Walk.length_reverse]; omega
    have hrmax : ∀ P : AttachmentPath G {v | v ∈ C.support},
        P.walk.length + 1 ≤ E.reverse.walk.length := by
      simpa only [Ear.reverse, Walk.length_reverse] using hmax
    have h := E.reverse.degree_snd_le_three C hC hno hrlen hrmax hdegree
    change G.degree E.walk.reverse.snd ≤ 3 at h
    rwa [Walk.snd_reverse] at h
  have hZdegree : G.degree (D.getVert 2) ≤ 3 := by
    have hrlen : 3 ≤ F.reverse.walk.length := by simp only [Ear.reverse, Walk.length_reverse]; omega
    have hrmax : ∀ P : AttachmentPath G {v | v ∈ C.support},
        P.walk.length + 1 ≤ F.reverse.walk.length := by
      simpa only [Ear.reverse, Walk.length_reverse] using hFmax
    have h := F.reverse.degree_snd_le_three C hC hno hrlen hrmax hdegree
    change G.degree F.walk.reverse.snd ≤ 3 at h
    rwa [Walk.snd_reverse, hFZ] at h
  let inner : Fin 3 → V := fun i => D.getVert i.val
  let outer : Fin 3 → V := ![E.start, E.finish, a]
  have hinj : Function.Injective inner := by
    intro i j heq
    apply Fin.ext
    exact hD.getVert_injOn' (show i.val ≤ D.length - 1 by omega)
      (show j.val ≤ D.length - 1 by omega) heq
  have houterMem : ∀ i, outer i ∈ C.support := by
    intro i
    fin_cases i
    · exact E.start_mem
    · exact E.finish_mem
    · exact haC
  have houterNe : Function.Injective outer := by
    intro i j heq
    fin_cases i <;> fin_cases j <;> simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, Fin.zero_eta, one_ne_zero,
    zero_ne_one] at heq ⊢
    all_goals first
      | exact E.endpoints_ne heq
      | exact E.endpoints_ne heq.symm
      | exact haA heq
      | exact haA heq.symm
      | exact haB heq
      | exact haB heq.symm
  have hdisjoint : ∀ i j, outer i ≠ inner j := by
    intro i j heq
    exact hDout _ (D.getVert_mem_support _) (heq ▸ houterMem i)
  have houterAdj : Pairwise (fun i j => G.Adj (outer i) (outer j)) := by
    intro i j hij
    exact triangle_adj_of_mem_support C hC.1 hClen (houterMem i) (houterMem j)
      (fun heq => hij (houterNe heq))
  have hinnerAdj : Pairwise (fun i j => G.Adj (inner i) (inner j)) := by
    intro i j hij
    exact triangle_adj_of_mem_support D hD hDlen (D.getVert_mem_support _) (D.getVert_mem_support _)
      (fun heq => hij (hinj heq))
  have hspokes : ∀ i, G.Adj (inner i) (outer i) := by
    intro i
    fin_cases i
    · exact (E.walk.adj_snd E.not_nil).symm
    · change G.Adj (D.getVert 1) E.finish
      rw [hDY]
      exact E.walk.adj_penultimate E.not_nil
    · exact haAdj
  have hdeg : ∀ i, G.degree (inner i) ≤ 3 := by
    intro i
    fin_cases i
    · exact E.degree_snd_le_three C hC hno (by omega) hmax hdegree
    · change G.degree (D.getVert 1) ≤ 3
      rwa [hDY]
    · exact hZdegree
  apply colorable_of_matched_triangle_vertex_deletion inner outer hinj hdisjoint houterAdj
    ?_ (hdelete _)
  intro i v hv
  have hi1 : i ≠ i + 1 := by fin_cases i <;> decide
  have hi2 : i ≠ i + 2 := by fin_cases i <;> decide
  have h12 : i + 1 ≠ i + 2 := by fin_cases i <;> decide
  rcases adj_cases_of_degree_le_three (hdeg i) (hinnerAdj hi1) (hinnerAdj hi2) (hspokes i)
    (fun heq => h12 (hinj heq)) (hdisjoint i (i + 1)).symm (hdisjoint i (i + 2)).symm hv with h | h | h
  · exact Or.inl ⟨i + 1, h⟩
  · exact Or.inl ⟨i + 2, h⟩
  · exact Or.inr h

#print axioms colorable_of_maximal_ear_length_four

end Erdos1091.Voss
