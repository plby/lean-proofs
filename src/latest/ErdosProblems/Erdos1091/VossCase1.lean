/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossCase1Order
import ErdosProblems.Erdos1091.VossCase1FourCycles
import ErdosProblems.Erdos1091.VossCase1LongCycle
import ErdosProblems.Erdos1091.VossCase1Triangle

/-! # Completion of Voss's inner-cycle case -/

open SimpleGraph

namespace Erdos1091.Voss

/-- The two final cycle parities contradict the three odd long-ear
closure invariants. -/
theorem four_ordered_spokes_impossible
    {V : Type*} {G : SimpleGraph V} {z x : V}
    (C : G.Walk z z) (hC : C.IsCycle) (D : G.Walk x x) (hD : D.IsCycle)
    (hDlen : 4 ≤ D.length) (hDC : ∀ v ∈ D.support, v ∉ C.support)
    (hno : ¬ HasOddCycleWithTwoChords G)
    {i j k : ℕ} (hi : 0 < i) (hij : i < j) (hjk : j < k) (hk : k < C.length)
    (h₀ : G.Adj z x) (h₁ : G.Adj (D.getVert 1) (C.getVert i))
    (h₂ : G.Adj (D.getVert 2) (C.getVert j))
    (h₃ : G.Adj (D.getVert 3) (C.getVert k))
    (ho₁ : Odd (D.length + 1 + i)) (ho₂ : Odd (D.length + 1 + (j - i)))
    (ho₃ : Odd (D.length + 1 + (k - j))) : False := by
  have hshort := four_spokes_short_inner_cycle_even C hC D hD hDlen hDC hno hi hij hjk hk h₀ h₁ h₂ h₃
  have hlong := four_spokes_long_inner_cycle_even C hC D hD hDlen hDC hno hi hij hjk hk h₀ h₁ h₂ h₃
  simp only [Nat.odd_iff] at ho₁ ho₂ ho₃
  simp only [Nat.even_iff] at hshort hlong
  omega

/-- The long-inner-cycle branch of a maximum ear is impossible. -/
theorem long_maximal_ear_impossible
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 5 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v) : False := by
  have he := E.inner_closing_chord C hC hno (by omega) hmax hdegree
  let D := E.innerCycle (by omega : 2 ≤ E.walk.length) (Walk.isChord_sym2Mk.mp he).1
  have hD : D.IsCycle := E.innerCycle_isCycle (by omega) he
  have hDlen : D.length + 1 = E.walk.length := by
    have hd := E.innerCycle_length (by omega) (Walk.isChord_sym2Mk.mp he).1
    change D.length = E.walk.length - 1 at hd
    omega
  obtain ⟨a, haAdj, haC, haE⟩ := E.innerCycle_third_attachment C hC hno (by omega) hmax hdegree he
  obtain ⟨b, hbAdj, hbC, hbE, hba⟩ := E.innerCycle_fourth_attachment C hC hno hlen hmax hdegree
    he haC haE haAdj
  have haA : a ≠ E.start := fun heq => haE (by rw [heq]; exact E.walk.start_mem_support)
  have haB : a ≠ E.finish := fun heq => haE (by rw [heq]; exact E.walk.end_mem_support)
  obtain ⟨R, hRcycle, hRlen, hRsupp, i, j, hi, hij, hjN, hiGet, hjGet⟩ :=
    CycleArc.exists_oriented_three C hC.1 E.start_mem E.finish_mem haC
      E.endpoints_ne.symm haA.symm haB.symm
  have hR : IsShortestOddCycle R := by
    refine ⟨hRcycle, ?_, ?_⟩
    · rw [hRlen]; exact hC.2.1
    · intro w p hp ho
      rw [hRlen]
      exact hC.2.2 w p hp ho
  let F := E.changeSet (T := {v | v ∈ R.support}) (fun v => (hRsupp v).symm)
  have hFlen : 5 ≤ F.walk.length := hlen
  have hFmax : ∀ P : AttachmentPath G {v | v ∈ R.support}, P.walk.length + 1 ≤ F.walk.length := by
    intro P
    exact hmax (P.changeSet hRsupp)
  have hDout : ∀ v ∈ D.support, v ∉ R.support := by
    intro v hv hvR
    exact E.innerCycle_notMem _ _ hv ((hRsupp v).mp hvR)
  have hDsup : D.support ⊆ F.walk.support := E.innerCycle_support_subset _ _
  have hDY : D.getVert 1 = F.walk.penultimate := E.innerCycle_snd _ _
  have hjF : R.getVert j ∉ F.walk.support := by
    change R.getVert j ∉ E.walk.support
    simpa only [hjGet] using haE
  have hthird : G.Adj (D.getVert 2) (R.getVert j) := hjGet ▸ haAdj
  have hfourth : G.Adj (D.getVert 3) b := hbAdj
  obtain ⟨k, hjk, hkN, hkGet, ho₁, ho₂, ho₃⟩ := fourth_attachment_order_and_parity
    R hR hno F hFlen hFmax hdegree rfl D hD hDlen hDout hDsup hDY
    hi hij hjN hiGet hjF hthird ((hRsupp b).mpr hbC) hbE (by simpa only [hjGet] using hba) hfourth
  have h₀ : G.Adj E.start E.walk.snd := E.walk.adj_snd E.not_nil
  have h₁ : G.Adj (D.getVert 1) (R.getVert i) := by
    rw [hDY, hiGet]
    exact E.walk.adj_penultimate E.not_nil
  have h₃ : G.Adj (D.getVert 3) (R.getVert k) := hkGet ▸ hfourth
  have hDFlen : D.length + 1 = F.walk.length := hDlen
  exact four_ordered_spokes_impossible R hRcycle D hD (by omega) hDout hno
    hi hij hjk hkN h₀ h₁ hthird h₃
    (by rwa [hDFlen]) (by rwa [hDFlen]) (by rwa [hDFlen])

/-- All possible maximum-ear lengths yield three-colorability when
single-vertex deletions are three-colorable. -/
theorem colorable_of_maximal_ear
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    (hdelete : ∀ v, (G.induce ({v}ᶜ : Set V)).Colorable 3) : G.Colorable 3 := by
  have he := E.inner_closing_chord C hC hno hlen hmax hdegree
  have hD := E.innerCycle_isCycle (by omega) he
  have hDlen := E.innerCycle_length (by omega) (Walk.isChord_sym2Mk.mp he).1
  have hthree := hD.three_le_length
  by_cases hfour : E.walk.length = 4
  · exact colorable_of_maximal_ear_length_four C hC hno E hfour hmax hdegree hdelete
  · exact (long_maximal_ear_impossible C hC hno E (by omega) hmax hdegree).elim

#print axioms long_maximal_ear_impossible
#print axioms colorable_of_maximal_ear

end Erdos1091.Voss
