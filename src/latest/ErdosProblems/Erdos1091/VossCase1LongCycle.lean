/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossSpokePath

/-! # The final cycle with two omitted inner edges -/

open SimpleGraph

namespace Erdos1091.Voss

/-- The two separated outer arcs and the complementary inner arcs form
a cycle whose chords are the two omitted inner edges. -/
theorem four_spokes_long_inner_cycle_even
    {V : Type*} {G : SimpleGraph V} {z x : V}
    (C : G.Walk z z) (hC : C.IsCycle) (D : G.Walk x x) (hD : D.IsCycle)
    (hDlen : 4 ≤ D.length) (hDC : ∀ v ∈ D.support, v ∉ C.support)
    (hno : ¬ HasOddCycleWithTwoChords G)
    {i j k : ℕ} (hi : 0 < i) (hij : i < j) (hjk : j < k) (hk : k < C.length)
    (h₀ : G.Adj z x) (h₁ : G.Adj (D.getVert 1) (C.getVert i))
    (h₂ : G.Adj (D.getVert 2) (C.getVert j))
    (h₃ : G.Adj (D.getVert 3) (C.getVert k)) :
    Even (D.length + i + (k - j) + 2) := by
  have hinjC : ∀ a b : ℕ, a < C.length → b < C.length → a ≠ b →
      C.getVert a ≠ C.getVert b := by
    intro a b ha hb hab heq
    exact hab (hC.getVert_injOn' (show a ≤ C.length - 1 by omega)
      (show b ≤ C.length - 1 by omega) heq)
  have hijV := hinjC i j (by omega) (by omega) (by omega)
  have hkz : C.getVert k ≠ z := by
    simpa only [Walk.getVert_zero] using hinjC k 0 hk (by omega) (by omega)
  let S : Set V := {v | v ∈ C.support ∨ v ∈ (D.drop 3).support}
  let p := Erdos1105.pathSegment D 1 2 (by omega)
  have hp : p.IsPath := CycleArc.segment_isPath D hD 1 2 (by omega) (by omega)
  have hpS : ∀ v ∈ p.support, v ∉ S := by
    intro v hv hvS
    obtain ⟨r, hr1, hr2, hr⟩ :=
      (Erdos1105.mem_pathSegment_support D 1 2 (by omega) (by omega)).mp hv
    rcases hvS with hvC | hvDrop
    · exact hDC v (hr ▸ D.getVert_mem_support r) hvC
    · rw [← hr] at hvDrop
      exact CycleArc.getVert_notMem_drop D hD (by omega) (by omega) (by omega) hvDrop
  have hiS : C.getVert i ∈ S := Or.inl (C.getVert_mem_support i)
  have hjS : C.getVert j ∈ S := Or.inl (C.getVert_mem_support j)
  let E := Ear.ofInternalPath p hp hpS hiS hjS hijV h₁.symm h₂
  have hplen : p.length = 1 := Erdos1105.pathSegment_length D 1 2 (by omega) (by omega)
  have hElen : E.walk.length = 3 := by
    have h := Ear.ofInternalPath_length p hp hpS hiS hjS hijV h₁.symm h₂
    change E.walk.length = p.length + 2 at h
    omega
  have hdropC : ∀ v ∈ (D.drop 3).support, v ∉ C.support := by
    intro v hv
    rw [Walk.drop_support_eq_support_drop_min] at hv
    exact hDC v (List.mem_of_mem_drop hv)
  let L := Ear.ofInternalPath (D.drop 3) (hD.isPath_drop (by omega)) hdropC
    (C.getVert_mem_support k) C.start_mem_support hkz h₃.symm h₀.symm
  have hLlen : L.walk.length = D.length - 3 + 2 := by
    exact (Ear.ofInternalPath_length (D.drop 3) (hD.isPath_drop (by omega)) hdropC
      (C.getVert_mem_support k) C.start_mem_support hkz h₃.symm h₀.symm).trans
      (congrArg (· + 2) (Walk.drop_length D 3))
  let pR := Erdos1105.pathSegment C j k hjk.le
  let qR := C.take i
  have hpR : pR.IsPath := CycleArc.segment_isPath C hC j k hjk.le hk
  have hqR : qR.IsPath := hC.isPath_take (by omega)
  have hpRC : ∀ v ∈ pR.support, v ∈ C.support :=
    Erdos1105.pathSegment_support_subset C j k hjk.le hk.le
  have hqRC : ∀ v ∈ qR.support, v ∈ C.support := by
    intro v hv
    rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  have hpq : pR.support.Disjoint qR.support := by
    intro v hvp hvq
    obtain ⟨r, hjr, hrk, hr⟩ := (Erdos1105.mem_pathSegment_support C j k hjk.le hk.le).mp hvp
    obtain ⟨t, ht, htlen⟩ := Walk.mem_support_iff_exists_getVert.mp hvq
    have hti : t ≤ i := by rw [Walk.take_length] at htlen; omega
    have ht' : C.getVert t = v := by
      change (C.take i).getVert t = v at ht
      simpa only [Walk.take_getVert, Nat.min_eq_right hti] using ht
    have heq : r = t := hC.getVert_injOn' (show r ≤ C.length - 1 by omega)
      (show t ≤ C.length - 1 by omega) (hr.trans ht'.symm)
    omega
  let q := pR.append (L.walk.append qR)
  have hq : q.IsPath := L.isPath_rim_ear_rim pR qR hpR hqR hpRC hqRC hpq
  have hqS : ∀ v ∈ q.support, v ∈ S := by
    intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with hvp | hv
    · exact Or.inl (hpRC v hvp)
    · rcases (Walk.mem_support_append_iff _ _).mp hv with hvL | hvq
      · have hvCases : v = C.getVert k ∨ v ∈ (D.drop 3).support ∨ v = z :=
          (Ear.ofInternalPath_support _ _ _ _ _ _ _ _).mp hvL
        rcases hvCases with rfl | hvm | rfl
        · exact Or.inl (C.getVert_mem_support k)
        · exact Or.inr hvm
        · exact Or.inl C.start_mem_support
      · exact Or.inl (hqRC v hvq)
  have hXq : x ∈ q.support := by
    apply (Walk.mem_support_append_iff _ _).mpr
    right
    apply (Walk.mem_support_append_iff _ _).mpr
    left
    exact Ear.mem_ofInternalPath_of_mem _ _ _ _ _ _ _ _ (D.drop 3).end_mem_support
  have hWq : D.getVert 3 ∈ q.support := by
    apply (Walk.mem_support_append_iff _ _).mpr
    right
    apply (Walk.mem_support_append_iff _ _).mpr
    left
    exact Ear.mem_ofInternalPath_of_mem _ _ _ _ _ _ _ _ (D.drop 3).start_mem_support
  have hYE : D.getVert 1 ∈ E.walk.support :=
    Ear.mem_ofInternalPath_of_mem _ _ _ _ _ _ _ _ p.start_mem_support
  have hZE : D.getVert 2 ∈ E.walk.support :=
    Ear.mem_ofInternalPath_of_mem _ _ _ _ _ _ _ _ p.end_mem_support
  have hYS : D.getVert 1 ∉ S := hpS _ p.start_mem_support
  have hZS : D.getVert 2 ∉ S := hpS _ p.end_mem_support
  have hXnotC := hDC x D.start_mem_support
  have hWnotC := hDC _ (D.getVert_mem_support 3)
  have hXi : x ≠ C.getVert i := fun heq => hXnotC (heq ▸ C.getVert_mem_support i)
  have hXj : x ≠ C.getVert j := fun heq => hXnotC (heq ▸ C.getVert_mem_support j)
  have hWi : D.getVert 3 ≠ C.getVert i := fun heq => hWnotC (heq ▸ C.getVert_mem_support i)
  have hWj : D.getVert 3 ≠ C.getVert j := fun heq => hWnotC (heq ▸ C.getVert_mem_support j)
  have hYX : G.Adj (D.getVert 1) x := (D.adj_snd hD.not_nil).symm
  have hZW : G.Adj (D.getVert 2) (D.getVert 3) := D.adj_getVert_succ (i := 2) (by omega)
  have hne : s(D.getVert 1, x) ≠ s(D.getVert 2, D.getVert 3) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨heq, _⟩ | ⟨heq, _⟩
    · have hidx : 1 = 2 := hD.getVert_injOn' (show 1 ≤ D.length - 1 by omega)
        (show 2 ≤ D.length - 1 by omega) heq
      omega
    · have hidx : 1 = 3 := hD.getVert_injOn' (show 1 ≤ D.length - 1 by omega)
        (show 3 ≤ D.length - 1 by omega) heq
      omega
  have heven := E.even_append_of_two_cross_edges (by omega) q hq hqS hno
    hYE hYS hZE hZS hXq hXi hXj hWq hWi hWj hYX hZW hne
  have hpRlen : pR.length = k - j := Erdos1105.pathSegment_length C j k hjk.le hk.le
  have hqRlen : qR.length = i := by rw [Walk.take_length, Nat.min_eq_left (by omega)]
  have hq₂ : (L.walk.append qR).length = D.length - 3 + 2 + i :=
    (Walk.length_append L.walk qR).trans (congrArg₂ Nat.add hLlen hqRlen)
  have hqlen : q.length = (k - j) + (D.length - 3 + 2 + i) :=
    (Walk.length_append pR (L.walk.append qR)).trans (congrArg₂ Nat.add hpRlen hq₂)
  have heq : D.length + i + (k - j) + 2 = E.walk.length + q.length := by omega
  rwa [heq]

#print axioms four_spokes_long_inner_cycle_even

end Erdos1091.Voss
