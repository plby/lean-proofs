/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossSpokePath

/-! # The two final cycles on four ordered attachments -/

open SimpleGraph

namespace Erdos1091.Voss

/-- The inner three-edge path and the long outer arc form the second
of Voss's final cycles; the two middle spokes are its chords. -/
theorem four_spokes_short_inner_cycle_even
    {V : Type*} {G : SimpleGraph V} {z x : V}
    (C : G.Walk z z) (hC : C.IsCycle) (D : G.Walk x x) (hD : D.IsCycle)
    (hDlen : 4 ≤ D.length) (hDC : ∀ v ∈ D.support, v ∉ C.support)
    (hno : ¬ HasOddCycleWithTwoChords G)
    {i j k : ℕ} (hi : 0 < i) (hij : i < j) (hjk : j < k) (hk : k < C.length)
    (h₀ : G.Adj z x) (h₁ : G.Adj (D.getVert 1) (C.getVert i))
    (h₂ : G.Adj (D.getVert 2) (C.getVert j))
    (h₃ : G.Adj (D.getVert 3) (C.getVert k)) : Even (k + 5) := by
  have hinjC : ∀ a b : ℕ, a < C.length → b < C.length → a ≠ b →
      C.getVert a ≠ C.getVert b := by
    intro a b ha hb hab heq
    exact hab (hC.getVert_injOn' (show a ≤ C.length - 1 by omega)
      (show b ≤ C.length - 1 by omega) heq)
  have hzk : z ≠ C.getVert k := by
    simpa only [Walk.getVert_zero] using hinjC 0 k (by omega) hk (by omega)
  let p := D.take 3
  have hp : p.IsPath := hD.isPath_take (by omega)
  have hpD : ∀ v ∈ p.support, v ∈ D.support := by
    intro v hv
    rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  have hpC : ∀ v ∈ p.support, v ∉ C.support := fun v hv => hDC v (hpD v hv)
  let E := Ear.ofInternalPath p hp hpC C.start_mem_support (C.getVert_mem_support k) hzk h₀ h₃
  have hplen : p.length = 3 := by rw [Walk.take_length, Nat.min_eq_left (by omega)]
  have hElen : E.walk.length = 5 := by
    have h := Ear.ofInternalPath_length p hp hpC C.start_mem_support
      (C.getVert_mem_support k) hzk h₀ h₃
    change E.walk.length = p.length + 2 at h
    omega
  let q := (C.take k).reverse
  have hq : q.IsPath := (hC.isPath_take hk).reverse
  have hqC : ∀ v ∈ q.support, v ∈ C.support := by
    intro v hv
    rw [Walk.support_reverse, List.mem_reverse, Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  have hqmem : ∀ t ≤ k, C.getVert t ∈ q.support := by
    intro t ht
    rw [Walk.support_reverse, List.mem_reverse]
    simpa only [Walk.take_getVert, Nat.min_eq_right ht] using (C.take k).getVert_mem_support t
  have hpMem : ∀ t ≤ 3, D.getVert t ∈ E.walk.support := by
    intro t ht
    apply Ear.mem_ofInternalPath_of_mem
    simpa only [Walk.take_getVert, Nat.min_eq_right ht] using (D.take 3).getVert_mem_support t
  have hiZ : C.getVert i ≠ z := by
    simpa only [Walk.getVert_zero] using hinjC i 0 (by omega) (by omega) (by omega)
  have hjZ : C.getVert j ≠ z := by
    simpa only [Walk.getVert_zero] using hinjC j 0 (by omega) (by omega) (by omega)
  have hiK := hinjC i k (by omega) hk (by omega)
  have hjK := hinjC j k (by omega) hk (by omega)
  have hne : s(D.getVert 1, C.getVert i) ≠ s(D.getVert 2, C.getVert j) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨heq, _⟩ | ⟨heq, _⟩
    · have hidx : 1 = 2 := hD.getVert_injOn' (show 1 ≤ D.length - 1 by omega)
        (show 2 ≤ D.length - 1 by omega) heq
      omega
    · exact hDC _ (D.getVert_mem_support 1) (heq ▸ C.getVert_mem_support j)
  have heven := E.even_append_of_two_cross_edges (by omega) q hq hqC hno
    (hpMem 1 (by omega)) (hDC _ (D.getVert_mem_support 1))
    (hpMem 2 (by omega)) (hDC _ (D.getVert_mem_support 2))
    (hqmem i (by omega)) hiZ hiK (hqmem j hjk.le) hjZ hjK h₁ h₂ hne
  have hqlen : q.length = k := by
    rw [Walk.length_reverse, Walk.take_length, Nat.min_eq_left hk.le]
  have heq : k + 5 = E.walk.length + q.length := by omega
  rwa [heq]

#print axioms four_spokes_short_inner_cycle_even

end Erdos1091.Voss
