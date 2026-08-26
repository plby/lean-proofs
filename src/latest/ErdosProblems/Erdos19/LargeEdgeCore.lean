import ErdosProblems.Erdos19.DenseRankWindow
import ErdosProblems.Erdos19.PeelableColoring

/-! # A large-edge coloring or concentration alternative

The core is chosen with its coloring-extension property intact. In the
concentration alternative, the rest of the hypergraph remains peelable
relative to this core; this is stronger than merely locating a dense family.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {X : Type*} [Fintype X]

theorem large_edge_colorable_or_concentrated_core (H : SetHypergraph X)
    (hlinear : H.IsLinear) (h : ℕ) (hh : 16 ≤ h)
    (hn : h ^ 4 ≤ Fintype.card X) (hmin : ∀ e : H, h ^ 4 ≤ e.1.ncard) :
    H.EdgeColorable (Fintype.card X - Fintype.card X / h ^ 4) ∨
      ∃ S W : Finset H, ∃ r : ℕ,
        S.Nonempty ∧ W ⊆ S ∧ h ^ 4 ≤ r ∧
        IsDenseCore H.lineGraph S (Fintype.card X - Fintype.card X / h ^ 4) ∧
        IsPeelableOutside H.lineGraph univ S
          (Fintype.card X - Fintype.card X / h ^ 4) ∧
        (∀ e ∈ S, r ≤ e.1.ncard) ∧
        (∀ e ∈ W, e.1.ncard ≤ r + r / h) ∧
        (h - 10) * (Fintype.card X) ^ 2 ≤
          h * (∑ e ∈ W, e.1.ncard * (e.1.ncard - 1)) := by
  classical
  let m := Fintype.card X - Fintype.card X / h ^ 4
  have hhpos : 0 < h := by omega
  have hhpow : 1 < h ^ 4 := by
    have hx : 2 ≤ h ^ 2 := by nlinarith only [hh]
    have hy := Nat.mul_le_mul hx hx
    nlinarith only [hy]
  have hnpos : 0 < Fintype.card X := by omega
  have hmpos : 0 < m := Nat.sub_pos_of_lt (Nat.div_lt_self hnpos hhpow)
  obtain ⟨S, hS, hdense, hpeel⟩ :=
    exists_dense_core_with_peelable_remainder H.lineGraph univ m
  by_cases hne : S.Nonempty
  · right
    obtain ⟨r, W, hr, hWS, hrmin, hrmax, hweight⟩ :=
      H.exists_dense_core_rank_window hlinear S h hh (fun e _ ↦ hmin e) hdense hne
    exact ⟨S, W, r, hne, hWS, hr, hdense, hpeel, hrmin, hrmax, hweight⟩
  · left
    have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    let c₀ : H → Fin m := fun _ ↦ ⟨0, hmpos⟩
    obtain ⟨c, _, _, hc⟩ := hpeel.exists_list_coloring_extension hS
      (fun _ ↦ (univ : Finset (Fin m))) (fun _ _ ↦ by simp)
      c₀ (by simp only [hSempty, notMem_empty, false_implies, implies_true])
    refine ⟨{ color := c, valid := ?_ }⟩
    intro e f hef hinter
    exact hc e (mem_univ _) f (mem_univ _) ⟨hef, hinter⟩

#print axioms large_edge_colorable_or_concentrated_core

end Erdos19.SetHypergraph
