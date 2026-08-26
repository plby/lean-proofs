/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.ProductMinors
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort

/-!
# Half-open row blocks for repeated grill columns

The branch sets explicitly replace the contraction of horizontal gaps.
-/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
open SimpleGraph

variable {m n b : ℕ}

def columnUpper (c : Fin b ↪o Fin n) (j : Fin b) : ℕ :=
  if h : j.val + 1 < b then (c ⟨j.val + 1, h⟩).val else n

theorem columnUpper_le (c : Fin b ↪o Fin n) (j : Fin b) : columnUpper c j ≤ n := by
  unfold columnUpper
  split
  · exact (c _).isLt.le
  · exact le_rfl

theorem column_lt_upper (c : Fin b ↪o Fin n) (j : Fin b) : (c j).val < columnUpper c j := by
  unfold columnUpper
  split
  · exact c.strictMono (show j < ⟨j.val + 1, _⟩ by exact Nat.lt_succ_self _)
  · exact (c j).isLt

theorem columnUpper_le_column (c : Fin b ↪o Fin n) {j k : Fin b} (hjk : j < k) :
    columnUpper c j ≤ (c k).val := by
  have hj : j.val + 1 < b := lt_of_le_of_lt (Nat.succ_le_of_lt hjk) k.isLt
  simp only [columnUpper, dif_pos hj]
  exact c.monotone (show (⟨j.val + 1, hj⟩ : Fin b) ≤ k from Nat.succ_le_of_lt hjk)

theorem columnUpper_eq_next (c : Fin b ↪o Fin n) {j k : Fin b}
    (hjk : j.val + 1 = k.val) : columnUpper c j = (c k).val := by
  have hj : j.val + 1 < b := by omega
  simp only [columnUpper, dif_pos hj]
  have heq : (⟨j.val + 1, hj⟩ : Fin b) = k := Fin.ext hjk
  rw [heq]

def columnBlock (c : Fin b ↪o Fin n) (r : Fin m) (j : Fin b) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun x ↦ x.1 = r ∧ (c j).val ≤ x.2.val ∧ x.2.val < columnUpper c j

@[simp] theorem mem_columnBlock (c : Fin b ↪o Fin n) {r : Fin m} {j : Fin b}
    {x : Fin m × Fin n} :
    x ∈ columnBlock c r j ↔ x.1 = r ∧ (c j).val ≤ x.2.val ∧ x.2.val < columnUpper c j := by
  simp only [columnBlock, Finset.mem_filter, Finset.mem_univ, true_and]

theorem column_mem_block (c : Fin b ↪o Fin n) (r : Fin m) (j : Fin b) :
    (r, c j) ∈ columnBlock c r j :=
  mem_columnBlock c |>.mpr ⟨rfl, le_rfl, column_lt_upper c j⟩

theorem columnBlock_connected
    (G : SimpleGraph (Fin m × Fin n))
    (hrow : ∀ r s t, (pathGraph n).Adj s t → G.Adj (r, s) (r, t))
    (c : Fin b ↪o Fin n) (r : Fin m) (j : Fin b) :
    (G.induce (columnBlock c r j : Set (Fin m × Fin n))).Connected := by
  let a := (c j).val
  let z := columnUpper c j
  have haz : a < z := column_lt_upper c j
  have hzn : z ≤ n := columnUpper_le c j
  let f : pathGraph (z - a) →g G.induce (columnBlock c r j : Set (Fin m × Fin n)) := {
    toFun := fun k ↦ ⟨(r, ⟨a + k.val, by omega⟩),
      (mem_columnBlock c).mpr ⟨rfl, by change a ≤ a + k.val; omega,
        by change a + k.val < z; omega⟩⟩
    map_rel' := by
      intro s t hst
      apply hrow r
      apply pathGraph_adj.mpr
      have h := pathGraph_adj.mp hst
      change a + s.val + 1 = a + t.val ∨ a + t.val + 1 = a + s.val
      omega }
  have hf : Function.Surjective f := by
    rintro ⟨⟨s, x⟩, hx⟩
    obtain ⟨hs, hax, hxz⟩ := (mem_columnBlock c).mp hx
    change a ≤ x.val at hax
    change x.val < z at hxz
    change s = r at hs
    subst s
    let k : Fin (z - a) := ⟨x.val - a, by omega⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    change (r, (⟨a + k.val, _⟩ : Fin n)) = (r, x)
    apply congrArg (fun y : Fin n ↦ (r, y))
    apply Fin.ext
    change a + (x.val - a) = x.val
    omega
  have : Nonempty (Fin (z - a)) := ⟨⟨0, by omega⟩⟩
  exact (show (pathGraph (z - a)).Connected from ⟨pathGraph_preconnected _⟩).map f hf

/-- Equal column graphs in increasing positions give an actual product
minor. All branch sets, horizontal gaps, and inter-column edges are explicit. -/
def repeatedColumns_minorModel
    (G : SimpleGraph (Fin m × Fin n)) (H : SimpleGraph (Fin m))
    (hrow : ∀ r s t, (pathGraph n).Adj s t → G.Adj (r, s) (r, t))
    (c : Fin b ↪o Fin n)
    (hcol : ∀ j, ∀ r s, H.Adj r s → G.Adj (r, c j) (s, c j)) :
    MinorModel (H □ pathGraph b) G := by
  refine {
    branchSet := fun x ↦ columnBlock c x.1 x.2
    branch_nonempty := fun x ↦ ⟨(x.1, c x.2), column_mem_block c x.1 x.2⟩
    branch_connected := fun x ↦ columnBlock_connected G hrow c x.1 x.2
    branch_disjoint := ?_
    adjacent := ?_ }
  · intro u v huv
    apply Finset.disjoint_left.mpr
    intro x hxu hxv
    obtain ⟨hru, hlu, hxu⟩ := (mem_columnBlock c).mp hxu
    obtain ⟨hrv, hlv, hxv⟩ := (mem_columnBlock c).mp hxv
    have hrows : u.1 = v.1 := hru.symm.trans hrv
    have hcols : u.2 ≠ v.2 := fun h ↦ huv (Prod.ext hrows h)
    rcases lt_or_gt_of_ne hcols with h | h
    · have hle := columnUpper_le_column c h
      omega
    · have hle := columnUpper_le_column c h
      omega
  · intro u v huv
    rcases huv with ⟨hH, hc⟩ | ⟨hP, hr⟩
    · refine ⟨(u.1, c u.2), column_mem_block c _ _,
        (v.1, c v.2), column_mem_block c _ _, ?_⟩
      rw [← hc]
      exact hcol u.2 u.1 v.1 hH
    · have hnext (j k : Fin b) (hjk : j.val + 1 = k.val) (r : Fin m) :
          ∃ x ∈ columnBlock c r j, ∃ y ∈ columnBlock c r k, G.Adj x y := by
        have hjklt : j < k := by change j.val < k.val; omega
        have hlt : (c j).val < (c k).val := c.strictMono hjklt
        let x : Fin n := ⟨(c k).val - 1, by omega⟩
        refine ⟨(r, x), (mem_columnBlock c).mpr ⟨rfl, ?_, ?_⟩,
          (r, c k), column_mem_block c _ _, hrow r _ _ ?_⟩
        · change (c j).val ≤ (c k).val - 1
          omega
        · rw [columnUpper_eq_next c hjk]
          change (c k).val - 1 < (c k).val
          omega
        · apply pathGraph_adj.mpr
          left
          change (c k).val - 1 + 1 = (c k).val
          omega
      rcases pathGraph_adj.mp hP with hjk | hkj
      · obtain ⟨x, hx, y, hy, hxy⟩ := hnext u.2 v.2 hjk u.1
        exact ⟨x, hx, y, by rw [← hr]; exact hy, hxy⟩
      · obtain ⟨y, hy, x, hx, hyx⟩ := hnext v.2 u.2 hkj u.1
        exact ⟨x, hx, y, by rw [← hr]; exact hy, hyx.symm⟩

/-- The graph induced in one column, relabelled by its row indices. -/
def grillColumnGraph (G : SimpleGraph (Fin m × Fin n)) (j : Fin n) : SimpleGraph (Fin m) :=
  G.comap fun r ↦ (r, j)

/-- A grill has all horizontal path edges and connected column graphs;
other edges of the host graph are unrestricted. -/
def IsGrill (G : SimpleGraph (Fin m × Fin n)) : Prop :=
  (∀ r s t, (pathGraph n).Adj s t → G.Adj (r, s) (r, t)) ∧
    ∀ j, (grillColumnGraph G j).Connected

/-- A finite code of the full adjacency relation of a labelled column. -/
def grillColumnCode (G : SimpleGraph (Fin m × Fin n)) (j : Fin n) :
    Finset (Fin m × Fin m) := Finset.univ.filter fun x ↦ G.Adj (x.1, j) (x.2, j)

theorem grillColumnGraph_eq_of_code_eq (G : SimpleGraph (Fin m × Fin n))
    {j k : Fin n} (h : grillColumnCode G j = grillColumnCode G k) :
    grillColumnGraph G j = grillColumnGraph G k := by
  ext r s
  have heq : (r, s) ∈ grillColumnCode G j ↔ (r, s) ∈ grillColumnCode G k := by rw [h]
  change G.Adj (r, j) (s, j) ↔ G.Adj (r, k) (s, k)
  simpa only [grillColumnCode, Finset.mem_filter, Finset.mem_univ, true_and] using heq

/-- The qualitative grill theorem, with explicit finite-pigeonhole
constants and ordinary minor models for both outcomes. -/
theorem grill_has_grid_or_completeBipartite
    (G : SimpleGraph (Fin m × Fin n)) (hG : IsGrill G)
    (g h : ℕ) (hh : 0 < h) (hm : h ^ g < m)
    (hn : max g h * 2 ^ (m * m) ≤ n) :
    IsMinor (squareGrid g) G ∨ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G := by
  let b := max g h
  have hb : 0 < b := hh.trans_le (Nat.le_max_right _ _)
  have hcard : Fintype.card (Finset (Fin m × Fin m)) * b ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_finset, Fintype.card_prod, Fintype.card_fin,
      Nat.mul_comm, b] using hn
  obtain ⟨S, hS⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (grillColumnCode G) hcard
  let J := Finset.univ.filter fun j ↦ grillColumnCode G j = S
  have hJ : b ≤ J.card := hS
  let c : Fin b ↪o Fin n := J.orderEmbOfCardLe hJ
  have hcode (j : Fin b) : grillColumnCode G (c j) = S :=
    (Finset.mem_filter.mp (J.orderEmbOfCardLe_mem hJ j)).2
  let zero : Fin b := ⟨0, hb⟩
  let H := grillColumnGraph G (c zero)
  have hH : H.Connected := hG.2 (c zero)
  have hcolumns (j : Fin b) : H = grillColumnGraph G (c j) :=
    grillColumnGraph_eq_of_code_eq G ((hcode zero).trans (hcode j).symm)
  have hcol (j : Fin b) (r s : Fin m) (hrs : H.Adj r s) : G.Adj (r, c j) (s, c j) := by
    rw [hcolumns j] at hrs
    exact hrs
  have hminor : IsMinor (H □ pathGraph b) G :=
    ⟨repeatedColumns_minorModel G H hG.1 c hcol⟩
  have hsize : h ^ g < Fintype.card (Fin m) := by simpa using hm
  rcases product_has_grid_or_completeBipartite H hH g h b hh hsize
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) with hgrid | hbip
  · exact Or.inl (hgrid.trans hminor)
  · exact Or.inr (hbip.trans hminor)

end
end Erdos73
