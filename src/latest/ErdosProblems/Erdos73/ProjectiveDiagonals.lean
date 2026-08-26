import ErdosProblems.Erdos73.TwistedGridCoordinates
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Explicit selected diagonals in the capped twisted-square quadrangulation. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph

abbrev ProjectiveFace (n : ℕ) := (Fin n × Fin (n - 1)) ⊕ Fin (n - 1)

def projectiveRoot {n : ℕ} (hn : 2 ≤ n) : Fin n × Fin n :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

def projectiveBoundary {n : ℕ} (hn : 2 ≤ n) (i : Fin (2 * n)) : Fin n × Fin n :=
  if hi : i.val < n then (⟨i.val, hi⟩, ⟨0, by omega⟩)
  else (⟨i.val - n, by have hh := i.isLt; omega⟩, ⟨n - 1, by omega⟩)

def projectiveDiagonalEnds {n : ℕ} (hn : 2 ≤ n) :
    ProjectiveFace n → (Fin n × Fin n) × (Fin n × Fin n)
  | Sum.inl (r, c) =>
    if hr : r.val + 1 < n then
      if r.val = 0 ∧ c.val % 2 = 1 then
        ((⟨0, by omega⟩, ⟨c.val + 1, by have hh := c.isLt; omega⟩),
          (⟨1, by omega⟩, ⟨c.val, by have hh := c.isLt; omega⟩))
      else ((r, ⟨c.val, by have hh := c.isLt; omega⟩),
        (⟨r.val + 1, hr⟩, ⟨c.val + 1, by have hh := c.isLt; omega⟩))
    else ((r, ⟨c.val, by have hh := c.isLt; omega⟩),
      (⟨0, by omega⟩, ⟨n - 2 - c.val, by omega⟩))
  | Sum.inr j =>
    (projectiveRoot hn,
      projectiveBoundary hn ⟨2 * j.val + 2, by have hh := j.isLt; omega⟩)

def projectiveDiagonalGraph {n : ℕ} (hn : 2 ≤ n) : SimpleGraph (Fin n × Fin n) :=
  fromEdgeSet (Set.range fun f : ProjectiveFace n =>
    s((projectiveDiagonalEnds hn f).1, (projectiveDiagonalEnds hn f).2))

theorem projectiveDiagonalEnds_ne {n : ℕ} (hn : 2 ≤ n) (f : ProjectiveFace n) :
    (projectiveDiagonalEnds hn f).1 ≠ (projectiveDiagonalEnds hn f).2 := by
  intro he
  have hr := congrArg (fun v : Fin n × Fin n => v.1.val) he
  have hc := congrArg (fun v : Fin n × Fin n => v.2.val) he
  rcases f with ⟨r, c⟩ | j
  · have hrr := r.isLt
    have hcc := c.isLt
    dsimp only [projectiveDiagonalEnds] at hr hc
    split_ifs at hr hc <;> simp only [Prod.fst, Prod.snd, Fin.val_mk] at hr hc <;> omega
  · have hj := j.isLt
    dsimp only [projectiveDiagonalEnds, projectiveRoot, projectiveBoundary] at hr hc
    split_ifs at hr hc <;> simp only [Prod.fst, Prod.snd, Fin.val_mk] at hr hc <;> omega

theorem projectiveDiagonal_adj {n : ℕ} (hn : 2 ≤ n) (f : ProjectiveFace n) :
    (projectiveDiagonalGraph hn).Adj
      (projectiveDiagonalEnds hn f).1 (projectiveDiagonalEnds hn f).2 :=
  ⟨⟨f, rfl⟩, projectiveDiagonalEnds_ne hn f⟩

theorem projectiveDiagonal_adj_southeast {n : ℕ} (hn : 2 ≤ n) (r c : ℕ)
    (hr : r + 1 < n) (hc : c + 1 < n) (hregular : r ≠ 0 ∨ c % 2 = 0) :
    (projectiveDiagonalGraph hn).Adj
      (⟨r, by omega⟩, ⟨c, by omega⟩) (⟨r + 1, hr⟩, ⟨c + 1, hc⟩) := by
  have hh := projectiveDiagonal_adj hn (Sum.inl (⟨r, by omega⟩, ⟨c, by omega⟩))
  dsimp only [projectiveDiagonalEnds] at hh
  rw [dif_pos hr, if_neg (by omega)] at hh
  exact hh

theorem projectiveDiagonal_adj_top_switch {n : ℕ} (hn : 2 ≤ n) (c : ℕ)
    (hc : c + 1 < n) (hodd : c % 2 = 1) :
    (projectiveDiagonalGraph hn).Adj
      (⟨0, by omega⟩, ⟨c + 1, hc⟩) (⟨1, by omega⟩, ⟨c, by omega⟩) := by
  have hh := projectiveDiagonal_adj hn (Sum.inl (⟨0, by omega⟩, ⟨c, by omega⟩))
  dsimp only [projectiveDiagonalEnds] at hh
  rw [dif_pos (by omega), if_pos ⟨rfl, hodd⟩] at hh
  exact hh

theorem projectiveDiagonal_adj_wrap {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (hc : c + 1 < n) :
    (projectiveDiagonalGraph hn).Adj
      (⟨n - 1, by omega⟩, ⟨c, by omega⟩) (⟨0, by omega⟩, ⟨n - 2 - c, by omega⟩) := by
  have hh := projectiveDiagonal_adj hn (Sum.inl (⟨n - 1, by omega⟩, ⟨c, by omega⟩))
  dsimp only [projectiveDiagonalEnds] at hh
  rw [dif_neg (by omega)] at hh
  exact hh

theorem projectiveDiagonal_adj_cap {n : ℕ} (hn : 2 ≤ n) (j : Fin (n - 1)) :
    (projectiveDiagonalGraph hn).Adj (projectiveRoot hn)
      (projectiveBoundary hn ⟨2 * j.val + 2, by have hh := j.isLt; omega⟩) :=
  projectiveDiagonal_adj hn (Sum.inr j)

theorem projectiveDiagonal_adj_left_even {n : ℕ} (hn : 2 ≤ n) (r : Fin n)
    (hr : 0 < r.val) (heven : r.val % 2 = 0) :
    (projectiveDiagonalGraph hn).Adj (projectiveRoot hn) (r, ⟨0, by omega⟩) := by
  have hdiv := Nat.mod_add_div r.val 2
  let j : Fin (n - 1) := ⟨r.val / 2 - 1, by have hh := r.isLt; omega⟩
  have hj : 2 * j.val + 2 = r.val := by dsimp only [j]; omega
  have hh := projectiveDiagonal_adj_cap hn j
  dsimp only [projectiveBoundary] at hh
  rw [dif_pos (by omega)] at hh
  convert hh using 1
  exact Prod.ext (Fin.ext hj.symm) rfl

theorem projectiveDiagonal_adj_right_even {n : ℕ} (hn : 2 ≤ n) (heven : n % 2 = 0)
    (r : Fin n) (hr : r.val % 2 = 0) :
    (projectiveDiagonalGraph hn).Adj (projectiveRoot hn) (r, ⟨n - 1, by omega⟩) := by
  have hmod : (n + r.val) % 2 = 0 := by omega
  have hdiv := Nat.mod_add_div (n + r.val) 2
  let j : Fin (n - 1) := ⟨(n + r.val) / 2 - 1, by have hh := r.isLt; omega⟩
  have hj : 2 * j.val + 2 = n + r.val := by dsimp only [j]; omega
  have hh := projectiveDiagonal_adj_cap hn j
  dsimp only [projectiveBoundary] at hh
  rw [dif_neg (by omega)] at hh
  convert hh using 1
  apply Prod.ext
  · apply Fin.ext
    dsimp only
    omega
  · rfl

end
end Erdos73
