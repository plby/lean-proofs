import ErdosProblems.Erdos19.GraphMatching
import Mathlib.Data.ZMod.Basic

/-! # Round-robin matchings on an odd auxiliary set -/

namespace Erdos19

open _root_.SimpleGraph

theorem zmod_odd_double_injective (t : ℕ) :
    Function.Injective (fun x : ZMod (2 * t + 1) ↦ x + x) := by
  intro x y hxy
  have hmod : (2 : ZMod (2 * t + 1)) * t + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      ZMod.natCast_self (2 * t + 1)
  apply sub_eq_zero.mp
  linear_combination (x - y) * hmod - (t : ZMod (2 * t + 1)) * hxy

def roundRobinMatching (t : ℕ) (i : ZMod (2 * t + 1)) :
    (⊤ : _root_.SimpleGraph (ZMod (2 * t + 1))).Subgraph where
  verts := {x | x ≠ i}
  Adj x y := x ≠ y ∧ x + y = i + i
  adj_sub := fun h ↦ h.1
  edge_vert := by
    intro x y h hxi
    subst x
    have hyi : y = i := add_left_cancel h.2
    exact h.1 hyi.symm
  symm.symm := by
    intro x y h
    exact ⟨h.1.symm, (add_comm y x).trans h.2⟩

@[simp] theorem roundRobinMatching_verts (t : ℕ) (i : ZMod (2 * t + 1)) :
    (roundRobinMatching t i).verts = {i}ᶜ := rfl

theorem roundRobinMatching_isMatching (t : ℕ) (i : ZMod (2 * t + 1)) :
    (roundRobinMatching t i).IsMatching := by
  intro x hx
  have hxy : x ≠ i + i - x := by
    intro h
    have hdouble : x + x = i + i := by linear_combination h
    exact hx (zmod_odd_double_injective t hdouble)
  refine ⟨i + i - x, ⟨hxy, by abel⟩, ?_⟩
  intro y hy
  change x ≠ y ∧ x + y = i + i at hy
  linear_combination hy.2

theorem roundRobinMatching_pairwise_disjoint (t : ℕ) :
    Pairwise (fun i j ↦ Disjoint (roundRobinMatching t i).spanningCoe
      (roundRobinMatching t j).spanningCoe) := by
  intro i j hij
  apply _root_.SimpleGraph.disjoint_left.mpr
  intro x y hi hj
  exact hij (zmod_odd_double_injective t (hi.2.symm.trans hj.2))

theorem roundRobinMatching_covers_edges (t : ℕ) (x y : ZMod (2 * t + 1)) (hxy : x ≠ y) :
    ∃ i, (roundRobinMatching t i).Adj x y := by
  let : NeZero (2 * t + 1) := ⟨by omega⟩
  have hs := Finite.surjective_of_injective (zmod_odd_double_injective t)
  obtain ⟨i, hi⟩ := hs (x + y)
  exact ⟨i, hxy, hi.symm⟩

#print axioms roundRobinMatching_isMatching
#print axioms roundRobinMatching_covers_edges

end Erdos19
