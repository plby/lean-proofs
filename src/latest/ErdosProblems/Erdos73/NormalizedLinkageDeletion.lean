/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.PregrillMinor

/-!
# The qualitative pregrill theorem and normalized linkage deletion

The constants are intentionally large and elementary. The arbitrary-linkage
deletion/contraction normalization remains a separate theorem.
-/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

def qualitativeGrillRows (g h : ℕ) : ℕ := h ^ g + 1

def qualitativeGrillColumns (g h : ℕ) : ℕ :=
  max g h * 2 ^ (qualitativeGrillRows g h * qualitativeGrillRows g h)

theorem qualitativeGrillRows_pos (g h : ℕ) : 0 < qualitativeGrillRows g h := Nat.zero_lt_succ _

theorem qualitativeGrillColumns_pos (g h : ℕ) (hh : 0 < h) : 0 < qualitativeGrillColumns g h :=
  Nat.mul_pos (hh.trans_le (Nat.le_max_right _ _)) (pow_pos (by omega) _)

/-- The full qualitative pregrill theorem, including averaging, column
normalization, and actual grill-to-grid/complete-bipartite minor models. -/
theorem pregrill_has_grid_or_completeBipartite
    {V : Type*} [Fintype V] {G : SimpleGraph V} {m n d : ℕ}
    (P : Pregrill G m n d) (g h : ℕ) (hh : 0 < h)
    (hm : qualitativeGrillRows g h ≤ m)
    (hd : 2 * qualitativeGrillRows g h * d ≤ m)
    (hn : 2 * qualitativeGrillColumns g h ≤ n) :
    IsMinor (squareGrid g) G ∨ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G := by
  obtain ⟨F⟩ := P.exists_fullPregrill (qualitativeGrillRows g h) (qualitativeGrillColumns g h)
    (qualitativeGrillRows_pos g h) hm hd hn
  obtain ⟨H, hH, hHG⟩ := F.exists_grillMinor_of_pos
    (qualitativeGrillRows_pos g h) (qualitativeGrillColumns_pos g h hh)
  rcases grill_has_grid_or_completeBipartite H hH g h hh
      (Nat.lt_succ_self _) le_rfl with hgrid | hbip
  · exact Or.inl (hgrid.trans hHG)
  · exact Or.inr (hbip.trans hHG)

/-- In the unique spanning normal form, deleting one of sufficiently
many disjoint connected columns retains a positive fraction of a linkage
unless one of the two ordinary minors exists. The returned paths lie
outside the deleted column and have endpoints outside it as well. -/
theorem unique_linkage_avoiding_connected_column
    {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V} {A B : Finset V}
    (R : PerfectPathPacking G A B) (hunique : R.IsUniqueLinkage)
    (Q : I → Finset V) (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (g h : ℕ) (hh : 0 < h) (hm : qualitativeGrillRows g h ≤ R.card)
    (hsize : (R.card + 1) * (2 * qualitativeGrillColumns g h) ≤ Fintype.card I)
    (hgrid : ¬ IsMinor (squareGrid g) G)
    (hbip : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G) :
    ∃ i, ∃ P : PathPacking G (A \ Q i) (B \ Q i),
      R.card / (2 * qualitativeGrillRows g h) + 1 ≤ P.card ∧
        ∀ r, Disjoint (P.path r).vertexSet (Q i) := by
  let k := R.card / (2 * qualitativeGrillRows g h) + 1
  rcases pregrill_or_avoiding_linkage_of_unique R hunique Q hne hconn hdisj
      (2 * qualitativeGrillColumns g h) k hsize with havoid | hpre
  · exact havoid
  · obtain ⟨pregrill⟩ := hpre
    have hd : 2 * qualitativeGrillRows g h * (k - 1) ≤ R.card := by
      dsimp only [k]
      rw [Nat.add_sub_cancel, Nat.mul_comm]
      exact Nat.div_mul_le_self _ _
    rcases pregrill_has_grid_or_completeBipartite pregrill g h hh hm hd le_rfl with h | h
    · exact (hgrid h).elim
    · exact (hbip h).elim

end
end Erdos73
