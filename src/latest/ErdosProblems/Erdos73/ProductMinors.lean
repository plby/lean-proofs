/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.MinorModels
import ErdosProblems.Erdos73.DegreeRadius
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Product constructions in the qualitative grill bound

A star in a connected repeated column graph yields a complete bipartite
minor, while a path yields an ordinary square-grid copy.
-/

namespace Erdos73

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
open SimpleGraph

variable {W C : Type*} [Fintype C]

def productRow (a : W) : Finset (W × C) := Finset.univ.image fun c ↦ (a, c)

@[simp] theorem mem_productRow {a : W} {x : W × C} : x ∈ productRow a ↔ x.1 = a := by
  rcases x with ⟨b, c⟩
  simp [productRow, eq_comm]

theorem productRow_connected (H : SimpleGraph W) (K : SimpleGraph C)
    (hK : K.Connected) (a : W) :
    ((H □ K).induce (productRow (C := C) a : Set (W × C))).Connected := by
  let f : K →g (H □ K).induce (productRow (C := C) a : Set (W × C)) := {
    toFun := fun c ↦ ⟨(a, c), mem_productRow.mpr rfl⟩
    map_rel' := fun {_ _} h ↦ Or.inr ⟨h, rfl⟩ }
  have hf : Function.Surjective f := by
    rintro ⟨⟨b, c⟩, hbc⟩
    have hb : b = a := mem_productRow.mp hbc
    subst b
    exact ⟨c, rfl⟩
  exact hK.map f hf

/-- A star with `h` leaves, multiplied by any connected graph with at
least `h` chosen vertices, contains an ordinary `K_{h,h}` minor. -/
def completeBipartite_minorModel_of_star_product
    (H : SimpleGraph W) (K : SimpleGraph C) (hK : K.Connected)
    {h : ℕ} (center : W) (leaf : Fin h ↪ W) (column : Fin h ↪ C)
    (hstar : ∀ i, H.Adj (leaf i) center) :
    MinorModel (completeBipartiteGraph (Fin h) (Fin h)) (H □ K) := by
  let branch : Fin h ⊕ Fin h → Finset (W × C) :=
    Sum.elim (fun i ↦ productRow (leaf i)) (fun j ↦ {(center, column j)})
  have hrow (i : Fin h) {x : W × C} : x ∈ branch (.inl i) ↔ x.1 = leaf i :=
    mem_productRow
  have hsingle (j : Fin h) {x : W × C} :
      x ∈ branch (.inr j) ↔ x = (center, column j) := Finset.mem_singleton
  refine {
    branchSet := branch
    branch_nonempty := ?_
    branch_connected := ?_
    branch_disjoint := ?_
    adjacent := ?_ }
  · intro z
    cases z with
    | inl i =>
      let c : C := Classical.choice hK.nonempty
      exact ⟨(leaf i, c), hrow i |>.mpr rfl⟩
    | inr j => exact Finset.singleton_nonempty _
  · intro z
    cases z with
    | inl i => exact productRow_connected H K hK (leaf i)
    | inr j =>
      change ((H □ K).induce (↑({(center, column j)} : Finset (W × C)))).Connected
      rw [Finset.coe_singleton]
      exact SimpleGraph.Connected.of_subsingleton
  · intro u v huv
    apply Finset.disjoint_left.mpr
    intro x hxu hxv
    cases u with
    | inl i =>
      cases v with
      | inl j =>
        exact huv (congrArg Sum.inl (leaf.injective ((hrow i |>.mp hxu).symm.trans
          (hrow j |>.mp hxv))))
      | inr j =>
        have hx := hsingle j |>.mp hxv
        have hc : center = leaf i := by simpa only [hx] using hrow i |>.mp hxu
        exact (hstar i).ne hc.symm
    | inr i =>
      cases v with
      | inl j =>
        have hx := hsingle i |>.mp hxu
        have hc : center = leaf j := by simpa only [hx] using hrow j |>.mp hxv
        exact (hstar j).ne hc.symm
      | inr j =>
        have heq := (hsingle i |>.mp hxu).symm.trans (hsingle j |>.mp hxv)
        exact huv (congrArg Sum.inr (column.injective (congrArg Prod.snd heq)))
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => simp [completeBipartiteGraph] at huv
      | inr j => exact ⟨(leaf i, column j), hrow i |>.mpr rfl,
          (center, column j), hsingle j |>.mpr rfl, Or.inl ⟨hstar i, rfl⟩⟩
    | inr i =>
      cases v with
      | inl j => exact ⟨(center, column i), hsingle i |>.mpr rfl,
          (leaf j, column i), hrow j |>.mpr rfl, Or.inl ⟨(hstar j).symm, rfl⟩⟩
      | inr j => simp [completeBipartiteGraph] at huv

/-- The usual square grid, expressed by Mathlib's two path factors. -/
def squareGrid (g : ℕ) : SimpleGraph (Fin g × Fin g) := pathGraph g □ pathGraph g

/-- Initial subpaths are ordinary subgraph copies. -/
def pathGraphCopyOfLE {g n : ℕ} (hgn : g ≤ n) : (pathGraph g).Copy (pathGraph n) where
  toHom := {
    toFun := Fin.castLE hgn
    map_rel' := by
      intro i j hij
      apply pathGraph_adj.mpr
      exact (pathGraph_adj (n := g)).mp hij }
  injective' := Fin.castLE_injective hgn

/-- Taking products preserves ordinary subgraph copies, without imposing
any nonedge-preservation condition. -/
def boxProdCopy {U U' T T' : Type*}
    {H : SimpleGraph U} {H' : SimpleGraph U'} {K : SimpleGraph T} {K' : SimpleGraph T'}
    (f : H.Copy H') (g : K.Copy K') : (H □ K).Copy (H' □ K') where
  toHom := {
    toFun := fun x ↦ (f x.1, g x.2)
    map_rel' := by
      intro x y hxy
      rcases hxy with ⟨h, heq⟩ | ⟨h, heq⟩
      · exact Or.inl ⟨f.toHom.map_adj h, congrArg g heq⟩
      · exact Or.inr ⟨g.toHom.map_adj h, congrArg f heq⟩ }
  injective' := by
    intro x y hxy
    exact Prod.ext (f.injective (congrArg Prod.fst hxy)) (g.injective (congrArg Prod.snd hxy))

/-- A long simple path in the column graph gives an actual grid copy
in its product with a sufficiently long horizontal path. -/
def squareGridCopyOfPath {H : SimpleGraph W} {u v : W} (P : H.Walk u v)
    (hP : P.IsPath) {g n : ℕ} (hg : g ≤ P.length + 1) (hn : g ≤ n) :
    (squareGrid g).Copy (H □ pathGraph n) :=
  boxProdCopy (hP.pathGraphCopy.comp (pathGraphCopyOfLE hg)) (pathGraphCopyOfLE hn)

/-- The path-or-degree counting bound now supplies actual minor models
in the repeated-column product, including both alternatives. -/
theorem product_has_grid_or_completeBipartite
    [Fintype W] (H : SimpleGraph W) (hH : H.Connected)
    (g h n : ℕ) (hh : 0 < h) (hsize : h ^ g < Fintype.card W)
    (hgn : g ≤ n) (hhn : h ≤ n) :
    IsMinor (squareGrid g) (H □ pathGraph n) ∨
      IsMinor (completeBipartiteGraph (Fin h) (Fin h)) (H □ pathGraph n) := by
  have hbound : (h - 1 + 1) ^ g < Fintype.card W := by
    simpa only [Nat.sub_add_cancel hh] using hsize
  rcases exists_longPath_or_large_degree H hH (h - 1) g hbound with
    ⟨u, v, P, hP, hlen⟩ | ⟨center, hdeg⟩
  · exact Or.inl ⟨MinorModel.of_copy (squareGridCopyOfPath P hP (by omega) hgn)⟩
  · have hcard : Fintype.card (Fin h) ≤ Fintype.card (H.neighborSet center) := by
      rw [Fintype.card_fin, H.card_neighborSet_eq_degree]
      omega
    let f : Fin h ↪ H.neighborSet center :=
      Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
    let leaf : Fin h ↪ W := f.trans (Function.Embedding.subtype _)
    let column : Fin h ↪ Fin n := ⟨Fin.castLE hhn, Fin.castLE_injective hhn⟩
    have hK : (pathGraph n).Connected := by
      have : Nonempty (Fin n) := ⟨⟨0, hh.trans_le hhn⟩⟩
      exact ⟨pathGraph_preconnected n⟩
    exact Or.inr ⟨completeBipartite_minorModel_of_star_product H (pathGraph n) hK
      center leaf column (fun i ↦ (f i).2.symm)⟩

end
end Erdos73
