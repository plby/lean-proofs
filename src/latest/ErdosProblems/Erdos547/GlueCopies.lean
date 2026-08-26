import ErdosProblems.Erdos547.Attachment

/-!
# Gluing copies on disjoint vertex sets with all cross edges verified
-/

namespace Erdos547

open Finset SimpleGraph

theorem glue_copies {U V : Type*} [DecidableEq U] (T : SimpleGraph U) (G : SimpleGraph V)
    (A B : Finset U) (hAB : Disjoint A B)
    (f : (T.induce (A : Set U)).Copy G) (g : (T.induce (B : Set U)).Copy G)
    (himages : ∀ x : ↥A, ∀ y : ↥B, f x ≠ g y)
    (hcross : ∀ x : ↥A, ∀ y : ↥B, T.Adj x.val y.val → G.Adj (f x) (g y)) :
    ∃ h : (T.induce ((A ∪ B : Finset U) : Set U)).Copy G,
      (∀ x : ↥A, h ⟨x.val, Finset.mem_union_left B x.property⟩ = f x) ∧
      (∀ y : ↥B, h ⟨y.val, Finset.mem_union_right A y.property⟩ = g y) := by
  classical
  let φ : ↥(A ∪ B : Finset U) → V := fun x ↦ if hx : x.val ∈ A then f ⟨x.val, hx⟩
    else g ⟨x.val, (Finset.mem_union.mp x.property).resolve_left hx⟩
  have hleft (x : ↥(A ∪ B : Finset U)) (hx : x.val ∈ A) : φ x = f ⟨x.val, hx⟩ := by
    simp only [φ, dif_pos hx]
  have hright (x : ↥(A ∪ B : Finset U)) (hx : x.val ∉ A) :
      φ x = g ⟨x.val, (Finset.mem_union.mp x.property).resolve_left hx⟩ := by
    simp only [φ, dif_neg hx]
  have hmap {x y : ↥(A ∪ B : Finset U)} (hxy : T.Adj x.val y.val) : G.Adj (φ x) (φ y) := by
    by_cases hx : x.val ∈ A <;> by_cases hy : y.val ∈ A
    · rw [hleft x hx, hleft y hy]
      exact f.toHom.map_adj hxy
    · rw [hleft x hx, hright y hy]
      exact hcross _ _ hxy
    · rw [hright x hx, hleft y hy]
      exact (hcross _ _ hxy.symm).symm
    · rw [hright x hx, hright y hy]
      exact g.toHom.map_adj hxy
  have hinj : Function.Injective φ := by
    intro x y he
    by_cases hx : x.val ∈ A <;> by_cases hy : y.val ∈ A
    · rw [hleft x hx, hleft y hy] at he
      exact Subtype.ext (congrArg (fun z : ↥A ↦ z.val) (f.injective he))
    · rw [hleft x hx, hright y hy] at he
      exact (himages _ _ he).elim
    · rw [hright x hx, hleft y hy] at he
      exact (himages _ _ he.symm).elim
    · rw [hright x hx, hright y hy] at he
      exact Subtype.ext (congrArg (fun z : ↥B ↦ z.val) (g.injective he))
  refine ⟨{
    toHom := { toFun := φ, map_rel' := hmap }
    injective' := hinj
  }, ?_, ?_⟩
  · intro x
    exact hleft _ x.property
  · intro y
    exact hright _ (fun hy ↦ Finset.disjoint_left.mp hAB hy y.property)

end Erdos547

#print axioms Erdos547.glue_copies
