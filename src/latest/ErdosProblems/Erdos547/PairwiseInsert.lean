import ErdosProblems.Erdos547.Attachment

/-!
# Preserving pairwise constraints when a vertex is inserted
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem pairwise_property_insert {U V : Type*} (P : SimpleGraph U)
    (compatible : V → V → Prop) (hsymm : ∀ ⦃a b⦄, compatible a b → compatible b a)
    (Q : Finset U) (v : U) (f : ↑(Q : Set U) → V)
    (f' : ↑(↑(insert v Q) : Set U) → V) (z : V)
    (hf : ∀ x y : (Q : Set U), P.Adj x.val y.val → compatible (f x) (f y))
    (hnew : f' ⟨v, Finset.mem_insert_self _ _⟩ = z)
    (hold : ∀ x : (Q : Set U), f' ⟨x.val, Finset.mem_insert_of_mem x.property⟩ = f x)
    (hcompat : ∀ x : (Q : Set U), P.Adj v x.val → compatible z (f x)) :
    ∀ x y : (↑(insert v Q) : Set U), P.Adj x.val y.val → compatible (f' x) (f' y) := by
  classical
  intro x y hxy
  rcases Finset.mem_insert.mp x.property with hx | hx
  · have hxeq : x = ⟨v, Finset.mem_insert_self _ _⟩ := Subtype.ext hx
    rcases Finset.mem_insert.mp y.property with hy | hy
    · have hloop : P.Adj v v := by simpa only [hx, hy] using hxy
      exact (P.loopless.irrefl v hloop).elim
    · have hyeq : y = ⟨y.val, Finset.mem_insert_of_mem hy⟩ := rfl
      rw [hxeq, hnew, hyeq, hold ⟨y.val, hy⟩]
      exact hcompat ⟨y.val, hy⟩ (by simpa only [hx] using hxy)
  · have hxeq : x = ⟨x.val, Finset.mem_insert_of_mem hx⟩ := rfl
    rcases Finset.mem_insert.mp y.property with hy | hy
    · have hyeq : y = ⟨v, Finset.mem_insert_self _ _⟩ := Subtype.ext hy
      rw [hxeq, hold ⟨x.val, hx⟩, hyeq, hnew]
      exact hsymm (hcompat ⟨x.val, hx⟩ (by simpa only [hy] using hxy.symm))
    · have hyeq : y = ⟨y.val, Finset.mem_insert_of_mem hy⟩ := rfl
      rw [hxeq, hold ⟨x.val, hx⟩, hyeq, hold ⟨y.val, hy⟩]
      exact hf ⟨x.val, hx⟩ ⟨y.val, hy⟩ hxy

end Erdos547

#print axioms Erdos547.pairwise_property_insert
