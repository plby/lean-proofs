import ErdosProblems.Erdos593.Graph.RainbowBipartite

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Positive-size rainbow bipartite submatrices

This small wrapper records that the finite host size supplied by the rainbow
bipartite submatrix lemma is nonzero whenever the requested submatrix has
positive size.  The proof deliberately uses only the public extraction
property, rather than the particular construction of the host size.
-/

namespace Erdos593
namespace RainbowBipartite

universe u

/-- For positive `n` and `t`, the rainbow bipartite submatrix lemma can be
instantiated with a positive finite host size. -/
theorem exists_pos_rainbow_bipartite_submatrix (n t : Nat) (hn : 0 < n) (ht : 0 < t) :
    ∃ q : Nat, 0 < q ∧
      ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
        LocallyBounded t color →
          ∃ (left : Fin n ↪ Fin q) (right : Fin n ↪ Fin q),
            IsRainbow color left right := by
  obtain ⟨q, hextract⟩ := exists_rainbow_bipartite_submatrix n t hn ht
  refine ⟨q, ?_, hextract⟩
  by_contra hq
  have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq
  subst q
  let color : Fin 0 → Fin 0 → PUnit := fun x _ => Fin.elim0 x
  have hlocal : LocallyBounded t color := by
    constructor <;> intro x <;> exact Fin.elim0 x
  obtain ⟨left, _, _⟩ := hextract PUnit color hlocal
  exact Fin.elim0 (left ⟨0, hn⟩)

end RainbowBipartite
end Erdos593
