import Wikipedia.HopfProblem.OrbitPairFinitePosetCoordinates
import Mathlib.Order.Preorder.Chain

/-!
# An actual ordered simplex enumerating a finite chain

A nonempty finite chain in a partial order inherits a linear order. Its
increasing enumeration gives an actual nondegenerate simplex in the native
nerve, with precisely the original chain as vertex range.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

variable {P : Type u} [PartialOrder P]

theorem chain_isChain (A : NonemptyFiniteChains P) : IsChain (· ≤ ·) (A.finset : Set P) := by
  intro a ha b hb hab
  exact A.comparable ⟨a, ha⟩ ⟨b, hb⟩

def chainEnumeration (A : NonemptyFiniteChains P) :
    Fin (A.finset.card - 1 + 1) ≃o A.finset := by
  classical
  letI : LinearOrder A.finset := (chain_isChain A).linearOrder
  exact Fintype.orderIsoFinOfCardEq A.finset
    (by rw [Fintype.card_coe, Nat.sub_add_cancel A.nonempty.card_pos])

def chainVertices (A : NonemptyFiniteChains P) : Fin (A.finset.card - 1 + 1) →o P :=
  (OrderHom.Subtype.val _).comp (chainEnumeration A).toOrderEmbedding.toOrderHom

theorem chainVertices_injective (A : NonemptyFiniteChains P) :
    Function.Injective (chainVertices A) :=
  Subtype.val_injective.comp (chainEnumeration A).injective

theorem chainVertices_range (A : NonemptyFiniteChains P) :
    Set.range (chainVertices A) = (A.finset : Set P) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact (chainEnumeration A i).property
  · intro hp
    refine ⟨(chainEnumeration A).symm ⟨p, hp⟩, ?_⟩
    exact congrArg Subtype.val ((chainEnumeration A).apply_symm_apply ⟨p, hp⟩)

def chainSimplex (A : NonemptyFiniteChains P) : (nerve P) _⦋A.finset.card - 1⦌ :=
  (chainVertices A).monotone.functor

theorem chainSimplex_nonDegenerate (A : NonemptyFiniteChains P) :
    chainSimplex A ∈ (nerve P).nonDegenerate (A.finset.card - 1) :=
  (PartialOrder.mem_nerve_nonDegenerate_iff_injective (chainSimplex A)).mpr
    (chainVertices_injective A)

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
