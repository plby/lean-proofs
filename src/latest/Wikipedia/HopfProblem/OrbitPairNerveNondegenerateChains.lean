import Wikipedia.HopfProblem.OrbitPairNondegeneratePosetFunctor

/-!
# Native nondegenerate nerve simplices are nonempty finite chains

This is an order isomorphism for every partially ordered type. The order
on nondegenerate simplices is the native generated-subcomplex order.
The proof factors a monotone sequence through an injective monotone
sequence whenever its vertex range is contained in the latter's range.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset

open FinitePoset

variable (P : Type u) [PartialOrder P]

def nerveVertices (x : (nerve P).N) : NonemptyFiniteChains P :=
  simplexVertexChain P x.dim x.simplex

theorem mem_nerveVertices (x : (nerve P).N) (p : P) :
    p ∈ (nerveVertices P x).finset ↔ ∃ i : Fin (x.dim + 1), x.simplex.obj i = p := by
  classical
  simp [nerveVertices, simplexVertexChain]

theorem nerveVertices_le_iff (x y : (nerve P).N) :
    nerveVertices P x ≤ nerveVertices P y ↔ x ≤ y := by
  classical
  constructor
  · intro h
    have hs : ∀ i : Fin (x.dim + 1), ∃ j : Fin (y.dim + 1),
        y.simplex.obj j = x.simplex.obj i := by
      intro i
      exact (mem_nerveVertices P y _).mp (h ((mem_nerveVertices P x _).mpr ⟨i, rfl⟩))
    choose g hg using hs
    have hy := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono y.simplex).mp y.nonDegenerate
    let f : Fin (x.dim + 1) →o Fin (y.dim + 1) :=
      { toFun := g
        monotone' := fun i j hij ↦ hy.le_iff_le.mp (by rw [hg i, hg j]; exact x.simplex.monotone hij) }
    change x.toS ≤ y.toS
    refine SSet.S.le_iff.mpr ⟨SimplexCategory.Hom.mk f, ?_⟩
    apply nerve.ext_of_isThin
    exact funext hg
  · intro h
    obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.mp h
    intro p hp
    obtain ⟨i, rfl⟩ := (mem_nerveVertices P x p).mp hp
    refine (mem_nerveVertices P y _).mpr ⟨f.toOrderHom i, ?_⟩
    exact congrArg (fun a : (nerve P) _⦋x.dim⦌ ↦ a.obj i) he

theorem nerveVertices_injective : Function.Injective (nerveVertices P) := by
  intro x y h
  exact le_antisymm ((nerveVertices_le_iff P x y).mp h.le)
    ((nerveVertices_le_iff P y x).mp h.symm.le)

def chainNondegenerate (A : NonemptyFiniteChains P) : (nerve P).N :=
  SSet.N.mk (chainSimplex A) (chainSimplex_nonDegenerate A)

theorem nerveVertices_chainNondegenerate (A : NonemptyFiniteChains P) :
    nerveVertices P (chainNondegenerate P A) = A := by
  classical
  apply NonemptyFiniteChains.ext
  ext p
  rw [mem_nerveVertices]
  change (p ∈ Set.range (chainVertices A)) ↔ p ∈ (A.finset : Set P)
  rw [chainVertices_range]

def nerveChainsOrderIso : (nerve P).N ≃o NonemptyFiniteChains P where
  toFun := nerveVertices P
  invFun := chainNondegenerate P
  left_inv x := nerveVertices_injective P (nerveVertices_chainNondegenerate P (nerveVertices P x))
  right_inv := nerveVertices_chainNondegenerate P
  map_rel_iff' := nerveVertices_le_iff P _ _

end Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset
