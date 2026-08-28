import Wikipedia.HopfProblem.OrbitPairNerveNondegenerateChains

/-!
# Naturality of native face chains, including collapsed vertices

Passing to the nondegenerate core preserves the vertex range of a nerve
simplex, since its degeneracy operator is surjective. The order isomorphism
with finite chains therefore commutes with every monotone map, without an
injectivity assumption.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset

variable (P : Type u) [PartialOrder P]

theorem toN_vertex_range (x : (nerve P).S) :
    Set.range x.toN.simplex.obj = Set.range x.simplex.obj := by
  have hs : Function.Surjective x.toNπ.toOrderHom :=
    SimplexCategory.epi_iff_surjective.mp inferInstance
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hs i
    refine ⟨j, ?_⟩
    have he := congrArg (fun a : (nerve P) _⦋x.dim⦌ ↦ a.obj j)
      (SSet.S.map_toNπ_op_apply x)
    exact he.symm.trans (congrArg x.toN.simplex.obj hj)
  · rintro ⟨j, rfl⟩
    exact ⟨x.toNπ.toOrderHom j, congrArg (fun a : (nerve P) _⦋x.dim⦌ ↦ a.obj j)
      (SSet.S.map_toNπ_op_apply x)⟩

theorem nerveVertices_map {Q : Type u} [PartialOrder Q] (f : P →o Q)
    (x : (nerve P).N) :
    nerveVertices Q (map (nerveMap f.monotone.functor) x) = (nerveVertices P x).map f := by
  classical
  apply NonemptyFiniteChains.ext
  ext q
  rw [mem_nerveVertices, NonemptyFiniteChains.mem_map_iff]
  change (q ∈ Set.range (x.toS.map (nerveMap f.monotone.functor)).toN.simplex.obj) ↔ _
  rw [toN_vertex_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨x.simplex.obj i, (mem_nerveVertices P x _).mpr ⟨i, rfl⟩, hi⟩
  · rintro ⟨p, hp, he⟩
    obtain ⟨i, rfl⟩ := (mem_nerveVertices P x p).mp hp
    exact ⟨i, he⟩

theorem chainNondegenerate_map {Q : Type u} [PartialOrder Q] (f : P →o Q)
    (A : NonemptyFiniteChains P) :
    map (nerveMap f.monotone.functor) (chainNondegenerate P A) =
      chainNondegenerate Q (A.map f) := by
  apply nerveVertices_injective Q
  rw [nerveVertices_map, nerveVertices_chainNondegenerate, nerveVertices_chainNondegenerate]

end Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset
