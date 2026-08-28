import Wikipedia.HopfProblem.OrbitPairSubdivisionNativeMesh

/-!
# Native subdivision preserves the standard simplex dimension bound

A strictly increasing chain of nonempty subsets of `n + 1` vertices has
at most `n + 1` terms. Applying this to nondegenerate nerve simplices gives
the native dimension bound used to keep a uniform contraction factor under
further subdivision.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

theorem strictChain_dimension_le {n k : ℕ}
    (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (hA : StrictMono A) : k ≤ n := by
  have hc : ∀ j, (A j).finset.card ≤ n + 1 := by
    intro j
    simpa using Finset.card_le_univ (A j).finset
  have hs : StrictMono (fun j ↦ (A j).finset.card) := fun i j hij ↦
    Finset.card_lt_card (hA hij)
  let e : Fin (k + 1) → Fin (n + 1) := fun j ↦
    ⟨(A j).finset.card - 1, by
      have hp := (A j).nonempty.card_pos
      have hj := hc j
      omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply hs.injective
    change (A i).finset.card = (A j).finset.card
    have h := congrArg Fin.val hij
    change (A i).finset.card - 1 = (A j).finset.card - 1 at h
    have hi := (A i).nonempty.card_pos
    have hj := (A j).nonempty.card_pos
    omega
  have h := Fintype.card_le_of_injective e he
  simpa using h

theorem nonDegenerate_simplex_dim_le (n k : ℕ)
    (x : (SimplexCategory.sd.{u}.obj ⦋n⦌).nonDegenerate k) : k ≤ n := by
  apply strictChain_dimension_le (fun j ↦ x.val.obj j)
  exact (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
    (X := NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) x.val).mp x.property

instance subdividedSimplexDimensionLE (n : ℕ) :
    (SimplexCategory.sd.{u}.obj ⦋n⦌).HasDimensionLE n where
  degenerate_eq_top k hk := by
    apply Set.eq_univ_of_forall
    intro x
    rw [(SimplexCategory.sd.obj ⦋n⦌).mem_degenerate_iff_notMem_nonDegenerate]
    intro hx
    have h := nonDegenerate_simplex_dim_le n k ⟨x, hx⟩
    omega

instance stdSimplexSubdivisionDimensionLE (n : ℕ) :
    (SSet.sd.obj (SSet.stdSimplex.{u}.obj ⦋n⦌)).HasDimensionLE n := by
  change SSet.HasDimensionLT ((SSet.stdSimplex.{u} ⋙ SSet.sd).obj ⦋n⦌) (n + 1)
  exact SSet.hasDimensionLT_of_mono (SSet.stdSimplex.sdIso.{u}.hom.app ⦋n⦌) (n + 1)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
