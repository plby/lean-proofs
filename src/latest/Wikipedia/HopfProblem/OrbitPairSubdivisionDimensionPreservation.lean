import Wikipedia.HopfProblem.OrbitPairSubdivisionFinite

/-!
# Native subdivision preserves dimension bounds

Every nondegenerate subdivided simplex comes from a nondegenerate
original carrier and a nondegenerate simplex of its standard subdivision
cell. A decreasing chain has the same dimension bound as an increasing
one after reversing its indices. These bounds pass to the native left
Kan extensions.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

theorem dual_nonDegenerate_simplex_dim_le (n k : ℕ)
    (x : (dualStandard.{u}.obj ⦋n⦌).nonDegenerate k) : k ≤ n := by
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono x.val).mp x.property
  apply strictChain_dimension_le (fun j ↦ x.val.obj j.rev)
  intro i j hij
  exact hs (Fin.rev_lt_rev.mpr hij)

instance dualStandardDimensionLE (n : ℕ) : (dualStandard.{u}.obj ⦋n⦌).HasDimensionLE n where
  degenerate_eq_top k hk := by
    apply Set.eq_univ_of_forall
    intro x
    rw [(dualStandard.obj ⦋n⦌).mem_degenerate_iff_notMem_nonDegenerate]
    intro hx
    have h := dual_nonDegenerate_simplex_dim_le n k ⟨x, hx⟩
    omega

end Wikipedia.HopfProblem.OrbitPair.Subdivision

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionColimit

variable (A : SimplexCategory ⥤ SSet.{u}) (L : SSet.{u} ⥤ SSet.{u})
    (α : A ⟶ SSet.stdSimplex.{u} ⋙ L) (X : SSet.{u})
    [SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension A] [L.IsLeftKanExtension α]

include α in
theorem dimension_of_standard_cells (d : ℕ) [X.HasDimensionLT d]
    (hA : ∀ n : ℕ, (A.obj ⦋n⦌).HasDimensionLE n) : (L.obj X).HasDimensionLT d where
  degenerate_eq_top k hk := by
    apply Set.eq_univ_of_forall
    intro z
    rw [(L.obj X).mem_degenerate_iff_notMem_nonDegenerate]
    intro hz
    obtain ⟨a, t, ht⟩ := exists_nondegenerate_cell A L α X k z
    have htnd : t ∈ (A.obj ⦋a.dim⦌).nonDegenerate k := by
      intro hdeg
      exact hz (ht ▸ SSet.degenerate_app_apply hdeg (cellMap A L α X a.dim a.simplex))
    let : (A.obj ⦋a.dim⦌).HasDimensionLE a.dim := hA a.dim
    have hka : k ≤ a.dim := (A.obj ⦋a.dim⦌).dim_le_of_nonDegenerate ⟨t, htnd⟩ a.dim
    have had : a.dim < d := X.dim_lt_of_nonDegenerate ⟨a.simplex, a.nonDegenerate⟩ d
    omega

end Wikipedia.HopfProblem.OrbitPair.SubdivisionColimit

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

instance sd_hasDimensionLT (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] :
    (SSet.sd.obj X).HasDimensionLT d := by
  let : SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension SimplexCategory.sd.{u} :=
    inferInstanceAs (Functor.HasPointwiseLeftKanExtension uliftYoneda.{u} SimplexCategory.sd.{u})
  exact SubdivisionColimit.dimension_of_standard_cells SimplexCategory.sd SSet.sd
    SSet.stdSimplex.sdIso.inv X d (fun n ↦ subdividedSimplexDimensionLE n)

instance dualSd_hasDimensionLT (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] :
    (dualSd.obj X).HasDimensionLT d :=
  SubdivisionColimit.dimension_of_standard_cells dualStandard dualSd dualSdIso.inv X d
    (fun n ↦ dualStandardDimensionLE n)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
