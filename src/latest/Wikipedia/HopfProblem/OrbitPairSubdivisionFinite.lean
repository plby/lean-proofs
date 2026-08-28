import Wikipedia.HopfProblem.OrbitPairDualGeneratedContractible
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

/-!
# Finite simplicial sets have finite native subdivisions

The cells indexed by nondegenerate original simplices cover the actual
left Kan extension. For a finite original simplicial set this is a finite
union of images of standard cells. If those standard cells are finite,
the actual functor value is finite as well.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionColimit

open SubdivisionParameters

variable (A : SimplexCategory ⥤ SSet.{u}) (L : SSet.{u} ⥤ SSet.{u})
    (α : A ⟶ SSet.stdSimplex.{u} ⋙ L) (X : SSet.{u})
    [SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension A] [L.IsLeftKanExtension α]

theorem exists_nondegenerate_cell (k : ℕ) (z : (L.obj X) _⦋k⦌) :
    ∃ a : X.N, ∃ t : (A.obj ⦋a.dim⦌) _⦋k⦌,
      (cellMap A L α X a.dim a.simplex).app (Opposite.op ⦋k⦌) t = z := by
  obtain ⟨n, x, t, ht⟩ := exists_cell A L α X k z
  let c := RealizationSimplex.core X n x
  refine ⟨SSet.N.mk c.simplex.val c.simplex.property,
    (A.map c.collapse).app (Opposite.op ⦋k⦌) t, ?_⟩
  exact (coreParameters_projection A X k L α n x t).trans ht

theorem nondegenerate_cells_cover :
    (⨆ a : X.N, SSet.Subcomplex.range (cellMap A L α X a.dim a.simplex)) = ⊤ := by
  ext d z
  obtain ⟨⟨k⟩⟩ := d
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion, Set.mem_range,
    Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact exists_nondegenerate_cell A L α X k z

include α in
theorem finite_of_standard_cells [X.Finite] (hA : ∀ n : ℕ, (A.obj ⦋n⦌).Finite) :
    (L.obj X).Finite := by
  rw [← SSet.finite_subcomplex_top_iff, ← nondegenerate_cells_cover A L α X,
    SSet.finite_iSup_iff]
  intro a
  let : (A.obj ⦋a.dim⦌).Finite := hA a.dim
  infer_instance

end Wikipedia.HopfProblem.OrbitPair.SubdivisionColimit

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

instance standard_finite (n : ℕ) : (SimplexCategory.sd.{u}.obj ⦋n⦌).Finite :=
  inferInstanceAs (SSet.Finite (nerve (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))))

instance dualStandard_finite (n : ℕ) : (dualStandard.{u}.obj ⦋n⦌).Finite :=
  inferInstanceAs
    (SSet.Finite (nerve (OrderDual (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))))))

instance sd_finite (X : SSet.{u}) [X.Finite] : (SSet.sd.obj X).Finite := by
  let : SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension SimplexCategory.sd.{u} :=
    inferInstanceAs (Functor.HasPointwiseLeftKanExtension uliftYoneda.{u} SimplexCategory.sd.{u})
  exact SubdivisionColimit.finite_of_standard_cells SimplexCategory.sd SSet.sd
    SSet.stdSimplex.sdIso.inv X (fun n ↦ standard_finite n)

instance dualSd_finite (X : SSet.{u}) [X.Finite] : (dualSd.obj X).Finite :=
  SubdivisionColimit.finite_of_standard_cells dualStandard dualSd dualSdIso.inv X
    (fun n ↦ dualStandard_finite n)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
