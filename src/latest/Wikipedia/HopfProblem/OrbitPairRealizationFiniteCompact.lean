import Wikipedia.HopfProblem.OrbitPairRealizationNondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.Order.NonemptyFiniteChains
import Mathlib.Data.Fintype.Powerset

/-!
# Compactness of native finite realizations and finite-poset nerves

A finite realization is a finite union of compact characteristic-simplex
images. The nerve of a finite poset is finite because a nondegenerate
simplex has pairwise distinct vertices. These facts apply in particular to
the native subdivided standard simplex.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

instance realizationCompactSpace (S : SSet.{u}) [SSet.Finite S] :
    CompactSpace (SSet.toTop.obj S) := by
  let K : S.N → Set (SSet.toTop.obj S) :=
    fun a ↦ Set.range (characteristic S a.dim a.simplex)
  have hK : IsCompact (⋃ a, K a) :=
    isCompact_iUnion (fun a ↦ isCompact_range (characteristic S a.dim a.simplex).continuous)
  have he : (⋃ a, K a) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n, x, t, ht, rfl⟩ := exists_positive_nonDegenerate S z
    exact Set.mem_iUnion.mpr ⟨SSet.N.mk x.val x.property, t, rfl⟩
  exact ⟨he ▸ hK⟩

instance finiteNonemptyChains (P : Type u) [PartialOrder P] [Finite P] :
    Finite (NonemptyFiniteChains P) := by
  let : Fintype P := Fintype.ofFinite P
  exact Finite.of_injective (fun A : NonemptyFiniteChains P ↦ A.finset)
    (fun A B h ↦ NonemptyFiniteChains.ext h)

instance finitePosetNerve (P : Type u) [PartialOrder P] [Finite P] : SSet.Finite (nerve P) := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : (nerve P).HasDimensionLT (Fintype.card P) :=
    { degenerate_eq_top := fun d hd ↦ by
        apply Set.eq_univ_of_forall
        intro x
        rw [(nerve P).mem_degenerate_iff_notMem_nonDegenerate]
        intro hx
        have hi := (PartialOrder.mem_nerve_nonDegenerate_iff_injective x).mp hx
        have hc := Fintype.card_le_of_injective x.obj hi
        simp only [Fintype.card_fin] at hc
        omega }
  apply SSet.finite_of_hasDimensionLT (nerve P) (Fintype.card P)
  intro d hd
  exact Finite.of_injective (fun x : (nerve P).nonDegenerate d ↦ x.val.obj)
    (fun x y h ↦ Subtype.ext (nerve.ext_of_isThin h))

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
