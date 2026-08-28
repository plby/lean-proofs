import Wikipedia.HopfProblem.ThreefoldHomologyBoundaryFirst
import Wikipedia.HopfProblem.ThreefoldHomologyFreeProducts
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessPieces
import Wikipedia.HopfProblem.ThreefoldHomologyStar

/-!
# The actual degree-one attachment is an isomorphism

The three original overlaps have free integral first homology of rank
three, proved from their genuine Wang sequences.  The actual regular
piece has rank three and the three fillings each have rank two.  Thus
both sides of the literal signed attachment map are free of rank nine.
Its already proved surjectivity, which uses the actual simple
connectedness of the threefold, therefore implies bijectivity over `ℤ`.

No coordinate matrix for this attachment map is assumed or substituted.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

open SingularMayerVietoris ThreefoldHomologyFreeProducts

theorem puncture_card : Fintype.card Puncture = 3 := by decide

theorem overlapFirst_free : Module.Free ℤ (StarOverlapHomology 1) := by
  have : ∀ i : Puncture, Module.Free ℤ (SingularHomology (RegularOverlap i) 1) :=
    BoundaryFirst.overlapH1_free
  exact free_pi_int (fun i : Puncture => SingularHomology (RegularOverlap i) 1)

theorem overlapFirst_finrank : Module.finrank ℤ (StarOverlapHomology 1) = 9 := by
  have : ∀ i : Puncture, Module.Free ℤ (SingularHomology (RegularOverlap i) 1) :=
    BoundaryFirst.overlapH1_free
  have : ∀ i : Puncture, Module.Finite ℤ (SingularHomology (RegularOverlap i) 1) :=
    BoundaryFirst.overlapH1_finite
  rw [finrank_pi_int (fun i : Puncture => SingularHomology (RegularOverlap i) 1)]
  simp only [BoundaryFirst.overlapH1_finrank, Finset.sum_const, Finset.card_univ,
    puncture_card]
  decide

theorem fillingFirst_free (i : Puncture) :
    Module.Free ℤ (SingularHomology (localPiece (some i)) 1) := by
  cases i with
  | none => exact Finiteness.cuspPieceHomology_free 1
  | some j => exact Finiteness.ellipticPieceHomology_free j 1

theorem fillingFirst_finrank (i : Puncture) :
    Module.finrank ℤ (SingularHomology (localPiece (some i)) 1) = 2 := by
  cases i with
  | none => exact Finiteness.cuspPieceHomology_finrank 1
  | some j => exact Finiteness.ellipticPieceHomology_finrank j 1

theorem fillingsFirst_free : Module.Free ℤ (StarFillingHomology 1) := by
  have : ∀ i : Puncture, Module.Free ℤ (SingularHomology (localPiece (some i)) 1) :=
    fillingFirst_free
  exact free_pi_int (fun i : Puncture => SingularHomology (localPiece (some i)) 1)

theorem fillingsFirst_finrank : Module.finrank ℤ (StarFillingHomology 1) = 6 := by
  have : ∀ i : Puncture, Module.Free ℤ (SingularHomology (localPiece (some i)) 1) :=
    fillingFirst_free
  have : ∀ i : Puncture, Module.Finite ℤ (SingularHomology (localPiece (some i)) 1) :=
    fun i => Finiteness.fillingHomology_finite i 1
  rw [finrank_pi_int (fun i : Puncture => SingularHomology (localPiece (some i)) 1)]
  simp only [fillingFirst_finrank, Finset.sum_const, Finset.card_univ, puncture_card]
  decide

theorem pairFirst_free : Module.Free ℤ (StarPairHomology 1) := by
  have := Finiteness.regularHomology_free 1
  have := fillingsFirst_free
  exact free_prod_int (SingularHomology SpecialRegularFamily 1) (StarFillingHomology 1)

theorem pairFirst_finrank : Module.finrank ℤ (StarPairHomology 1) = 9 := by
  have := Finiteness.regularHomology_free 1
  have := Finiteness.regularHomology_finite 1
  have := fillingsFirst_free
  have := Finiteness.starFillingHomology_finite 1
  rw [finrank_prod_int (SingularHomology SpecialRegularFamily 1) (StarFillingHomology 1),
    Finiteness.regularHomology_finrank, fillingsFirst_finrank]
  rfl

/-- The original degree-one attachment is bijective over the integers. -/
theorem starLeft_one_bijective : Function.Bijective (starLeftHomologyMap 1) := by
  have := overlapFirst_free
  have := pairFirst_free
  have := Finiteness.starOverlapHomology_finite 1
  have := Finiteness.starPairHomology_finite 1
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (starLeftHomologyMap 1) starLeftHomologyMap_one_surjective
  rw [overlapFirst_finrank, pairFirst_finrank]

/-- This isomorphism retains the literal original signed attachment map. -/
def starLeftOneEquiv : StarOverlapHomology 1 ≃ₗ[ℤ] StarPairHomology 1 :=
  LinearEquiv.ofBijective (starLeftHomologyMap 1) starLeft_one_bijective

@[simp] theorem starLeftOneEquiv_toLinearMap :
    starLeftOneEquiv.toLinearMap = starLeftHomologyMap 1 := rfl

@[simp] theorem starLeftOneEquiv_apply (a : StarOverlapHomology 1) :
    starLeftOneEquiv a = starLeftHomologyMap 1 a := rfl

theorem starLeft_one_kernel_eq_bot : LinearMap.ker (starLeftHomologyMap 1) = ⊥ :=
  LinearMap.ker_eq_bot.mpr starLeft_one_bijective.injective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree
