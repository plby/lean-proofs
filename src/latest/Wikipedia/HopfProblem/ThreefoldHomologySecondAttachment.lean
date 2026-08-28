import Wikipedia.HopfProblem.ThreefoldHomologySecondAttachmentRanks
import Wikipedia.HopfProblem.ThreefoldHomologySecondVanishing

/-!
# The actual second attachment is an integral isomorphism

The original native cap-kernel relation map is onto between free integral
modules of rank six, hence injective.  The genuine cap-kernel transport
then detects every class in the kernel of the full signed second star
map.  Its bijectivity makes the next actual connecting map zero, giving
third homology as the cokernel of the unchanged third attachment map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

open SingularMayerVietoris CapElimination

/-- The original cap-kernel relation map is an integral isomorphism, without a chosen matrix. -/
theorem nativeCapKernelRegularMap_two_bijective :
    Function.Bijective (nativeCapKernelRegularMap 2) := by
  have := nativeCapKernelsTwo_free
  have := nativeCapKernelsTwo_finite
  have := Finiteness.regularHomology_free 2
  have := Finiteness.regularHomology_finite 2
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (nativeCapKernelRegularMap 2) nativeCapKernelRegularMap_two_surjective
  rw [nativeCapKernelsTwo_finrank, Finiteness.regularHomology_finrank]
  exact le_rfl

/-- The actual original signed second attachment has trivial integral kernel. -/
theorem starLeft_two_injective : Function.Injective (starLeftHomologyMap 2) := by
  intro a b hab
  have hz : starLeftHomologyMap 2 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hreg : starOverlapToRegularHomologyMap 2 (a - b) = 0 := congrArg Prod.fst hz
  have hcap : starOverlapToFillingsHomologyMap 2 (a - b) = 0 := by
    have h := congrArg Prod.snd hz
    change -starOverlapToFillingsHomologyMap 2 (a - b) = 0 at h
    exact neg_eq_zero.mp h
  let c : LinearMap.ker (starOverlapToFillingsHomologyMap 2) := ⟨a - b, hcap⟩
  have hc : nativeCapKernelRegularMap 2 (nativeCapKernelEquiv 2 c) = 0 :=
    (nativeCapKernelRegularMap_equiv 2 c).trans hreg
  have he : nativeCapKernelEquiv 2 c = 0 :=
    nativeCapKernelRegularMap_two_bijective.injective
      (hc.trans (nativeCapKernelRegularMap 2).map_zero.symm)
  have hc0 : c = 0 := (nativeCapKernelEquiv 2).injective
    (he.trans (nativeCapKernelEquiv 2).map_zero.symm)
  have hab0 : a - b = 0 := congrArg
    (fun x : LinearMap.ker (starOverlapToFillingsHomologyMap 2) => x.val) hc0
  exact sub_eq_zero.mp hab0

/-- Bijectivity concerns the literal original overlap-to-pieces map. -/
theorem starLeft_two_bijective : Function.Bijective (starLeftHomologyMap 2) :=
  ⟨starLeft_two_injective, starLeft_two_surjective⟩

/-- The original second attachment, bundled without replacing its forward map. -/
def starLeftSecondEquiv : StarOverlapHomology 2 ≃ₗ[ℤ] StarPairHomology 2 :=
  LinearEquiv.ofBijective (starLeftHomologyMap 2) starLeft_two_bijective

@[simp] theorem starLeftSecondEquiv_toLinearMap :
    starLeftSecondEquiv.toLinearMap = starLeftHomologyMap 2 := rfl

@[simp] theorem starLeftSecondEquiv_apply (a : StarOverlapHomology 2) :
    starLeftSecondEquiv a = starLeftHomologyMap 2 a := rfl

theorem starLeft_two_kernel_eq_bot : LinearMap.ker (starLeftHomologyMap 2) = ⊥ :=
  LinearMap.ker_eq_bot.mpr starLeft_two_injective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

open SingularMayerVietoris

/-- The original connecting map from global third homology vanishes. -/
theorem connecting_two_eq_zero : starConnectingHomomorphism 2 = 0 := by
  apply LinearMap.ext
  intro a
  change starConnectingHomomorphism 2 a = 0
  apply SecondDegree.starLeft_two_injective
  simpa only [map_zero] using (star_exact_at_intersection 2).apply_apply_eq_zero a

/-- Every actual third-homology class is a sum of original piece classes. -/
theorem starRight_three_surjective : Function.Surjective (starRightHomologyMap 3) := by
  intro a
  apply (star_exact_at_ambient 2 a).mp
  rw [connecting_two_eq_zero, LinearMap.zero_apply]

/-- The only relations are the actual signed third overlap images. -/
theorem starLeft_three_range_eq_ker :
    LinearMap.range (starLeftHomologyMap 3) = LinearMap.ker (starRightHomologyMap 3) :=
  (LinearMap.exact_iff.mp (star_exact_at_pair 3)).symm

/-- Quotient by the original third attachment map,
with the original inclusion sum as forward map. -/
def attachmentCokernelEquiv :
    (StarPairHomology 3 ⧸ LinearMap.range (starLeftHomologyMap 3)) ≃ₗ[ℤ]
      SingularHomology Space 3 :=
  ((Submodule.quotEquivOfEq _ _ starLeft_three_range_eq_ker).toAddEquiv.trans
    ((starRightHomologyMap 3).quotKerEquivOfSurjective
      starRight_three_surjective).toAddEquiv).toIntLinearEquiv

@[simp] theorem attachmentCokernelEquiv_mk (a : StarPairHomology 3) :
    attachmentCokernelEquiv (Submodule.Quotient.mk a) = starRightHomologyMap 3 a := rfl

/-- Actual global third homology is canonically the genuine third attachment cokernel. -/
def homologyThreeCokernelEquiv :
    SingularHomology Space 3 ≃ₗ[ℤ]
      (StarPairHomology 3 ⧸ LinearMap.range (starLeftHomologyMap 3)) :=
  attachmentCokernelEquiv.symm

@[simp] theorem homologyThreeCokernelEquiv_inclusion (a : StarPairHomology 3) :
    homologyThreeCokernelEquiv (starRightHomologyMap 3 a) = Submodule.Quotient.mk a :=
  attachmentCokernelEquiv.symm_apply_apply (Submodule.Quotient.mk a)

theorem starRight_three_eq_zero_iff (a : StarPairHomology 3) :
    starRightHomologyMap 3 a = 0 ↔
      ∃ b : StarOverlapHomology 3, starLeftHomologyMap 3 b = a :=
  star_exact_at_pair 3 a

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree
