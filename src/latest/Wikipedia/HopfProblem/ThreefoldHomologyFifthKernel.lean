import Wikipedia.HopfProblem.ThreefoldHomologyTopDegree

/-!
# The actual fifth homology is the fourth attachment kernel

The two proved elliptic columns make the genuine fifth attachment map
surjective.  The next actual inclusion map is consequently zero.  Thus
the genuine connecting homomorphism identifies fifth homology of the
original threefold with the kernel of its actual fourth attachment map.

This is a proved reduction, not a claim that the still unevaluated fourth
attachment kernel vanishes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

open SingularMayerVietoris TopDegree Finiteness ThreefoldHomologyTopDegreeAlgebra

/-- The original regular fifth-homology term is covered by the genuine boundaries. -/
theorem regularAttachment_five_surjective :
    Function.Surjective (starOverlapToRegularHomologyMap 5) := by
  have hs := surjective_of_columnIso groupedAttachmentFifth
    (singularHomologyMap (overlapToRegularFamily none) 5)
    ellipticAttachmentFifthEquiv groupedAttachmentFifth_columnIso
  intro a
  obtain ⟨b, hb⟩ := hs a
  exact ⟨groupedOverlapFifthEquiv.symm b, hb⟩

/-- Every actual degree-five signed star class comes from an actual overlap class. -/
theorem starLeft_five_surjective : Function.Surjective (starLeftHomologyMap 5) := by
  have := starFillingHomology_subsingleton (by decide : 4 < 5)
  intro a
  obtain ⟨b, hb⟩ := regularAttachment_five_surjective a.1
  refine ⟨b, ?_⟩
  apply Prod.ext
  · exact hb
  · exact Subsingleton.elim _ _

/-- The actual sum of piece inclusions is zero in degree five, by exactness. -/
theorem starRight_five_eq_zero : starRightHomologyMap 5 = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := starLeft_five_surjective a
  exact (star_exact_at_pair 5).apply_apply_eq_zero b

/-- No fifth global class is lost by the actual connecting homomorphism. -/
theorem connecting_four_injective : Function.Injective (starConnectingHomomorphism 4) := by
  intro a b hab
  have hz : starConnectingHomomorphism 4 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (star_exact_at_ambient 4 (a - b)).mp hz
  rw [starRight_five_eq_zero, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc.symm

/-- The native connecting map with its proved actual kernel codomain. -/
def connectingIntoKernel :
    SingularHomology Space 5 →ₗ[ℤ] LinearMap.ker (starLeftHomologyMap 4) :=
  (starConnectingHomomorphism 4).codRestrict (LinearMap.ker (starLeftHomologyMap 4))
    (fun a => (star_exact_at_intersection 4).apply_apply_eq_zero a)

theorem connectingIntoKernel_bijective : Function.Bijective connectingIntoKernel := by
  constructor
  · intro a b hab
    exact connecting_four_injective (congrArg Subtype.val hab)
  · intro a
    obtain ⟨b, hb⟩ := (star_exact_at_intersection 4 a.val).mp a.property
    exact ⟨b, Subtype.ext hb⟩

/-- The actual fifth integral homology is the actual fourth attachment kernel. -/
def homologyFiveKernelEquiv :
    SingularHomology Space 5 ≃ₗ[ℤ] LinearMap.ker (starLeftHomologyMap 4) :=
  LinearEquiv.ofBijective connectingIntoKernel connectingIntoKernel_bijective

@[simp] theorem homologyFiveKernelEquiv_val (a : SingularHomology Space 5) :
    (homologyFiveKernelEquiv a : StarOverlapHomology 4) = starConnectingHomomorphism 4 a := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree
