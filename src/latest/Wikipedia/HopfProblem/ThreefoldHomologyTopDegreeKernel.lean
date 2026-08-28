import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessGlobal

/-!
# The actual sixth homology as the kernel of the degree-five attachments

All original star-cover pieces have zero sixth homology, so the genuine
connecting homomorphism is injective in degree six.  Its image is the
kernel of the literal signed attachment map.  Since the original three
fillings have zero fifth homology, that kernel is exactly the kernel of
the sum of the actual three overlap maps into the regular family.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree

open SingularMayerVietoris Finiteness

/-- The genuine top connecting map is injective because its actual
incoming term vanishes. -/
theorem connecting_five_injective : Function.Injective (starConnectingHomomorphism 5) := by
  have := starPairHomology_subsingleton (by decide : 5 < 6)
  intro a b hab
  have hz : starConnectingHomomorphism 5 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (star_exact_at_ambient 5 (a - b)).mp hz
  have hc₀ : c = 0 := Subsingleton.elim _ _
  rw [hc₀, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

/-- The actual connecting map, with its proved image in the actual kernel. -/
def connectingIntoKernel :
    SingularHomology Space 6 →ₗ[ℤ] LinearMap.ker (starLeftHomologyMap 5) :=
  (starConnectingHomomorphism 5).codRestrict (LinearMap.ker (starLeftHomologyMap 5))
    (fun a => (star_exact_at_intersection 5).apply_apply_eq_zero a)

@[simp] theorem connectingIntoKernel_val (a : SingularHomology Space 6) :
    (connectingIntoKernel a : StarOverlapHomology 5) = starConnectingHomomorphism 5 a := rfl

theorem connectingIntoKernel_bijective : Function.Bijective connectingIntoKernel := by
  constructor
  · intro a b hab
    exact connecting_five_injective (congrArg Subtype.val hab)
  · intro a
    obtain ⟨b, hb⟩ := (star_exact_at_intersection 5 a.val).mp a.property
    exact ⟨b, Subtype.ext hb⟩

/-- Sixth singular homology of the original threefold, identified by the
genuine connecting homomorphism with its literal attachment kernel. -/
def homologySixKernelEquiv :
    SingularHomology Space 6 ≃ₗ[ℤ] LinearMap.ker (starLeftHomologyMap 5) :=
  LinearEquiv.ofBijective connectingIntoKernel connectingIntoKernel_bijective

@[simp] theorem homologySixKernelEquiv_val (a : SingularHomology Space 6) :
    (homologySixKernelEquiv a : StarOverlapHomology 5) = starConnectingHomomorphism 5 a := rfl

/-- In degree five the filling components vanish, but the original
regular component of the signed star map is retained exactly. -/
theorem starLeft_five_eq_zero_iff (a : StarOverlapHomology 5) :
    starLeftHomologyMap 5 a = 0 ↔ starOverlapToRegularHomologyMap 5 a = 0 := by
  have := starFillingHomology_subsingleton (by decide : 4 < 5)
  change (starOverlapToRegularHomologyMap 5 a,
    -starOverlapToFillingsHomologyMap 5 a) = (0, 0) ↔ _
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    exact Prod.ext h (Subsingleton.elim _ _)

/-- Removing the proved-zero filling component changes no overlap class. -/
def attachmentKernelEquiv :
    LinearMap.ker (starLeftHomologyMap 5) ≃ₗ[ℤ]
      LinearMap.ker (starOverlapToRegularHomologyMap 5) where
  toFun a := ⟨a.val, (starLeft_five_eq_zero_iff a.val).mp a.property⟩
  invFun a := ⟨a.val, (starLeft_five_eq_zero_iff a.val).mpr a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- This top-degree reduction uses only original maps and established
piece vanishing, not Poincaré duality or an assumed boundary matrix. -/
def homologySixRegularKernelEquiv :
    SingularHomology Space 6 ≃ₗ[ℤ]
      LinearMap.ker (starOverlapToRegularHomologyMap 5) :=
  homologySixKernelEquiv.trans attachmentKernelEquiv

@[simp] theorem homologySixRegularKernelEquiv_val (a : SingularHomology Space 6) :
    (homologySixRegularKernelEquiv a : StarOverlapHomology 5) =
      starConnectingHomomorphism 5 a := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree
