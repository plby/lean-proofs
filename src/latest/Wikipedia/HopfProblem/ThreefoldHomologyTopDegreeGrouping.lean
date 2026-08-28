import Wikipedia.HopfProblem.ThreefoldHomologyTopDegreeKernel

/-!
# Grouping the original degree-five boundary maps

Separate the actual cusp overlap from the two actual elliptic overlaps.
The original sum map then has the literal form `cusp + elliptic`, with
neither column replaced by a chosen homology presentation.  The kernel
transport below changes coordinates only by this regrouping.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree

open SingularMayerVietoris

abbrev EllipticOverlapFifth :=
  ∀ j : Elliptic.Kind, SingularHomology (RegularOverlap (some j)) 5

/-- Regroup the original three overlaps without changing any component. -/
def groupedOverlapFifthEquiv : StarOverlapHomology 5 ≃ₗ[ℤ]
    (SingularHomology (RegularOverlap none) 5 × EllipticOverlapFifth) :=
  ({ Equiv.piOptionEquivProd with map_add' := fun _ _ => rfl } :
    StarOverlapHomology 5 ≃+
      (SingularHomology (RegularOverlap none) 5 × EllipticOverlapFifth)).toIntLinearEquiv

@[simp] theorem groupedOverlapFifthEquiv_apply (a : StarOverlapHomology 5) :
    groupedOverlapFifthEquiv a = (a none, fun j => a (some j)) := rfl

@[simp] theorem groupedOverlapFifthEquiv_symm_none
    (a : SingularHomology (RegularOverlap none) 5) (b : EllipticOverlapFifth) :
    groupedOverlapFifthEquiv.symm (a, b) none = a := rfl

@[simp] theorem groupedOverlapFifthEquiv_symm_some
    (a : SingularHomology (RegularOverlap none) 5) (b : EllipticOverlapFifth)
    (j : Elliptic.Kind) : groupedOverlapFifthEquiv.symm (a, b) (some j) = b j := rfl

/-- The sum of the two literal elliptic boundary inclusions. -/
def ellipticAttachmentFifth :
    EllipticOverlapFifth →ₗ[ℤ] SingularHomology SpecialRegularFamily 5 where
  toFun a := ∑ j : Elliptic.Kind,
    singularHomologyMap (overlapToRegularFamily (some j)) 5 (a j)
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, map_zsmul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact (int_smul_eq_zsmul ..).symm

@[simp] theorem ellipticAttachmentFifth_apply (a : EllipticOverlapFifth) :
    ellipticAttachmentFifth a = ∑ j : Elliptic.Kind,
      singularHomologyMap (overlapToRegularFamily (some j)) 5 (a j) := rfl

/-- The unchanged original sum map in the grouped source coordinates. -/
def groupedAttachmentFifth :
    (SingularHomology (RegularOverlap none) 5 × EllipticOverlapFifth) →ₗ[ℤ]
      SingularHomology SpecialRegularFamily 5 :=
  (starOverlapToRegularHomologyMap 5).comp groupedOverlapFifthEquiv.symm.toLinearMap

@[simp] theorem groupedAttachmentFifth_apply
    (a : SingularHomology (RegularOverlap none) 5) (b : EllipticOverlapFifth) :
    groupedAttachmentFifth (a, b) =
      singularHomologyMap (overlapToRegularFamily none) 5 a + ellipticAttachmentFifth b := by
  change (∑ i : Puncture, singularHomologyMap (overlapToRegularFamily i) 5
    (groupedOverlapFifthEquiv.symm (a, b) i)) = _
  rw [Fintype.sum_option]
  rfl

/-- The kernel coordinate change is the literal regrouping of boundary classes. -/
def groupedAttachmentKernelEquiv :
    LinearMap.ker (starOverlapToRegularHomologyMap 5) ≃ₗ[ℤ]
      LinearMap.ker groupedAttachmentFifth :=
  ({ toFun := fun a => ⟨groupedOverlapFifthEquiv a.val, by
       change starOverlapToRegularHomologyMap 5
         (groupedOverlapFifthEquiv.symm (groupedOverlapFifthEquiv a.val)) = 0
       rw [LinearEquiv.symm_apply_apply]
       exact a.property⟩
     invFun := fun a => ⟨groupedOverlapFifthEquiv.symm a.val, a.property⟩
     left_inv := fun a => Subtype.ext (LinearEquiv.symm_apply_apply _ a.val)
     right_inv := fun a => Subtype.ext (LinearEquiv.apply_symm_apply _ a.val)
     map_add' := fun a b => Subtype.ext (map_add groupedOverlapFifthEquiv a.val b.val) } :
    LinearMap.ker (starOverlapToRegularHomologyMap 5) ≃+
      LinearMap.ker groupedAttachmentFifth).toIntLinearEquiv

/-- The actual top homology is identified with the kernel of the unchanged
grouped map, retaining the genuine singular connecting homomorphism. -/
def homologySixGroupedKernelEquiv :
    SingularHomology Space 6 ≃ₗ[ℤ] LinearMap.ker groupedAttachmentFifth :=
  homologySixRegularKernelEquiv.trans groupedAttachmentKernelEquiv

@[simp] theorem homologySixGroupedKernelEquiv_val (a : SingularHomology Space 6) :
    (homologySixGroupedKernelEquiv a :
      SingularHomology (RegularOverlap none) 5 × EllipticOverlapFifth) =
        (starConnectingHomomorphism 5 a none,
          fun j => starConnectingHomomorphism 5 a (some j)) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree
