import Wikipedia.HopfProblem.ThreefoldPicardExponentialBasic
import Wikipedia.HopfProblem.ThreefoldPicardExponentialConstants
import Wikipedia.HopfProblem.HolomorphicPicardGroup

/-!
# The native Picard group of the threefold is its holomorphic H¹

The actual integral constant-sheaf cohomology groups in degrees one and
two vanish, by the genuine sheaf--singular comparison and the proved
integral cohomology of the original glued threefold. The genuine long
exact sequence therefore makes the original holomorphic exponential an
isomorphism on degree-one cohomology. The already proved native Picard
classification then identifies the actual tensor-product group of line
bundle isomorphism classes with the original `H¹(O_X)`.

No identification of the threefold with a sphere is assumed, and no value
or dimension of `H¹(O_X)` is imposed or asserted. The maps retain the
ordinary exponential and the original integral normalization `2πi n`.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PicardExponential

open HolomorphicExponentialSheaf

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Genuine integral degree-two vanishing annihilates the original
exponential connecting map, without a sphere-recognition premise. -/
theorem exponentialConnectingH1_eq_zero (x : UnitsH1) : exponentialConnectingH1 x = 0 :=
  integerSheafH2_eq_zero _

/-- Vanishing of original integral H¹ makes the ordinary exponential
injective on actual holomorphic degree-one cohomology. -/
theorem exponentialH1_injective : Function.Injective exponentialH1 := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, hy⟩ := (exponentialH1_exact x).mp hx
  have hy0 := integerSheafH1_eq_zero y
  simpa only [hy0, map_zero] using hy.symm

/-- Vanishing of original integral H² gives an actual preimage under
the original exponential map for every genuine unit-sheaf H¹ class. -/
theorem exponentialH1_surjective : Function.Surjective exponentialH1 := by
  intro x
  exact (exponentialH1_connecting_exact x).mp (exponentialConnectingH1_eq_zero x)

theorem exponentialH1_bijective : Function.Bijective exponentialH1 :=
  ⟨exponentialH1_injective, exponentialH1_surjective⟩

/-- The original sheaf exponential induces an unconditional additive
equivalence on genuine degree-one cohomology of the actual threefold. -/
def exponentialH1Equiv : HolomorphicH1 ≃+ UnitsH1 :=
  AddEquiv.ofBijective exponentialH1 exponentialH1_bijective

@[simp] theorem exponentialH1Equiv_apply (x : HolomorphicH1) :
    exponentialH1Equiv x = CategoryTheory.Sheaf.H.map (exponential IF Space) 1 x := rfl

/-- The same original induced map is an isomorphism in abelian groups. -/
def exponentialH1Iso : AddCommGrpCat.of HolomorphicH1 ≅ AddCommGrpCat.of UnitsH1 :=
  exponentialH1Equiv.toAddCommGrpIso

@[simp] theorem exponentialH1Iso_hom :
    exponentialH1Iso.hom = AddCommGrpCat.ofHom exponentialH1 := by
  ext x
  rfl

/-- The actual original native line bundles modulo analytic fibre-linear
isomorphism, with the already proved actual tensor-product group law. -/
abbrev PicardGroup := HolomorphicPicard.LineBundle.IsoClasses.{0} IF Space

/-- The constructed threefold's genuine Picard group is its actual
holomorphic degree-one cohomology. No numerical H¹ calculation is used. -/
def picardHolomorphicH1Equiv : PicardGroup ≃+ HolomorphicH1 :=
  (HolomorphicPicard.LineBundle.classificationAddEquiv IF Space).trans exponentialH1Equiv.symm

/-- Exponentiating the image of a native bundle class returns exactly
its original genuine unit-sheaf cocycle class. -/
theorem exponentialH1_picardHolomorphicH1Equiv (x : PicardGroup) :
    exponentialH1 (picardHolomorphicH1Equiv x) =
      HolomorphicPicard.LineBundle.isoClassCohomologyClass IF Space x :=
  exponentialH1Equiv.apply_symm_apply _

/-- The comparison uses the actual cocycle of each original native bundle. -/
theorem exponentialH1_picardHolomorphicH1Equiv_toIsoClasses
    (V : HolomorphicPicard.LineBundle.{0} IF Space) :
    exponentialH1 (picardHolomorphicH1Equiv
      (HolomorphicPicard.LineBundle.toIsoClasses IF Space V)) =
        HolomorphicPicard.LineBundle.cohomologyClass IF Space V :=
  exponentialH1_picardHolomorphicH1Equiv _

/-- Conversely, the bundle class assigned to a genuine holomorphic H¹
class has exactly its image under the original sheaf exponential. -/
theorem picardHolomorphicH1Equiv_symm_class (x : HolomorphicH1) :
    HolomorphicPicard.LineBundle.isoClassCohomologyClass IF Space
      (picardHolomorphicH1Equiv.symm x) = exponentialH1 x := by
  have h := exponentialH1_picardHolomorphicH1Equiv (picardHolomorphicH1Equiv.symm x)
  rw [picardHolomorphicH1Equiv.apply_symm_apply] at h
  exact h.symm

/-- Each actual native bundle has a unique genuine holomorphic H¹
preimage under the original exponential map. -/
theorem existsUnique_holomorphicH1_of_bundle
    (V : HolomorphicPicard.LineBundle.{0} IF Space) :
    ∃! x : HolomorphicH1, exponentialH1 x =
      HolomorphicPicard.LineBundle.cohomologyClass IF Space V := by
  let c := HolomorphicPicard.LineBundle.cohomologyClass IF Space V
  refine ⟨exponentialH1Equiv.symm c, exponentialH1Equiv.apply_symm_apply c, ?_⟩
  intro y hy
  apply exponentialH1_injective
  exact hy.trans (exponentialH1Equiv.apply_symm_apply c).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PicardExponential
