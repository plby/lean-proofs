import Wikipedia.HopfProblem.ThreefoldHomologyGluingMaps
import Wikipedia.HopfProblem.ThreefoldHomologyGluingAlgebra
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Mayer–Vietoris for every actual threefold filling attachment

The proved two-open cover of an attachment stage gives the genuine
integral singular Mayer–Vietoris sequence. Its auxiliary subspaces are
identified with the literal preceding stage, filling patch, and full
regular overlap by the existing geometric homeomorphisms. The first map
is the signed pair of actual overlap inclusions and the second map is
the sum of actual stage inclusions. No matrix calculation is assumed.
-/

noncomputable section

open Set
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

variable (s : Finset Puncture) (i : Puncture)

local notation "U" => (attachmentLeft s i : Set (partialPatch (insert i s)))
local notation "V" => (attachmentRight s i : Set (partialPatch (insert i s)))

/-- The actual singular connecting map of the attachment cover before
flattening its intersection subspace. -/
def rawAttachmentConnectingHomomorphism (n : ℕ) :
    StageHomology (insert i s) (n + 1) →ₗ[ℤ]
      SingularHomology (U ∩ V : Set (partialPatch (insert i s))) n :=
  connectingHomomorphism U V (attachmentLeft s i).isOpen (attachmentRight s i).isOpen
    (attachmentLeft_union_right s i) n

/-- The product of the two genuine cover-flattening homology equivalences. -/
def attachmentPairHomologyEquiv (hi : i ∉ s) (n : ℕ) :
    (SingularHomology U n × SingularHomology V n) ≃ₗ[ℤ]
      (StageHomology s n × FillingPatchHomology i n) :=
  ((attachmentLeftHomologyEquiv s i hi n).toAddEquiv.prodCongr
    (attachmentRightHomologyEquiv s i hi n).toAddEquiv).toIntLinearEquiv

@[simp] theorem attachmentPairHomologyEquiv_apply (hi : i ∉ s) (n : ℕ)
    (a : SingularHomology U n × SingularHomology V n) :
    attachmentPairHomologyEquiv s i hi n a =
      (attachmentLeftHomologyEquiv s i hi n a.1,
        attachmentRightHomologyEquiv s i hi n a.2) := rfl

/-- The signed actual overlap-inclusion map, with the standard
Mayer–Vietoris convention (left, -right). -/
def attachmentLeftHomologyMap (n : ℕ) :
    OverlapHomology i n →ₗ[ℤ] (StageHomology s n × FillingPatchHomology i n) := by
  let f := (overlapPreviousHomologyMap s i n).toAddMonoidHom.prod
    (-(overlapFillingHomologyMap i n).toAddMonoidHom)
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r a := by
        convert! f.map_zsmul r a using 1
        exact congrArg f (int_smul_eq_zsmul ..) }

/-- The sum of the two literal inclusions into the enlarged stage. -/
def attachmentRightHomologyMap (n : ℕ) :
    (StageHomology s n × FillingPatchHomology i n) →ₗ[ℤ] StageHomology (insert i s) n := by
  let f := (previousStageHomologyMap s i n).toAddMonoidHom.coprod
    (fillingStageHomologyMap s i n).toAddMonoidHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r a := by
        convert! f.map_zsmul r a using 1
        exact int_smul_eq_zsmul .. }

@[simp] theorem attachmentLeftHomologyMap_apply (n : ℕ) (a : OverlapHomology i n) :
    attachmentLeftHomologyMap s i n a =
      (overlapPreviousHomologyMap s i n a, -overlapFillingHomologyMap i n a) := rfl

@[simp] theorem attachmentRightHomologyMap_apply (n : ℕ)
    (a : StageHomology s n × FillingPatchHomology i n) :
    attachmentRightHomologyMap s i n a =
      previousStageHomologyMap s i n a.1 + fillingStageHomologyMap s i n a.2 := rfl

/-- The actual singular connecting homomorphism with codomain the
homology of the full geometric regular/filling overlap. -/
def attachmentConnectingHomomorphism (hi : i ∉ s) (n : ℕ) :
    StageHomology (insert i s) (n + 1) →ₗ[ℤ] OverlapHomology i n :=
  (attachmentOverlapHomologyEquiv s i hi n).toLinearMap.comp
    (rawAttachmentConnectingHomomorphism s i n)

/-- The signed geometric map is exactly the raw singular-chain map
under the actual cover identifications. -/
theorem attachmentLeftHomologyMap_comparison (hi : i ∉ s) (n : ℕ) :
    (attachmentLeftHomologyMap s i n).comp
        (attachmentOverlapHomologyEquiv s i hi n).toLinearMap =
      (attachmentPairHomologyEquiv s i hi n).toLinearMap.comp
        (leftHomologyMap U V n) := by
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, leftHomologyMap_apply,
    attachmentPairHomologyEquiv_apply, attachmentLeftHomologyMap_apply, map_neg]
  apply Prod.ext
  · exact (LinearMap.congr_fun (attachmentLeftHomologyEquiv_overlap s i hi n) a).symm
  · exact congrArg Neg.neg
      (LinearMap.congr_fun (attachmentRightHomologyEquiv_overlap s i hi n) a).symm

/-- The second geometric map is the actual sum of cover inclusions. -/
theorem attachmentRightHomologyMap_comparison (hi : i ∉ s) (n : ℕ) :
    (attachmentRightHomologyMap s i n).comp
        (attachmentPairHomologyEquiv s i hi n).toLinearMap =
      rightHomologyMap U V n := by
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, attachmentPairHomologyEquiv_apply,
    attachmentRightHomologyMap_apply, rightHomologyMap_apply]
  exact congrArg₂ (· + ·)
    (LinearMap.congr_fun (attachmentLeftHomologyEquiv_inclusion s i hi n) a.1)
    (LinearMap.congr_fun (attachmentRightHomologyEquiv_inclusion s i hi n) a.2)

/-- Exactness at the homology of the preceding stage and the new filling. -/
theorem attachment_exact_at_pair (hi : i ∉ s) (n : ℕ) :
    Function.Exact (attachmentLeftHomologyMap s i n) (attachmentRightHomologyMap s i n) := by
  have hraw : Function.Exact (leftHomologyMap U V n) (rightHomologyMap U V n) :=
    LinearMap.exact_iff.mpr
      (exact_at_pair U V (attachmentLeft s i).isOpen (attachmentRight s i).isOpen
        (attachmentLeft_union_right s i) n).symm
  apply exact_of_linearEquiv_squares _ _ _ _ (attachmentOverlapHomologyEquiv s i hi n)
    (attachmentPairHomologyEquiv s i hi n) (LinearEquiv.refl ℤ _)
    (attachmentLeftHomologyMap_comparison s i hi n) _ hraw
  simpa using attachmentRightHomologyMap_comparison s i hi n

/-- Exactness at the actual homology of the full regular overlap. -/
theorem attachment_exact_at_intersection (hi : i ∉ s) (n : ℕ) :
    Function.Exact (attachmentConnectingHomomorphism s i hi n)
      (attachmentLeftHomologyMap s i n) := by
  have hraw : Function.Exact (rawAttachmentConnectingHomomorphism s i n)
      (leftHomologyMap U V n) :=
    LinearMap.exact_iff.mpr
      (exact_at_intersection U V (attachmentLeft s i).isOpen (attachmentRight s i).isOpen
        (attachmentLeft_union_right s i) n).symm
  apply exact_of_linearEquiv_squares _ _ _ _ (LinearEquiv.refl ℤ _)
    (attachmentOverlapHomologyEquiv s i hi n) (attachmentPairHomologyEquiv s i hi n)
    _ (attachmentLeftHomologyMap_comparison s i hi n) hraw
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
    attachmentConnectingHomomorphism]

/-- Exactness at every positive-degree homology group of the actual
enlarged attachment stage. -/
theorem attachment_exact_at_ambient (hi : i ∉ s) (n : ℕ) :
    Function.Exact (attachmentRightHomologyMap s i (n + 1))
      (attachmentConnectingHomomorphism s i hi n) := by
  have hraw : Function.Exact (rightHomologyMap U V (n + 1))
      (rawAttachmentConnectingHomomorphism s i n) :=
    LinearMap.exact_iff.mpr
      (exact_at_ambient U V (attachmentLeft s i).isOpen (attachmentRight s i).isOpen
        (attachmentLeft_union_right s i) n).symm
  apply exact_of_linearEquiv_squares _ _ _ _ (attachmentPairHomologyEquiv s i hi (n + 1))
    (LinearEquiv.refl ℤ _) (attachmentOverlapHomologyEquiv s i hi n) _ _ hraw
  · simpa using attachmentRightHomologyMap_comparison s i hi (n + 1)
  · simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
      attachmentConnectingHomomorphism]

/-- The degree-zero endpoint is surjective for every actual attachment. -/
theorem attachmentRightHomologyMap_zero_surjective (hi : i ∉ s) :
    Function.Surjective (attachmentRightHomologyMap s i 0) := by
  apply surjective_of_linearEquiv_square (rightHomologyMap U V 0) _
    (attachmentPairHomologyEquiv s i hi 0) (LinearEquiv.refl ℤ _)
  · simpa using attachmentRightHomologyMap_comparison s i hi 0
  · exact rightHomologyMap_zero_surjective U V (attachmentLeft s i).isOpen
      (attachmentRight s i).isOpen (attachmentLeft_union_right s i)

/-- The actual all-degree integral singular Mayer–Vietoris attachment
sequence, expressed entirely using the literal geometric spaces. -/
theorem attachment_mayerVietoris_exact (hi : i ∉ s) (n : ℕ) :
    Function.Exact (attachmentConnectingHomomorphism s i hi n)
        (attachmentLeftHomologyMap s i n) ∧
      Function.Exact (attachmentLeftHomologyMap s i n) (attachmentRightHomologyMap s i n) ∧
      Function.Exact (attachmentRightHomologyMap s i (n + 1))
        (attachmentConnectingHomomorphism s i hi n) :=
  ⟨attachment_exact_at_intersection s i hi n, attachment_exact_at_pair s i hi n,
    attachment_exact_at_ambient s i hi n⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
