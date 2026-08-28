import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris

/-!
# Actual cone-product projections and middle sections

These maps use literal preimages of subsets under the second product
projection. A contractible cone factor makes the first projection a
genuine homotopy equivalence. The middle section of a suspension has the
explicit height one half.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

/-- The literal preimage under the second projection has its ordinary product topology. -/
def rightPreimageHomeomorph (S : Set Y) :
    (Prod.snd ⁻¹' S : Set (X × Y)) ≃ₜ X × S where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The literal first projection from this subset. -/
def rightPreimageProjection (S : Set Y) : C((Prod.snd ⁻¹' S : Set (X × Y)), X) :=
  ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- Removing an actually contractible second factor gives a constructed homotopy equivalence. -/
def rightPreimageContractibleHomotopyEquiv (S : Set Y) [ContractibleSpace S] :
    (Prod.snd ⁻¹' S : Set (X × Y)) ≃ₕ X :=
  (rightPreimageHomeomorph X Y S).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl X).prodCongr
      (Classical.choice (ContractibleSpace.hequiv_unit S))).trans
        (Homeomorph.prodUnique X Unit).toHomotopyEquiv)

@[simp] theorem rightPreimageContractibleHomotopyEquiv_apply (S : Set Y)
    [ContractibleSpace S] (p : (Prod.snd ⁻¹' S : Set (X × Y))) :
    rightPreimageContractibleHomotopyEquiv X Y S p = p.1.1 := rfl

/-- The actual projection is therefore injective on singular homology in every degree. -/
theorem rightPreimageProjection_homology_injective (S : Set Y) [ContractibleSpace S]
    (n : ℕ) : Function.Injective (singularHomologyMap (rightPreimageProjection X Y S) n) :=
  (homotopyEquivHomologyEquiv (rightPreimageContractibleHomotopyEquiv X Y S) n).injective

/-- The actual midpoint section of the suspension belt. -/
def suspensionMiddleSection : C(Y, Suspension.middleBand Y) :=
  ⟨fun y => Suspension.middleBandHomeomorph.symm (⟨1 / 2, by norm_num⟩, y),
    Suspension.middleBandHomeomorph.symm.continuous.comp
      (continuous_const.prodMk continuous_id)⟩

@[simp] theorem suspensionMiddleSection_coe (y : Y) :
    (suspensionMiddleSection Y y : Suspension Y) =
      Suspension.mk ⟨1 / 2, by norm_num⟩ y := rfl

@[simp] theorem suspensionMiddleSection_label (y : Y) :
    Suspension.middleBandHomotopyEquiv (suspensionMiddleSection Y y) = y := by
  change (Suspension.middleBandHomeomorph
    (Suspension.middleBandHomeomorph.symm (⟨1 / 2, by norm_num⟩, y))).2 = y
  rw [Homeomorph.apply_symm_apply]

/-- Adjoin a fixed midpoint edge to an unchanged first factor. -/
def suspensionProductMiddleSection (y : Y) :
    C(X, (Prod.snd ⁻¹' Suspension.middleBand Y : Set (X × Suspension Y))) :=
  ⟨fun x => ⟨(x, suspensionMiddleSection Y y), (suspensionMiddleSection Y y).2⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

@[simp] theorem suspensionProductMiddleSection_coe (y : Y) (x : X) :
    (suspensionProductMiddleSection X Y y x : X × Suspension Y) =
      (x, Suspension.mk ⟨1 / 2, by norm_num⟩ y) := rfl

/-- Actual intersection classes in the source kernel lift through the proved
Mayer--Vietoris sequence; naturality then detects surjectivity in the target. -/
theorem contractibleTargetCoverMap_homology_surjective
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = univ)
    [ContractibleSpace U'] [ContractibleSpace V']
    (hfU : MapsTo f U U') (hfV : MapsTo f V V') (n : ℕ)
    (hlift : ∀ b : SingularHomology (U' ∩ V' : Set Y) n,
      ∃ c : SingularHomology (U ∩ V : Set X) n,
        leftHomologyMap U V n c = 0 ∧
          singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n c = b) :
    Function.Surjective (singularHomologyMap f (n + 1)) := by
  intro b
  obtain ⟨c, hc, hcb⟩ := hlift (connectingHomomorphism U' V' hU' hV' hcover' n b)
  have hr : c ∈ LinearMap.range (connectingHomomorphism U V hU hV hcover n) := by
    rw [exact_at_intersection]
    exact hc
  obtain ⟨a, ha⟩ := hr
  refine ⟨a, contractibleCoverConnecting_injective U' V' hU' hV' hcover' n ?_⟩
  have hn := connectingHomomorphism_naturality_apply f U V U' V' hfU hfV
    hU hV hcover hU' hV' hcover' n a
  rw [ha, hcb] at hn
  exact hn.symm

end Wikipedia.HopfProblem.CuspCentralHomology
