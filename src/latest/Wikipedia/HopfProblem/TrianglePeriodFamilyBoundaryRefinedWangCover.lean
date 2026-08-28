import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRefinedWangCoverTopology
import Wikipedia.HopfProblem.MappingTorusHomologyHomotopies

/-!
# Actual retractions and quarter fibres of the refined Wang cover

Contract only the real coordinate in each of the two genuine shorter
intersection intervals. The resulting homotopy equivalence keeps the fibre
coordinate and commutes with inclusion into the original intersection.
The actual quarter and three-quarter fibres give its two coproduct sections.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang

open ContinuousMap
open PeriodTorusHigherHomology PeriodTorusHigherHomology.CircleTopology

variable {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)

/-- The actual refined intersection retracts to the two original fibre copies. -/
def intersectionHomotopyEquiv : ↥(U φ ∩ V φ) ≃ₕ X ⊕ X := by
  letI : ContractibleSpace LowerInterval :=
    intervalContractible (1 / 8 : ℝ) (3 / 8) (by norm_num)
  letI : ContractibleSpace UpperInterval :=
    intervalContractible (5 / 8 : ℝ) (7 / 8) (by norm_num)
  exact (intersectionHomeomorph φ).toHomotopyEquiv.trans
    (sumHomotopyEquiv (contractibleProdHomotopyEquiv LowerInterval X)
      (contractibleProdHomotopyEquiv UpperInterval X))

@[simp] theorem intersectionHomotopyEquiv_inl (p : LowerInterval × X) :
    intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inl p)) =
      Sum.inl p.2 := by
  change Sum.map (fun p : LowerInterval × X => p.2) (fun p : UpperInterval × X => p.2)
    (intersectionHomeomorph φ ((intersectionHomeomorph φ).symm (Sum.inl p))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

@[simp] theorem intersectionHomotopyEquiv_inr (p : UpperInterval × X) :
    intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inr p)) =
      Sum.inr p.2 := by
  change Sum.map (fun p : LowerInterval × X => p.2) (fun p : UpperInterval × X => p.2)
    (intersectionHomeomorph φ ((intersectionHomeomorph φ).symm (Sum.inr p))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- The two genuine retractions agree after the literal intersection inclusion. -/
theorem intersectionHomotopyEquiv_inclusion :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv φ).toFun.comp
        (intersectionInclusion φ) = (intersectionHomotopyEquiv φ).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph φ).symm.surjective q
  cases p with
  | inl p =>
      change MappingTorus.HomologyCover.intersectionHomotopyEquiv φ
          (intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inl p))) =
        intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inl p))
      rw [intersectionHomeomorph_symm_inl_inclusion,
        MappingTorus.HomologyCover.intersectionHomotopyEquiv_inl, intersectionHomotopyEquiv_inl]
  | inr p =>
      change MappingTorus.HomologyCover.intersectionHomotopyEquiv φ
          (intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inr p))) =
        intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inr p))
      rw [intersectionHomeomorph_symm_inr_inclusion,
        MappingTorus.HomologyCover.intersectionHomotopyEquiv_inr, intersectionHomotopyEquiv_inr]

/-- The first actual refined-component time is the literal one-quarter point. -/
def lowerComponentTime : LowerInterval := ⟨1 / 4, by constructor <;> norm_num⟩

/-- The second actual refined-component time is the literal three-quarter point. -/
def upperComponentTime : UpperInterval := ⟨3 / 4, by constructor <;> norm_num⟩

/-- Insert the fibre at one quarter into the actual refined intersection. -/
def lowerComponentFibre : C(X, ↥(U φ ∩ V φ)) where
  toFun x := (intersectionHomeomorph φ).symm (Sum.inl (lowerComponentTime, x))
  continuous_toFun := (intersectionHomeomorph φ).symm.continuous.comp
    (continuous_inl.comp (continuous_const.prodMk continuous_id))

/-- Insert the fibre at three quarters into the other actual refined component. -/
def upperComponentFibre : C(X, ↥(U φ ∩ V φ)) where
  toFun x := (intersectionHomeomorph φ).symm (Sum.inr (upperComponentTime, x))
  continuous_toFun := (intersectionHomeomorph φ).symm.continuous.comp
    (continuous_inr.comp (continuous_const.prodMk continuous_id))

@[simp] theorem lowerComponentFibre_coe (x : X) :
    (lowerComponentFibre φ x).val = MappingTorus.mk φ (1 / 4, x) :=
  intersectionHomeomorph_symm_inl_coe φ (lowerComponentTime, x)

@[simp] theorem upperComponentFibre_coe (x : X) :
    (upperComponentFibre φ x).val = MappingTorus.mk φ (3 / 4, x) :=
  intersectionHomeomorph_symm_inr_coe φ (upperComponentTime, x)

/-- The actual lower fibre is sent to the first coproduct summand. -/
theorem lowerComponentFibre_retraction :
    (intersectionHomotopyEquiv φ).toFun.comp (lowerComponentFibre φ) = sumInlMap X X := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inl φ (lowerComponentTime, x)

/-- The actual upper fibre is sent to the second coproduct summand. -/
theorem upperComponentFibre_retraction :
    (intersectionHomotopyEquiv φ).toFun.comp (upperComponentFibre φ) = sumInrMap X X := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inr φ (upperComponentTime, x)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang
