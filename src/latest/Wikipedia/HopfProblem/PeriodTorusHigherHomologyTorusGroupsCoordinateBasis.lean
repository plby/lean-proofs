import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsTopClass
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsCoordinateMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturality

/-!
# Actual coordinate-subtorus classes form an integral homology basis

Each generator is the actual singular homology map of a literal
coordinate-subtorus inclusion, evaluated on the genuine normalized top
class of the source torus. The proof identifies these classes with the
standard coordinate vectors through the proved Mayer--Vietoris recurrence.
Thus the basis statement concerns the actual induced maps, not just ranks.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris CircleTopology

/-- The actual homology class induced from a coordinate subtorus. -/
def coordinateTorusClass (r n : ℕ) (i : Fin (r.choose n)) :
    SingularHomology (ProductTorus r) n :=
  singularHomologyMap (coordinateTorusMap r n i) n (productTorusTopClass n)

@[simp] theorem coordinateTorusClass_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusClass r 0 i = pointClass (0 : ProductTorus r) := by
  rw [coordinateTorusClass, productTorusTopClass_zero, singularHomologyMap_pointClass,
    coordinateTorusMap_degree_zero]
  rfl

theorem homeomorphHomology_coordinateTorusMap_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) (a : SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (singularHomologyMap (coordinateTorusMap (r + 1) (n + 1)
          ((binomialPascalIndexEquiv r n).symm (Sum.inl j))) (n + 1) a) =
      circleSectionHomology (ProductTorus r) (n + 1)
        (singularHomologyMap (coordinateTorusMap r (n + 1) j) (n + 1) a) := by
  change ((singularHomologyMap
      (productTorusSuccHomeomorph r :
        C(ProductTorus (r + 1), Circle × ProductTorus r)) (n + 1)).comp
        (singularHomologyMap (coordinateTorusMap (r + 1) (n + 1)
          ((binomialPascalIndexEquiv r n).symm (Sum.inl j))) (n + 1))) a = _
  rw [← singularHomologyMap_comp, coordinateTorusMap_omit, singularHomologyMap_comp]
  rfl

theorem homeomorphHomology_coordinateTorusMap_take (r n : ℕ)
    (j : Fin (r.choose n)) (a : SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (singularHomologyMap (coordinateTorusMap (r + 1) (n + 1)
          ((binomialPascalIndexEquiv r n).symm (Sum.inr j))) (n + 1) a) =
      singularHomologyMap (circleProductMap (coordinateTorusMap r n j)) (n + 1)
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1) a) := by
  change ((singularHomologyMap
      (productTorusSuccHomeomorph r :
        C(ProductTorus (r + 1), Circle × ProductTorus r)) (n + 1)).comp
        (singularHomologyMap (coordinateTorusMap (r + 1) (n + 1)
          ((binomialPascalIndexEquiv r n).symm (Sum.inr j))) (n + 1))) a = _
  rw [← singularHomologyMap_comp, coordinateTorusMap_take, singularHomologyMap_comp]
  rfl

/-- Omitting the first coordinate gives the actual section summand. -/
theorem circleCoordinates_coordinateTorusClass_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))) =
      (coordinateTorusClass r (n + 1) j, 0) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_omit, circleProductHomologyEquiv_section]

/-- Taking the first coordinate gives the actual connecting summand, by
naturality of the genuine Mayer--Vietoris connecting map. -/
theorem circleCoordinates_coordinateTorusClass_take (r n : ℕ)
    (j : Fin (r.choose n)) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))) =
      (0, coordinateTorusClass r n j) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_take, circleProductHomologyEquiv_naturality,
    productTorusTopClass_succ_coordinates, map_zero]

/-- A pair-valued form of the actual recursive coordinate formula. -/
theorem productTorusHomologyEquiv_succ_pair (r n : ℕ)
    (a : SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      ((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
        (productTorusHomologyEquiv r n).toAddEquiv)
          (circleProductHomologyEquiv (ProductTorus r) n
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)) :=
  productTorusHomologyEquiv_succ_apply r n a

theorem productTorusHomologyEquiv_coordinateTorusClass_zero
    (r : ℕ) (i : Fin (r.choose 0)) :
    productTorusHomologyEquiv r 0 (coordinateTorusClass r 0 i) = Pi.single i 1 := by
  rw [coordinateTorusClass_zero, productTorusHomologyEquiv_zero]
  change integerBinomialZeroEquiv r
    (connectedHomologyZeroEquiv (ProductTorus r) (pointClass (0 : ProductTorus r))) = _
  rw [connectedHomologyZeroEquiv_pointClass]
  exact integerBinomialZeroEquiv_one_single r i

/-- Every literal coordinate-subtorus top class maps to the corresponding
standard integral coordinate vector. -/
theorem productTorusHomologyEquiv_coordinateTorusClass (r n : ℕ)
    (i : Fin (r.choose n)) :
    productTorusHomologyEquiv r n (coordinateTorusClass r n i) = Pi.single i 1 := by
  induction r generalizing n with
  | zero =>
      cases n with
      | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero 0 i
      | succ n => exact Fin.elim0 i
  | succ r ih =>
      cases n with
      | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero (r + 1) i
      | succ n =>
          obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
          cases j with
          | inl j =>
              apply (binomialModuleSuccEquiv r n).injective
              rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_omit,
                binomialModuleSuccEquiv_single_inl]
              change (productTorusHomologyEquiv r (n + 1) (coordinateTorusClass r (n + 1) j),
                productTorusHomologyEquiv r n 0) = (Pi.single j 1, 0)
              rw [ih (n + 1) j, map_zero]
          | inr j =>
              apply (binomialModuleSuccEquiv r n).injective
              rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_take,
                binomialModuleSuccEquiv_single_inr]
              change (productTorusHomologyEquiv r (n + 1) 0,
                productTorusHomologyEquiv r n (coordinateTorusClass r n j)) = (0, Pi.single j 1)
              rw [map_zero, ih n j]

/-- A basis of actual integral singular homology whose vectors are proved
below to be the actual images of coordinate-subtorus top classes. -/
def coordinateTorusBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (SingularHomology (ProductTorus r) n) :=
  (binomialCoordinateBasis r n).map (productTorusHomologyEquiv r n).symm

/-- The basis vectors are the literal induced coordinate-subtorus classes. -/
@[simp] theorem coordinateTorusBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasis r n i = coordinateTorusClass r n i := by
  apply (productTorusHomologyEquiv r n).injective
  rw [coordinateTorusBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    binomialCoordinateBasis_apply, productTorusHomologyEquiv_coordinateTorusClass]

theorem coordinateTorusBasis_coe (r n : ℕ) :
    ⇑(coordinateTorusBasis r n) = coordinateTorusClass r n :=
  funext (coordinateTorusBasis_apply r n)

theorem coordinateTorusClass_linearIndependent (r n : ℕ) :
    LinearIndependent ℤ (coordinateTorusClass r n) := by
  simpa only [coordinateTorusBasis_coe] using (coordinateTorusBasis r n).linearIndependent

/-- The actual induced coordinate-subtorus classes span all of actual homology. -/
theorem coordinateTorusClass_span (r n : ℕ) :
    Submodule.span ℤ (Set.range (coordinateTorusClass r n)) = ⊤ := by
  simpa only [coordinateTorusBasis_coe] using (coordinateTorusBasis r n).span_eq

/-- To prove a map onto actual torus homology is surjective, it suffices
to realize each literal coordinate-subtorus top class in its range. -/
theorem surjective_of_coordinateTorusClass_mem_range {M : Type*}
    [AddCommGroup M] [Module ℤ M] (r n : ℕ)
    (f : M →ₗ[ℤ] SingularHomology (ProductTorus r) n)
    (hf : ∀ i : Fin (r.choose n), coordinateTorusClass r n i ∈ LinearMap.range f) :
    Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← coordinateTorusClass_span r n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hf i

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
