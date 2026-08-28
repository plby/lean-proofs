import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyHomotopy
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct

/-!
# The actual specialization map in the original four-period marking

The map is the original source collapse precomposed with the inverse of
the proved coordinate homeomorphism.  The exact positive-`M₀` conjugacy
and the genuine central rotation homotopy imply invariance of its actual
integral singular homology map in every degree.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The genuine collapse with source periods ordered `(β₀, β₁, α₀, α₁)`. -/
def markedCollapse : C(ProductTorus 4, QuotientCentralFibre C ε) :=
  (sourceCollapse C ε hε).comp
    ((sourceCoordinateTorusHomeomorph (C 0)).symm : C(ProductTorus 4, SourceModel (C 0)))

/-- This changes only the actual product coordinates, not the collapse map. -/
theorem markedCollapse_eq_product :
    markedCollapse C ε hε = (productCollapse C ε hε).comp
      (sourceProductCoordinateHomeomorph.symm :
        C(ProductTorus 4, CompactFibreTorus × ProductTorus 2)) := rfl

theorem markedCollapse_comp_sourceCoordinates :
    (markedCollapse C ε hε).comp
      (sourceCoordinateTorusHomeomorph (C 0) : C(SourceModel (C 0), ProductTorus 4)) =
        sourceCollapse C ε hε := by
  apply ContinuousMap.ext
  intro x
  change sourceCollapse C ε hε
    ((sourceCoordinateTorusHomeomorph (C 0)).symm (sourceCoordinateTorusHomeomorph (C 0) x)) = _
  rw [Homeomorph.symm_apply_apply]

theorem markedCollapse_comp_productCoordinates :
    (markedCollapse C ε hε).comp
      (sourceProductCoordinateHomeomorph :
        C(CompactFibreTorus × ProductTorus 2, ProductTorus 4)) = productCollapse C ε hε := by
  rw [markedCollapse_eq_product]
  apply ContinuousMap.ext
  intro x
  change productCollapse C ε hε
    (sourceProductCoordinateHomeomorph.symm (sourceProductCoordinateHomeomorph x)) = _
  rw [Homeomorph.symm_apply_apply]

theorem sourceCoordinateTorusHomeomorph_symm_matrix (x : ProductTorus 4) :
    (sourceCoordinateTorusHomeomorph (C 0)).symm (torusMatrixMap M₀ x) =
      sourceShear (C 0) ((sourceCoordinateTorusHomeomorph (C 0)).symm x) := by
  apply (sourceCoordinateTorusHomeomorph (C 0)).injective
  rw [Homeomorph.apply_symm_apply, sourceCoordinateTorusHomeomorph_shear,
    Homeomorph.apply_symm_apply]

/-- The actual matrix map is the exact conjugate of the original source shear. -/
theorem markedCollapse_comp_matrix :
    (markedCollapse C ε hε).comp (torusMatrixMap M₀) =
      ((sourceCollapse C ε hε).comp (sourceShear (C 0))).comp
        ((sourceCoordinateTorusHomeomorph (C 0)).symm :
          C(ProductTorus 4, SourceModel (C 0))) := by
  apply ContinuousMap.ext
  intro x
  change sourceCollapse C ε hε
    ((sourceCoordinateTorusHomeomorph (C 0)).symm (torusMatrixMap M₀ x)) = _
  rw [sourceCoordinateTorusHomeomorph_symm_matrix]
  rfl

/-- Monodromy invariance comes from an actual homotopy into the literal central fibre. -/
def markedCollapseMonodromyHomotopy :
    (markedCollapse C ε hε).Homotopy
      ((markedCollapse C ε hε).comp (torusMatrixMap M₀)) := by
  rw [markedCollapse_comp_matrix]
  have h := (sourceRotationHomotopy C ε hε 1).compContinuousMap
    ((sourceCoordinateTorusHomeomorph (C 0)).symm : C(ProductTorus 4, SourceModel (C 0)))
  simpa only [sourceRotation_one, markedCollapse] using h

theorem markedCollapse_homology_comp_matrix (n : ℕ) :
    (singularHomologyMap (markedCollapse C ε hε) n).comp
      (singularHomologyMap (torusMatrixMap M₀) n) =
        singularHomologyMap (markedCollapse C ε hε) n := by
  rw [← singularHomologyMap_comp]
  exact (homotopy_homologyMap (markedCollapseMonodromyHomotopy C ε hε) n).symm

/-- The equality concerns the actual homology maps, not an assumed matrix representation. -/
theorem markedCollapse_homology_invariant (n : ℕ)
    (a : SingularHomology (ProductTorus 4) n) :
    singularHomologyMap (markedCollapse C ε hε) n
      (singularHomologyMap (torusMatrixMap M₀) n a) =
        singularHomologyMap (markedCollapse C ε hε) n a :=
  LinearMap.congr_fun (markedCollapse_homology_comp_matrix C ε hε n) a

theorem markedCollapse_homology_range_variation (n : ℕ) :
    LinearMap.range (singularHomologyMap (torusMatrixMap M₀) n - LinearMap.id) ≤
      LinearMap.ker (singularHomologyMap (markedCollapse C ε hε) n) := by
  rintro a ⟨b, rfl⟩
  change singularHomologyMap (markedCollapse C ε hε) n
    (singularHomologyMap (torusMatrixMap M₀) n b - b) = 0
  rw [map_sub, markedCollapse_homology_invariant, sub_self]

/-- The coordinate homeomorphism changes the source of the actual induced map. -/
theorem markedCollapse_homology_source (n : ℕ)
    (a : SingularHomology (SourceModel (C 0)) n) :
    singularHomologyMap (markedCollapse C ε hε) n
      (homeomorphHomologyEquiv (sourceCoordinateTorusHomeomorph (C 0)) n a) =
        singularHomologyMap (sourceCollapse C ε hε) n a := by
  have h := congrArg (fun f => singularHomologyMap f n)
    (markedCollapse_comp_sourceCoordinates C ε hε)
  rw [singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem markedCollapse_homology_product (n : ℕ)
    (a : SingularHomology (CompactFibreTorus × ProductTorus 2) n) :
    singularHomologyMap (markedCollapse C ε hε) n
      (homeomorphHomologyEquiv sourceProductCoordinateHomeomorph n a) =
        singularHomologyMap (productCollapse C ε hε) n a := by
  have h := congrArg (fun f => singularHomologyMap f n)
    (markedCollapse_comp_productCoordinates C ε hε)
  rw [singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

/-- Surjectivity is transported through the proved original source homeomorphism. -/
theorem markedCollapse_homology_surjective_of_source (n : ℕ)
    (hf : Function.Surjective (singularHomologyMap (sourceCollapse C ε hε) n)) :
    Function.Surjective (singularHomologyMap (markedCollapse C ε hε) n) := by
  intro x
  obtain ⟨a, rfl⟩ := hf x
  exact ⟨homeomorphHomologyEquiv (sourceCoordinateTorusHomeomorph (C 0)) n a,
    markedCollapse_homology_source C ε hε n a⟩

/-- Surjectivity is transported through the proved marked-product homeomorphism. -/
theorem markedCollapse_homology_surjective_of_product (n : ℕ)
    (hf : Function.Surjective (singularHomologyMap (productCollapse C ε hε) n)) :
    Function.Surjective (singularHomologyMap (markedCollapse C ε hε) n) := by
  intro x
  obtain ⟨a, rfl⟩ := hf x
  exact ⟨homeomorphHomologyEquiv sourceProductCoordinateHomeomorph n a,
    markedCollapse_homology_product C ε hε n a⟩

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
