import Wikipedia.HopfProblem.ThreefoldHomologyCuspFibreGeometry
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology

/-!
# The actual cusp fibre and boundary surject onto filling homology

Move the original boundary fibre to a high logarithmic level, keeping
its real period coordinate fixed.  That actual fibre has the proved
small-level specialization homotopy, so its inclusion surjects onto the
homology of the whole fixed-radius cap.  Homotopy invariance proves the
same statement for the original boundary fibre and hence the original
boundary-to-filling coefficient, in every integral degree.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SpecialPeriods.CuspFamily CuspUniformization
open ThreefoldOverlapMappingTorus.Cusp ThreefoldHomologyFinitenessCusp
open SingularMayerVietoris PeriodTorusHigherHomology

/-- An allowed logarithmic height exists inside every positive target radius. -/
theorem exists_smallHeight (D : Data) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : Height D.radius, ‖heightParameter D h‖ < δ := by
  let h : Height D.radius :=
    ⟨max (heightThreshold D.radius) (heightThreshold δ) + 1,
      by
        change heightThreshold D.radius < max (heightThreshold D.radius) (heightThreshold δ) + 1
        exact (le_max_left _ _).trans_lt (lt_add_one _)⟩
  refine ⟨h, ?_⟩
  have hh : heightThreshold δ + 1 ≤ (h : ℝ) := by
    change heightThreshold δ + 1 ≤ max (heightThreshold D.radius) (heightThreshold δ) + 1
    linarith [le_max_right (heightThreshold D.radius) (heightThreshold δ)]
  rw [heightParameter_norm]
  calc
    Real.exp (-2 * Real.pi * (h : ℝ)) ≤
        Real.exp (-2 * Real.pi * (heightThreshold δ + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    _ < δ := cutoffRadius_threshold_lt hδ

/-- Height interpolation equates the actual full-cap fibre maps on all integral homology. -/
theorem fibreToFull_homology_eq (D : Data) (h₀ h₁ : Height D.radius) (n : ℕ) :
    singularHomologyMap (fibreToFull D h₀) n = singularHomologyMap (fibreToFull D h₁) n :=
  homotopy_homologyMap (fibreHeightHomotopy D h₀ h₁) n

/-- Every actual boundary fibre, at every allowed height, generates the
integral homology of the entire original fixed-radius cusp cap. -/
theorem fibreToFull_homology_surjective (D : Data) (h : Height D.radius) (n : ℕ) :
    Function.Surjective (singularHomologyMap (fibreToFull D h) n) := by
  obtain ⟨δ, hδ, _hδr, hsmall⟩ := exists_smallFibreInclusion_homology_surjective D
  obtain ⟨h', hh'⟩ := exists_smallHeight D hδ
  rw [fibreToFull_homology_eq D h h' n, ← heightFibreHomeomorph_inclusion,
    singularHomologyMap_comp]
  exact (hsmall (heightParameter D h') (heightParameter_ne_zero D h') hh'.le n).comp
    (homeomorphHomologyEquiv (heightFibreHomeomorph D h') n).surjective

/-- The generic full-cap map is exactly the original special cusp fibre map. -/
theorem specialFibreToPiece_eq :
    specialFibreToPiece = fibreToFull specialData specialHeight := rfl

/-- The actual global coefficient is the same original cusp fibre map. -/
theorem fibreToFilling_eq :
    ThreefoldOverlapMappingTorus.fibreToFilling none = specialFibreToPiece := by
  rw [ThreefoldOverlapMappingTorus.fibreToFilling,
    ThreefoldOverlapMappingTorus.boundaryToFilling_cusp]
  rfl

/-- Unconditional surjectivity of the actual cusp fibre-to-filling map,
for the original gluing radius and every integral homology degree. -/
theorem fibreToFilling_homology_surjective (n : ℕ) :
    Function.Surjective
      (singularHomologyMap (ThreefoldOverlapMappingTorus.fibreToFilling none) n) := by
  rw [fibreToFilling_eq, specialFibreToPiece_eq]
  exact fibreToFull_homology_surjective specialData specialHeight n

/-- The actual cusp boundary-to-filling coefficient is onto in every degree. -/
theorem boundaryFillingHomologyMap_surjective (n : ℕ) :
    Function.Surjective (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none n) := by
  intro a
  obtain ⟨b, hb⟩ := fibreToFilling_homology_surjective n a
  refine ⟨singularHomologyMap (MappingTorus.HomologyCover.fibreInclusion
    (ThreefoldOverlapMappingTorus.monodromy none)) n b, ?_⟩
  exact (LinearMap.congr_fun
    (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre none n) b).trans hb

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
