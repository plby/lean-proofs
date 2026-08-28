import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernel
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationEnds

/-!
# Integral specialization on the actual marked source in every degree

The geometric middle-degree calculations, the top-degree calculation,
and the actual augmentation combine into one all-degree statement.  The
operator in the kernel formula is the induced singular-homology map of
the actual integral matrix map on the coordinate four-torus.  In degrees
two and three the imported marking theorems identify it with the actual
exterior powers of the original cusp monodromy matrix.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC

/-- The actual marked collapse is surjective on integral singular
homology in every degree, at the original ambient cusp radius. -/
theorem markedCollapse_homology_surjective (n : ℕ) :
    Function.Surjective (singularHomologyMap (markedCollapse C r hr) n) := by
  rcases n with _ | (_ | (_ | n))
  · exact (markedCollapse_homologyZero_bijective C r hr).surjective
  · exact markedCollapse_homologyOne_surjective C r hr hC
  · exact markedCollapse_homologyTwo_surjective C r hr hC
  · exact markedCollapse_homology_surjective_of_product C r hr (n + 3)
      (productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC n)

/-- The monodromy-difference image is the exact integral kernel, not
its rational span or its saturation. -/
theorem markedCollapse_homology_kernel (n : ℕ) :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) n) =
      LinearMap.range (singularHomologyMap (torusMatrixMap M₀) n - LinearMap.id) := by
  rcases n with _ | (_ | (_ | (_ | (_ | n))))
  · exact markedCollapse_homologyZero_kernel_eq_variation C r hr
  · simpa only [SpecializationCoinvariants.torusDifference] using
      markedCollapse_homologyOne_kernel C r hr hC
  · simpa only [SpecializationCoinvariants.torusDifference] using
      markedCollapse_homologyTwo_kernel C r hr hC
  · simpa only [SpecializationCoinvariants.torusDifference] using
      markedCollapse_homologyThree_kernel C r hr hC
  · exact markedCollapse_homologyFour_kernel_eq_variation C r hr hC
  · exact markedCollapse_homologyHigher_kernel_eq_variation C r hr hC (n + 5) (by omega)

theorem markedCollapse_homology_eq_zero_iff (n : ℕ)
    (a : SingularHomology (ProductTorus 4) n) :
    singularHomologyMap (markedCollapse C r hr) n a = 0 ↔
      ∃ b : SingularHomology (ProductTorus 4) n,
        singularHomologyMap (torusMatrixMap M₀) n b - b = a := by
  change a ∈ LinearMap.ker (singularHomologyMap (markedCollapse C r hr) n) ↔ _
  rw [markedCollapse_homology_kernel C r hr hC n]
  rfl

/-- All degrees of the actual geometric calculation, with no supplied
surjectivity, representation, or kernel hypotheses. -/
theorem markedCollapse_singular_homology (n : ℕ) :
    Function.Surjective (singularHomologyMap (markedCollapse C r hr) n) ∧
      LinearMap.ker (singularHomologyMap (markedCollapse C r hr) n) =
        LinearMap.range (singularHomologyMap (torusMatrixMap M₀) n - LinearMap.id) :=
  ⟨markedCollapse_homology_surjective C r hr hC n,
    markedCollapse_homology_kernel C r hr hC n⟩

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
