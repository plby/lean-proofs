import Wikipedia.HopfProblem.CuspCentralHomologySpecializationEndsZero
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusThreeFour
import Wikipedia.HopfProblem.CuspCentralHomologyTopDegrees
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups
import Mathlib.RingTheory.FiniteType

/-!
# The actual marked specialization in the end degrees

Degree zero is identified by actual augmentation naturality. The proved
geometric degree-four surjectivity, together with the actual
rank-one integral homology groups, makes the actual marked collapse an
isomorphism in degree four. Its geometric monodromy invariance then forces
the actual top-degree monodromy map to be the identity. Above degree four,
the already proved vanishing of both actual homology groups gives the
actual-map equivalences directly.

Only positivity of the original radius and the original holomorphicity
hypothesis are used; no small-radius or drift assumption is supplied.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hr hC

/-- The original-radius geometric surjectivity in the exact source marking. -/
theorem markedCollapse_homologyFour_surjective :
    Function.Surjective (singularHomologyMap (markedCollapse C r hr) 4) :=
  markedCollapse_homology_surjective_of_product C r hr 4
    (productCollapse_homologyFour_surjective_of_holomorphic C r hr hC)

/-- The actual degree-four collapse is bijective between the two free rank-one groups. -/
theorem markedCollapse_homologyFour_bijective :
    Function.Bijective (singularHomologyMap (markedCollapse C r hr) 4) := by
  let := productTorus_homology_free 4 4
  let := productTorus_homology_finite 4 4
  let := centralSingularH4_free C r hr hC
  let := centralSingularH4_finite C r hr hC
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (singularHomologyMap (markedCollapse C r hr) 4)
    (markedCollapse_homologyFour_surjective C r hr hC)
  rw [productTorus_homology_finrank, centralSingularH4_finrank C r hr hC]
  simp

/-- The forward map is the actual singular-homology pushforward of the marked collapse. -/
def markedCollapseHomologyFourEquiv :
    SingularHomology (ProductTorus 4) 4 ≃ₗ[ℤ]
      SingularHomology (QuotientCentralFibre C r) 4 :=
  LinearEquiv.ofBijective (singularHomologyMap (markedCollapse C r hr) 4)
    (markedCollapse_homologyFour_bijective C r hr hC)

@[simp] theorem markedCollapseHomologyFourEquiv_apply
    (a : SingularHomology (ProductTorus 4) 4) :
    markedCollapseHomologyFourEquiv C r hr hC a =
      singularHomologyMap (markedCollapse C r hr) 4 a := rfl

theorem markedCollapse_homologyFour_kernel :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 4) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyFour_bijective C r hr hC).injective

@[simp] theorem markedCollapse_homologyFour_eq_zero_iff
    (a : SingularHomology (ProductTorus 4) 4) :
    singularHomologyMap (markedCollapse C r hr) 4 a = 0 ↔ a = 0 :=
  (markedCollapseHomologyFourEquiv C r hr hC).map_eq_zero_iff

/-- The actual top monodromy is identity, proved by geometric invariance and injectivity. -/
theorem markedMonodromy_homologyFour :
    singularHomologyMap (torusMatrixMap M₀) 4 = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (markedCollapse_homologyFour_bijective C r hr hC).injective
  exact markedCollapse_homology_invariant C r hr 4 a

theorem markedMonodromy_homologyFour_variation_zero :
    singularHomologyMap (torusMatrixMap M₀) 4 - LinearMap.id = 0 := by
  rw [markedMonodromy_homologyFour C r hr hC, sub_self]

theorem markedMonodromy_homologyFour_variation_range :
    LinearMap.range (singularHomologyMap (torusMatrixMap M₀) 4 - LinearMap.id) = ⊥ := by
  rw [markedMonodromy_homologyFour_variation_zero C r hr hC, LinearMap.range_zero]

/-- Both the actual degree-four specialization kernel and the variation image are zero. -/
theorem markedCollapse_homologyFour_kernel_eq_variation :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 4) =
      LinearMap.range (singularHomologyMap (torusMatrixMap M₀) 4 - LinearMap.id) := by
  rw [markedCollapse_homologyFour_kernel C r hr hC,
    markedMonodromy_homologyFour_variation_range C r hr hC]

/-! ## The actual maps above degree four -/

theorem markedCollapse_homologyHigher_bijective (n : ℕ) (hn : 4 < n) :
    Function.Bijective (singularHomologyMap (markedCollapse C r hr) n) := by
  let := productTorus_homology_subsingleton_of_lt hn
  let := centralSingularHomology_subsingleton_of_four_lt C r hr hC hn
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-- The equivalence in a vanishing degree still has the actual collapse as its forward map. -/
def markedCollapseHomologyHigherEquiv (n : ℕ) (hn : 4 < n) :
    SingularHomology (ProductTorus 4) n ≃ₗ[ℤ]
      SingularHomology (QuotientCentralFibre C r) n :=
  LinearEquiv.ofBijective (singularHomologyMap (markedCollapse C r hr) n)
    (markedCollapse_homologyHigher_bijective C r hr hC n hn)

@[simp] theorem markedCollapseHomologyHigherEquiv_apply
    (n : ℕ) (hn : 4 < n) (a : SingularHomology (ProductTorus 4) n) :
    markedCollapseHomologyHigherEquiv C r hr hC n hn a =
      singularHomologyMap (markedCollapse C r hr) n a := rfl

theorem markedCollapse_homologyHigher_zero (n : ℕ) (hn : 4 < n) :
    singularHomologyMap (markedCollapse C r hr) n = 0 := by
  let := centralSingularHomology_subsingleton_of_four_lt C r hr hC hn
  apply LinearMap.ext
  intro a
  exact Subsingleton.elim _ _

theorem markedCollapse_homologyHigher_kernel (n : ℕ) (hn : 4 < n) :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) n) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyHigher_bijective C r hr hC n hn).injective

theorem markedCollapse_homologyHigher_kernel_eq_variation (n : ℕ) (hn : 4 < n) :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) n) =
      LinearMap.range (singularHomologyMap (torusMatrixMap M₀) n - LinearMap.id) := by
  let := productTorus_homology_subsingleton_of_lt hn
  have hvariation : singularHomologyMap (torusMatrixMap M₀) n - LinearMap.id = 0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  rw [markedCollapse_homologyHigher_kernel C r hr hC n hn, hvariation, LinearMap.range_zero]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
