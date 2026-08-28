import Wikipedia.HopfProblem.CuspCentralHomologySpecializationThreeFourNaturality
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationOverlap
import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverMayerVietoris
import Wikipedia.HopfProblem.CuspCentralHomologyMiddleMaps
import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesMayerVietoris

/-!
# Actual cusp specialization is surjective in degrees three and four

The target connecting map is injective because both actual cover pieces
have zero homology in these degrees. Its image lies in the actual
phase-projection kernel. The proved source connecting lift supplies a
source class for every such kernel element. The actual overlap map is
the identity on homology in the displayed phase-circle coordinates, and
actual Mayer–Vietoris naturality completes the lift.

No desired overlap identification, connecting-map formula, surjectivity,
or model exact sequence is taken as a hypothesis.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology
open SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

/-- The actual product collapse surjects in every degree at least three.
The nonzero target cases are exactly degrees three and four. -/
theorem productCollapse_homology_three_add_surjective (n : ℕ) :
    Function.Surjective (singularHomologyMap (productCollapse C ε hε) (n + 3)) := by
  let a : ℝ := 1 / 2
  have ha : 0 ≤ a := by norm_num [a]
  have ha1 : a < 1 := by norm_num [a]
  let U := outerRegion C ε hε a
  let V := innerRegion C ε hε
  let hU := outerRegion_isOpen C ε hε hε1 hC hR a
  let hV := innerRegion_isOpen C ε hε hε1 hC hR
  let hc := outerRegion_union_innerRegion C ε hε a ha1
  let δT := connectingHomomorphism U V hU hV hc (n + 2)
  let δS := connectingHomomorphism (BaseCover.phaseOuterRegion a) BaseCover.phaseInnerRegion
    (BaseCover.phaseOuterRegion_isOpen a) BaseCover.phaseInnerRegion_isOpen
    (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1) (n + 2)
  let eT := middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 2)
  let : Subsingleton (SingularHomology U (n + 3)) :=
    outerRegion_homology_subsingleton C ε hε hε1 hC hR a ha ha1 n
  let : Subsingleton (SingularHomology V (n + 3)) :=
    innerRegion_homology_subsingleton C ε hε hε1 hC hR n
  have hδT : Function.Injective δT :=
    coverConnecting_injective_of_vanishing U V hU hV hc (n + 2)
  intro b
  have hk : δT b ∈ LinearMap.ker (leftHomologyMap U V (n + 2)) := by
    change leftHomologyMap U V (n + 2) (δT b) = 0
    have h := LinearMap.congr_fun (connectingHomomorphism_comp_left U V hU hV hc (n + 2)) b
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hx : singularHomologyMap
      (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 2)
      (eT (δT b)) = 0 :=
    (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 (n + 1) (δT b)).mp hk
  obtain ⟨s, hs⟩ := BaseCover.phaseConnecting_lift a ha ha1 (n + 1) (eT (δT b)) hx
  refine ⟨s, hδT (eT.injective ?_)⟩
  have hnat : singularHomologyMap (SpecializationCover.overlapMap C ε hε a) (n + 2)
      (δS s) = δT (singularHomologyMap (productCollapse C ε hε) (n + 3) s) :=
    productCollapse_connecting_naturality C ε hε hε1 hC hR a ha1 (n + 2) s
  calc
    eT (δT (singularHomologyMap (productCollapse C ε hε) (n + 3) s)) =
        eT (singularHomologyMap (SpecializationCover.overlapMap C ε hε a) (n + 2)
          (δS s)) := congrArg eT hnat.symm
    _ = BaseCover.phaseOverlapHomologyEquiv a ha ha1 (n + 2) (δS s) :=
      SpecializationCover.overlapMap_homology_coordinates C ε hε hε1 hC hR
        a ha ha1 (n + 2) (δS s)
    _ = eT (δT b) := hs

/-- Surjectivity of the actual specialization map on integral third homology. -/
theorem productCollapse_homologyThree_surjective :
    Function.Surjective (singularHomologyMap (productCollapse C ε hε) 3) :=
  productCollapse_homology_three_add_surjective C ε hε hε1 hC hR 0

/-- Surjectivity of the actual specialization map on integral fourth homology. -/
theorem productCollapse_homologyFour_surjective :
    Function.Surjective (singularHomologyMap (productCollapse C ε hε) 4) :=
  productCollapse_homology_three_add_surjective C ε hε hε1 hC hR 1

theorem productCollapse_homologyThree_range :
    LinearMap.range (singularHomologyMap (productCollapse C ε hε) 3) = ⊤ :=
  LinearMap.range_eq_top.mpr (productCollapse_homologyThree_surjective C ε hε hε1 hC hR)

theorem productCollapse_homologyFour_range :
    LinearMap.range (singularHomologyMap (productCollapse C ε hε) 4) = ⊤ :=
  LinearMap.range_eq_top.mpr (productCollapse_homologyFour_surjective C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspCentralHomology
