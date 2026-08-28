import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationNegation
import Wikipedia.HopfProblem.CuspBoundaryGammaZeroWangNaturality
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspRegular
import Wikipedia.HopfProblem.ThreefoldHomologyCuspKernel

/-!
# Actual naturality for a cusp fibre-negation extension

The representative formula determines the native boundary map uniquely.
The genuine mapping-torus comparison then computes its Wang map. If this
map extends to the actual original cap, joint cap--Wang detection fixes
every original degree-three cap-kernel class. The extension itself is
constructed separately on the toric cap.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open SpecialPeriods SpecialPeriods.Threefold SingularMayerVietoris
open PeriodTorusHigherHomology ThreefoldOverlapMappingTorus MappingTorusHomology
open CuspBoundaryGammaZero CuspFamily ThreefoldHomologyCuspFibre

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

private theorem cuspMonodromy_negation (x : RealTorus₄) :
    flatNegation (monodromy none x) = monodromy none (flatNegation x) := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  change -cuspTorusHomeomorph 1 (standardLattice.mkQ v) =
    cuspTorusHomeomorph 1 (-standardLattice.mkQ v)
  rw [← map_neg standardLattice.mkQ v, cuspTorusHomeomorph_mkQ,
    cuspTorusHomeomorph_mkQ, map_neg, map_neg]

variable (N : C(Boundary none, Boundary none))
    (hN : ∀ (t : ℝ) (x : RealTorus₄),
      N (MappingTorus.mk (monodromy none) (t, x)) =
        MappingTorus.mk (monodromy none) (t, -x))

include hN

/-- The native representative formula identifies the actual map used by Wang naturality. -/
theorem cuspNegation_eq_mappingTorusMap :
    N = mappingTorusMap (monodromy none) (monodromy none) flatNegation
      cuspMonodromy_negation := by
  apply ContinuousMap.ext
  intro p
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective (monodromy none) p
  exact hN t x

/-- Naturality of the genuine Wang boundary, in the unchanged original sign convention. -/
theorem cuspNegation_wang (n : ℕ) (a : SingularHomology (Boundary none) (n + 1)) :
    wangBoundary (monodromy none) n (singularHomologyMap N (n + 1) a) =
      singularHomologyMap flatNegation n (wangBoundary (monodromy none) n a) := by
  rw [cuspNegation_eq_mappingTorusMap N hN]
  exact wangBoundary_mappingTorusMap (monodromy none) (monodromy none)
    flatNegation cuspMonodromy_negation n a

/-- The original whole cusp-to-regular map commutes with actual fibre negation. -/
theorem cuspNegation_regular_comp :
    (familyNegation Dsp).comp (boundaryToRegularFamily none) =
      (boundaryToRegularFamily none).comp N := by
  apply ContinuousMap.ext
  intro p
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective (monodromy none) p
  change familyNegation Dsp (boundaryToRegularFamily none
      (MappingTorus.mk (monodromy none) (t, x))) =
    boundaryToRegularFamily none (N (MappingTorus.mk (monodromy none) (t, x)))
  rw [hN]
  change familyNegation Dsp (boundaryToRegularFamily none
      (MappingTorus.mk Cusp.monodromy (t, x))) =
    boundaryToRegularFamily none (MappingTorus.mk Cusp.monodromy (t, -x))
  rw [Cusp.boundaryToRegularFamily_cusp_mk, Cusp.boundaryToRegularFamily_cusp_mk]
  rfl

variable (J : C(localPiece (some none), localPiece (some none)))
    (hJ : (boundaryToFilling none).comp N = J.comp (boundaryToFilling none))

include hJ
omit hN

/-- An actual extension to the original cap preserves its literal homology kernel. -/
theorem cuspNegation_cap_zero (a : SingularHomology (Boundary none) 3)
    (ha : boundaryFillingHomologyMap none 3 a = 0) :
    boundaryFillingHomologyMap none 3 (singularHomologyMap N 3 a) = 0 := by
  have h := congrArg
    (fun f : C(Boundary none, localPiece (some none)) => singularHomologyMap f 3) hJ
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h a
  change boundaryFillingHomologyMap none 3 (singularHomologyMap N 3 a) =
    singularHomologyMap J 3 (boundaryFillingHomologyMap none 3 a) at he
  rw [he, ha, map_zero]

include hN

/-- Joint detection by the original cap and Wang maps fixes every third-degree cap-kernel class. -/
theorem cuspNegation_capKernel_fixed
    (a : LinearMap.ker (boundaryFillingHomologyMap none 3)) :
    singularHomologyMap N 3 a.val = a.val := by
  apply cuspCap_wang_ext 2
  · exact (cuspNegation_cap_zero N J hJ a.val a.property).trans a.property.symm
  · rw [cuspNegation_wang N hN, flatNegation_homology_two]

/-- Its original regular-family image is fixed by the genuine regular involution. -/
theorem cuspNegation_capKernel_regular_fixed
    (a : LinearMap.ker (boundaryFillingHomologyMap none 3)) :
    singularHomologyMap (familyNegation Dsp) 3
        (boundaryRegularHomologyMap none 3 a.val) =
      boundaryRegularHomologyMap none 3 a.val := by
  have h := congrArg (fun f : C(Boundary none, (Dsp).Space) => singularHomologyMap f 3)
    (cuspNegation_regular_comp N hN)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h a.val
  change singularHomologyMap (familyNegation Dsp) 3
      (boundaryRegularHomologyMap none 3 a.val) =
    boundaryRegularHomologyMap none 3 (singularHomologyMap N 3 a.val) at he
  rw [he, cuspNegation_capKernel_fixed N hN J hJ]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
