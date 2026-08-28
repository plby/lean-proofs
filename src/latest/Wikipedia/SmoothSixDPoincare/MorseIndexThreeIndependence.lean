import Wikipedia.SmoothSixDPoincare.MorseIndexThreeRelation

/-!
# An index-three attaching relation has infinite order when upper third homology vanishes

Exactness identifies the kernel of the original attaching-sphere map with
the image of upper third homology. Its vanishing makes that original map
injective, so no nonzero integer multiple of the actual attaching class is zero.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  [Subsingleton (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 3)]

theorem coreBoundary_two_injective_of_upper (hf : Continuous f) :
    Injective (d.coreBoundaryHomologyMap 2) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_attachingSphere hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.morseConnectingMap hf 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

theorem indexThreeAttaching_zsmul_eq_zero (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) (z : ℤ)
    (hz : z • d.indexThreeAttachingClass hindex = 0) : z = 0 := by
  have hcore : d.coreBoundaryHomologyMap 2
      (z • (d.indexThreeBoundaryEquiv hindex).symm 1) = 0 := by
    rw [map_zsmul]
    exact hz
  have hs : z • (d.indexThreeBoundaryEquiv hindex).symm 1 = 0 :=
    d.coreBoundary_two_injective_of_upper hf (hcore.trans (map_zero _).symm)
  have h := congrArg (d.indexThreeBoundaryEquiv hindex) hs
  rw [map_zsmul, LinearEquiv.apply_symm_apply, map_zero, zsmul_eq_mul, mul_one] at h
  simpa using h

theorem indexThreeAttaching_smul_eq_zero (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) (z : ℤ)
    (hz : (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2).isModule.smul z
      (d.indexThreeAttachingClass hindex) = 0) : z = 0 :=
  d.indexThreeAttaching_zsmul_eq_zero hf hindex z
    ((int_smul_eq_zsmul
      (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2).isModule z
        (d.indexThreeAttachingClass hindex)).symm.trans hz)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
