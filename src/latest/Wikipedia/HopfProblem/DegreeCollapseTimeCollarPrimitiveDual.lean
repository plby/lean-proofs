import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenDualEvaluation
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarSplitting
import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeForgetZero
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic

/-!
# Integral duals of primitive classes in the actual positive half

The actual half-sum equivalence extends an integral functional to the
closed manifold. Complementary cap evaluation supplies a fourth-homology
class there. Splitting that class and using zero restriction on the
negative half retains an actual positive-half dual. Third homology may
be infinite, and fourth homology is not assumed to vanish.
-/

noncomputable section

open CategoryTheory Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree NoExoticSixSphere

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def halfHomologyProjection (k : ℕ) [Subsingleton (SingularHomology B k)]
    [Subsingleton (SingularHomology B (k + 1))] :
    SingularHomology M (k + 1) →ₗ[ℤ] SingularHomology (NonnegativeHalf t) (k + 1) := by
  let e := LinearEquiv.ofBijective (C.halvesHomologySum (k + 1))
    (C.halvesHomologySum_bijective k)
  let f := (AddMonoidHom.fst (SingularHomology (NonnegativeHalf t) (k + 1))
    (SingularHomology (NonnegativeHalf (fun p ↦ -t p)) (k + 1))).comp e.symm.toAddMonoidHom
  exact ConstantSheafSingularComparison.addHomToIntLinearMap f

theorem halfHomologyProjection_inclusion (k : ℕ) [Subsingleton (SingularHomology B k)]
    [Subsingleton (SingularHomology B (k + 1))]
    (c : SingularHomology (NonnegativeHalf t) (k + 1)) :
    C.halfHomologyProjection k (singularHomologyMap (halfInclusion t) (k + 1) c) = c := by
  let e := LinearEquiv.ofBijective (C.halvesHomologySum (k + 1))
    (C.halvesHomologySum_bijective k)
  have he : e (c, 0) = singularHomologyMap (halfInclusion t) (k + 1) c := by
    change C.halvesHomologySum (k + 1) (c, 0) = _
    rw [halvesHomologySum_apply, map_zero, add_zero]
  change (e.symm (singularHomologyMap (halfInclusion t) (k + 1) c)).1 = c
  rw [← he, LinearEquiv.symm_apply_apply]

theorem supported_pullback_negative_zero (K : Set M)
    (hK : ∀ p ∈ K, 0 < t p) (k : ℕ)
    (a : IntegralSupportedCohomology.Cohomology K k) :
    singularCohomologyPullback (halfInclusion (fun p ↦ -t p)) k
      (IntegralSupportedCohomology.toAbsolute K k a) = 0 := by
  apply RelativeIntegralCap.cohomologyForget_pullback_zero Kᶜ
    (halfInclusion (fun p ↦ -t p)) _ k a
  intro p hp
  have hpos := hK p.val hp
  have hnonpos : t p.val ≤ 0 := neg_nonneg.mp p.property
  exact (not_lt_of_ge hnonpos) hpos

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

theorem exists_half_dual_evaluation
    (σ : SingularHomology (NonnegativeHalf t) 3 →ₗ[ℤ] ℤ) :
    ∃ z : SingularHomology (NonnegativeHalf t) 4, ∀ b : SingularCohomology M 4,
      singularCohomologyPullback (halfInclusion (fun p ↦ -t p)) 4 b = 0 →
      singularEvaluation (NonnegativeHalf t) 4
        (singularCohomologyPullback (halfInclusion t) 4 b) z =
        σ (C.halfHomologyProjection 2
          (IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl b)) := by
  let φ := σ.comp (C.halfHomologyProjection 2)
  obtain ⟨z, hz⟩ := IntegralSevenDuality.exists_dual_evaluation (E := E) M φ
  obtain ⟨⟨x, y⟩, hxy⟩ := (C.halvesHomologySum_bijective 3).2 z
  refine ⟨x, ?_⟩
  intro b hb
  have he := hz b
  rw [← hxy, halvesHomologySum_apply, map_add,
    ← singularEvaluation_naturality (halfInclusion t),
    ← singularEvaluation_naturality (halfInclusion (fun p ↦ -t p)), hb,
    map_zero, LinearMap.zero_apply, add_zero] at he
  exact he

include C in
theorem exists_unit_half_dual_of_primitive
    (σ : SingularHomology (NonnegativeHalf t) 3 →ₗ[ℤ] ℤ)
    (c : SingularHomology (NonnegativeHalf t) 3) (hc : σ c = 1)
    (b : SingularCohomology M 4)
    (hb : singularCohomologyPullback (halfInclusion (fun p ↦ -t p)) 4 b = 0)
    (hcap : IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl b =
      singularHomologyMap (halfInclusion t) 3 c) :
    ∃ z : SingularHomology (NonnegativeHalf t) 4,
      singularEvaluation (NonnegativeHalf t) 4
        (singularCohomologyPullback (halfInclusion t) 4 b) z = 1 := by
  obtain ⟨z, hz⟩ := C.exists_half_dual_evaluation (E := E) σ
  refine ⟨z, (hz b hb).trans ?_⟩
  rw [hcap, halfHomologyProjection_inclusion, hc]

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
