import Wikipedia.HopfProblem.MappingTorusHomologyCoveringAmbient
import Wikipedia.HopfProblem.MappingTorusHomologyCoveringChains
import Wikipedia.HopfProblem.MappingTorusHomologyCoveringExtension

/-!
# The actual Wang boundary of a finite cyclic covering

For the literal map `[t,x] ↦ [mt,x]` from the circle product to the
mapping torus of `B.symm`, the signed Wang boundary is the finite homology
norm of `B` applied to the signed circle boundary.

The formula is proved on actual singular cycles. The positive circle is
subdivided into `2m` paths, their covering images are the actual charted
strip chains, and their common intersection boundary is the signed norm
pair. The genuine small-chain Mayer--Vietoris connecting formula then
computes the result. Actual circle-product exactness extends it to every
homology class; no covering or connecting naturality formula is assumed.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open MappingTorus MappingTorus.HomologyCover
open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)

omit [CompactSpace X] [T2Space X] [NeZero m] in
private theorem inverseMonodromy_period (h : B ^ m = 1) : B.symm ^ m = 1 := by
  rw [homeomorph_symm_pow_eq m B h m le_rfl, Nat.sub_self, pow_zero]

/-- The actual ambient small cycle is exactly the covering image of
the actual subdivided circle cross-product cycle. -/
theorem coverSmallCycle_productCover_eq (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.mapCycles (smallInclusion (U B.symm) (V B.symm)) (n + 1)
        (coverSmallCycle B.symm m (inverseMonodromy_period m B hB) n b) =
      ModuleHomology.mapCycles (singularChainMap (productCover m B hB)) (n + 1)
        (crossProductCycles Circle X n (arcSumCycle m) b) := by
  apply Subtype.ext
  rw [coverSmallCycle_ambient_sum_val, ModuleHomology.mapCycles_val]
  change (∑ k ∈ Finset.range m,
      (inducedChain (inclusionU B.symm) (n + 1) (uCrossChain B.symm k n b) +
        inducedChain (inclusionV B.symm) (n + 1) (vCrossChain B.symm k n b))) =
    inducedChain (productCover m B hB) (n + 1)
      (crossProductEdge Circle X n (arcSumChain m) b.1)
  simp only [arcSumChain, map_sum, LinearMap.sum_apply, map_add, LinearMap.add_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg₂ (· + ·)
    (uStrip_inclusion_crossProduct m B hB k n b.1)
    (vStrip_inclusion_crossProduct m B hB k n b.1)

/-- The charted small cycle represents the actual covering image of
the positive circle cross product, not merely an abstract class with
the same boundary. -/
theorem coverSmallCycle_productCover_class (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.cycleClass (singularComplex (Torus B.symm)) (n + 1)
        (ModuleHomology.mapCycles (smallInclusion (U B.symm) (V B.symm)) (n + 1)
          (coverSmallCycle B.symm m (inverseMonodromy_period m B hB) n b)) =
      productCoverHomology m B hB (n + 1)
        (positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b)) := by
  rw [coverSmallCycle_productCover_eq, positiveCircleCross_subdivision_cycleClass m n b]
  exact (ModuleHomology.homologyMap_cycleClass (singularChainMap (productCover m B hB))
    (n + 1) (crossProductCycles Circle X n (arcSumCycle m) b)).symm

/-- The two genuine connecting coordinates of a covered positive
cross product are the negative lower norm and positive upper norm. -/
theorem boundaryCoordinates_productCover_cross_cycleClass (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    boundaryCoordinates B.symm n
        (productCoverHomology m B hB (n + 1)
          (positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b))) =
      (-homologyNorm m B.symm n (ModuleHomology.cycleClass (singularComplex X) n b),
        homologyNorm m B.symm n (ModuleHomology.cycleClass (singularComplex X) n b)) := by
  rw [← coverSmallCycle_productCover_class]
  exact coverSmallCycle_boundaryCoordinates B.symm m (inverseMonodromy_period m B hB) n b

/-- The specified signed Wang convention gives the positive norm,
and finite order identifies the inverse-monodromy norm with that of `B`. -/
theorem wangBoundary_productCover_cross_cycleClass (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    wangBoundary B.symm n
        (productCoverHomology m B hB (n + 1)
          (positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b))) =
      homologyNorm m B n (ModuleHomology.cycleClass (singularComplex X) n b) := by
  rw [wangBoundary_apply, boundaryCoordinates_productCover_cross_cycleClass]
  simp only [neg_neg]
  rw [homologyNorm_symm m B n hB]

/-- The actual cyclic covering's Wang boundary on every positive
circle cross product, in every degree. -/
theorem wangBoundary_productCover_positiveCircleCross (n : ℕ) (b : SingularHomology X n) :
    wangBoundary B.symm n
        (productCoverHomology m B hB (n + 1) (positiveCircleCross X n b)) =
      homologyNorm m B n b := by
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) n b
  exact wangBoundary_productCover_cross_cycleClass m B hB n c

/-- Naturality for the actual finite cyclic covering: the boundary is
the actual homology norm times the actual circle boundary. -/
theorem wangBoundary_productCover (n : ℕ) :
    (wangBoundary B.symm n).comp (productCoverHomology m B hB (n + 1)) =
      (homologyNorm m B n).comp (circleBoundary X n) :=
  wangBoundary_productCover_eq_of_cross m B hB n (homologyNorm m B n)
    (wangBoundary_productCover_positiveCircleCross m B hB n)

theorem wangBoundary_productCover_apply (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    wangBoundary B.symm n (productCoverHomology m B hB (n + 1) a) =
      homologyNorm m B n (circleBoundary X n a) :=
  LinearMap.congr_fun (wangBoundary_productCover m B hB n) a

/-- The formula in terms of powers of the actual induced monodromy map. -/
theorem wangBoundary_productCover_sum_powers (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    wangBoundary B.symm n (productCoverHomology m B hB (n + 1) a) =
      ∑ k ∈ Finset.range m, ((monodromyHomologyMap B n) ^ k) (circleBoundary X n a) := by
  rw [wangBoundary_productCover_apply, homologyNorm_eq_sum_powers, LinearMap.sum_apply]

/-- Both raw connecting coordinates retain the exact lower-first sign. -/
theorem boundaryCoordinates_productCover (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    boundaryCoordinates B.symm n (productCoverHomology m B hB (n + 1) a) =
      (-homologyNorm m B n (circleBoundary X n a),
        homologyNorm m B n (circleBoundary X n a)) := by
  rw [boundaryCoordinates_eq_antidiagonal, wangBoundary_productCover_apply]

/-- The boundary image of the actual finite cover is exactly the
image of the actual finite monodromy norm. -/
theorem wangBoundary_productCover_range (n : ℕ) :
    LinearMap.range ((wangBoundary B.symm n).comp (productCoverHomology m B hB (n + 1))) =
      LinearMap.range (homologyNorm m B n) := by
  rw [wangBoundary_productCover]
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨circleBoundary X n a, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := circleBoundary_surjective X n a
    exact ⟨c, congrArg (homologyNorm m B n) hc⟩

end Wikipedia.HopfProblem.MappingTorusHomology.Covering
