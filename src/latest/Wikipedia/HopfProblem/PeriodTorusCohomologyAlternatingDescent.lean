import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingEta
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantIndices

/-!
# Genuine integral descent of the distinguished class through elliptic covers

The already proved integral image criterion shows that the index one
or two kills the actual degree-two descent obstruction.  Consequently
the original finite period cover has a unique native cohomology class
pulling back to `η` in the order-three case, and to `2 η` in the
order-four case.  The evaluation formula below uses the actual images
of the positive period-loop two-cycles under that original cover.

This does not assert that the factor two is necessary for this particular
class, nor identify either class with a first Chern class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomologyPontryagin Elliptic Elliptic.HigherHomology

/-- The actual invariant-cohomology image contains the index multiple of every invariant class. -/
theorem invariantH2_index_smul_mem_range (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2) :
    (fibreNormIndex j : ℤ) • a ∈ LinearMap.range
      (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) 2) := by
  rw [periodCoverCohomologyToInvariants_h2_mem_range]
  refine ⟨periodInvariantCohomologyH2Coordinates j p a 1 -
    periodCoverDeckDualH2Shear j p * periodInvariantCohomologyH2Coordinates j p a 0, ?_⟩
  rw [map_zsmul]
  simp only [Pi.smul_apply, zsmul_eq_mul]
  norm_cast
  ring

/-- A unique actual cohomology class descends the indicated multiple of the normalized η. -/
theorem existsUnique_ellipticEtaClass (j : Kind) (p : FixedPeriod j) :
    ∃! a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) 2,
      singularCohomologyPullback (periodCover j p j.twist (mainTwist_admissible j)) 2 a =
        (fibreNormIndex j : ℤ) • etaClass p.val := by
  obtain ⟨a, ha⟩ := invariantH2_index_smul_mem_range j p
    (etaInvariantClass j p j.twist (mainTwist_admissible j))
  have ha' : singularCohomologyPullback
      (periodCover j p j.twist (mainTwist_admissible j)) 2 a =
        (fibreNormIndex j : ℤ) • etaClass p.val := by
    exact congrArg Subtype.val ha
  refine ⟨a, ha', ?_⟩
  intro b hb
  exact periodCover_cohomology_injective j p 2 (hb.trans ha'.symm)

/-- The unique genuinely descended native class, using the actual finite period covering. -/
def ellipticEtaClass (j : Kind) (p : FixedPeriod j) :
    SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) 2 :=
  (existsUnique_ellipticEtaClass j p).exists.choose

theorem ellipticEtaClass_pullback (j : Kind) (p : FixedPeriod j) :
    singularCohomologyPullback (periodCover j p j.twist (mainTwist_admissible j)) 2
      (ellipticEtaClass j p) = (fibreNormIndex j : ℤ) • etaClass p.val :=
  (existsUnique_ellipticEtaClass j p).exists.choose_spec

/-- No multiple is needed to descend η through the actual order-three period cover. -/
theorem ellipticEtaClass_three_pullback (p : FixedPeriod .three) :
    singularCohomologyPullback
      (periodCover .three p Kind.three.twist (mainTwist_admissible .three)) 2
        (ellipticEtaClass .three p) = etaClass p.val := by
  simpa only [fibreNormIndex, Nat.cast_one, one_smul] using ellipticEtaClass_pullback .three p

/-- Twice η descends through the actual order-four cover without a remaining parity assumption. -/
theorem ellipticEtaClass_four_pullback (p : FixedPeriod .four) :
    singularCohomologyPullback
      (periodCover .four p Kind.four.twist (mainTwist_admissible .four)) 2
        (ellipticEtaClass .four p) = (2 : ℤ) • etaClass p.val :=
  ellipticEtaClass_pullback .four p

/-- Evaluation on the actual covered images of positive period-loop products retains its sign. -/
theorem ellipticEtaClass_evaluate_periodLoops (j : Kind) (p : FixedPeriod j) (x y : Lattice) :
    singularEvaluation (Surface j p j.twist (mainTwist_admissible j)) 2
      (ellipticEtaClass j p)
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 2
        (product11 p.val.Torus (loopHomologyClass (p.val.periodLoop x))
          (loopHomologyClass (p.val.periodLoop y)))) =
      (fibreNormIndex j : ℤ) *
        (x 1 * y 2 - x 2 * y 1 + 6 * (x 0 * y 3 - x 3 * y 0)) := by
  rw [← singularEvaluation_naturality, ellipticEtaClass_pullback, map_zsmul]
  simp only [LinearMap.smul_apply, zsmul_eq_mul, etaClass_evaluate_periodLoops]
  norm_cast

/-- The descended native class is nonzero on the actual surface. -/
theorem ellipticEtaClass_ne_zero (j : Kind) (p : FixedPeriod j) : ellipticEtaClass j p ≠ 0 := by
  intro h
  have hp := ellipticEtaClass_pullback j p
  rw [h, map_zero] at hp
  have hz : (fibreNormIndex j : ℤ) • etaClass p.val = (0 : ℤ) • etaClass p.val := by
    simpa only [zero_smul] using hp.symm
  have hd := etaClass_zsmul_injective p.val hz
  have hpos : (0 : ℤ) < fibreNormIndex j := by exact_mod_cast fibreNormIndex_pos j
  omega

/-- The order-three descended class is primitive in the actual surface cohomology. -/
theorem ellipticEtaClass_three_primitive (p : FixedPeriod .three) (r : ℤ)
    (a : SingularCohomology
      (Surface .three p Kind.three.twist (mainTwist_admissible .three)) 2)
    (ha : r • a = ellipticEtaClass .three p) : IsUnit r := by
  apply etaClass_primitive p.val r
    (singularCohomologyPullback
      (periodCover .three p Kind.three.twist (mainTwist_admissible .three)) 2 a)
  have h := congrArg (singularCohomologyPullback
    (periodCover .three p Kind.three.twist (mainTwist_admissible .three)) 2) ha
  simpa only [map_zsmul, ellipticEtaClass_three_pullback] using h

end Wikipedia.HopfProblem.PeriodTorusCohomology
