import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthNormalEquations
import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthDiffeomorph
import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations

/-!
# A computed induced normal frame of the actual south Hopf fiber

The source is the standard S3 parametrizing the genuine south fiber.
The frame is induced by the checked ambient defining equations and
uses the orthogonal complement of the ORIGINAL inclusion derivative.
Its exact quaternion formula is proved, not chosen as a framing class.
Comparison with another target-chart framing is a separate obligation.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def southFiberAmbient (q : Sphere 3) : V 8 := (southFiberPoint q).val

theorem southNormalEquations_first_zero (x : V 8) (hx : southNormalEquations x = 0)
    (hh : polynomial x 0 < 0) : first x = 0 := by
  have ht := congrArg (fun p : SouthNormalModel ↦ p.snd) hx
  change tailQuaternion (polynomial x) = 0 at ht
  rw [polynomial, tailQuaternion_join] at ht
  have hm : first x * star (second x) = 0 :=
    (smul_eq_zero.mp ht).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hm with ha | hb
  · exact ha
  · have hb' : second x = 0 := star_eq_zero.mp hb
    change Quaternion.normSq (first x) - Quaternion.normSq (second x) < 0 at hh
    rw [hb', map_zero, sub_zero] at hh
    exact False.elim ((not_lt_of_ge
      (show 0 ≤ Quaternion.normSq (first x) from Quaternion.normSq_nonneg)) hh)

theorem southNormalEquations_isolate (x : V 8) :
    southNormalEquations x = 0 ∧ polynomial x 0 < 0 ↔
      ∃ q : Sphere 3, southFiberAmbient q = x := by
  constructor
  · rintro ⟨hzero, hhead⟩
    have hn := congrArg (fun p : SouthNormalModel ↦ p.fst) hzero
    change ‖x‖ ^ 2 - 1 = 0 at hn
    have hnorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
    let sx : Sphere 7 := ⟨x, mem_sphere_zero_iff_norm.mpr hnorm⟩
    have hs : sphereMap sx = south :=
      (sphereMap_eq_south_iff sx).mpr (southNormalEquations_first_zero x hzero hhead)
    refine ⟨southFiberInverse ⟨sx, hs⟩, ?_⟩
    exact congrArg Subtype.val (southFiberPoint_southFiberInverse ⟨sx, hs⟩)
  · rintro ⟨q, rfl⟩
    refine ⟨southNormalEquations_zero (southFiberPoint q) (first_southFiberPoint q), ?_⟩
    have hh := congrArg (fun y : Sphere 4 ↦ y.val 0) (sphereMap_southFiberPoint q)
    change polynomial (southFiberAmbient q) 0 = -1 at hh
    rw [hh]
    norm_num

theorem contMDiff_southFiberAmbient : ContMDiff (𝓡 3) 𝓘(ℝ, V 8) ∞ southFiberAmbient := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact southAxis.toContinuousLinearMap.contDiff.contMDiff.comp contMDiff_coe_sphere

theorem southFiberAmbient_differential_injective (q : Sphere 3) :
    Function.Injective (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient q) := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, V 4) ∞ (Subtype.val : Sphere 3 → V 4) := contMDiff_coe_sphere
  change Function.Injective (mfderiv (𝓡 3) 𝓘(ℝ, V 8)
    (southAxis.toContinuousLinearMap ∘ (Subtype.val : Sphere 3 → V 4)) q)
  rw [mfderiv_comp q southAxis.toContinuousLinearMap.differentiableAt.mdifferentiableAt
    (hs.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  exact southAxis.injective.comp (injective_mvfderiv_subtypeVal_sphere (n := 3) q)

theorem southNormalDimensions :
    Module.finrank ℝ (V 8) = Module.finrank ℝ SouthNormalModel + Module.finrank ℝ (V 3) := by
  have hp := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ).toLinearEquiv.finrank_eq
  rw [Module.finrank_prod, Module.finrank_self, Quaternion.finrank_eq_four] at hp
  rw [hp, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]

def southNormalFrame : SmoothRangeFrame (𝓡 3)
    (fun q : Sphere 3 ↦ (NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).rangeᗮ.starProjection) SouthNormalModel :=
  NormalFrameOfEquations.inducedFrame contMDiff_southFiberAmbient
    (fun _ ↦ contDiff_southNormalEquations.contDiffAt)
    (fun q ↦ southNormalEquations_zero (southFiberPoint q) (first_southFiberPoint q))
    (fun q ↦ southNormalEquations_surjective (southFiberPoint q) (first_southFiberPoint q))
    southFiberAmbient_differential_injective southNormalDimensions

theorem southNormalFrame_ambient (q : Sphere 3) :
    southNormalFrame.ambient q = southNormalLift (second (southFiberPoint q).val) := by
  change orthogonalRightInverse (fderiv ℝ southNormalEquations (southFiberPoint q).val) = _
  exact southNormalEquations_orthogonalRightInverse _ (first_southFiberPoint q)

theorem southNormalFrame_first (q : Sphere 3) (p : SouthNormalModel) :
    first (southNormalFrame.ambient q p) =
      (1 / 2 : ℝ) • (p.snd * Quaternion.linearIsometryEquivTuple.symm q.val) := by
  rw [southNormalFrame_ambient, first_southNormalLift, second_southFiberPoint]

theorem southNormalFrame_second (q : Sphere 3) (p : SouthNormalModel) :
    second (southNormalFrame.ambient q p) =
      (1 / 2 : ℝ) • (p.fst • Quaternion.linearIsometryEquivTuple.symm q.val) := by
  rw [southNormalFrame_ambient, second_southNormalLift, second_southFiberPoint]

theorem southNormalFrame_transverse (q : Sphere 3) (w : ℍ) :
    southNormalFrame.ambient q (WithLp.toLp 2 (0, (2 : ℝ) • w)) =
      firstAxis (w * Quaternion.linearIsometryEquivTuple.symm q.val) := by
  apply first_second_ext
  · rw [southNormalFrame_first, first_firstAxis]
    change (1 / 2 : ℝ) • (((2 : ℝ) • w) *
      Quaternion.linearIsometryEquivTuple.symm q.val) = _
    rw [smul_mul_assoc, smul_smul]
    norm_num
  · rw [southNormalFrame_second, second_firstAxis]
    change (1 / 2 : ℝ) • ((0 : ℝ) • Quaternion.linearIsometryEquivTuple.symm q.val) = 0
    rw [zero_smul, smul_zero]

end NoExoticSixSphere.QuaternionicHopf
