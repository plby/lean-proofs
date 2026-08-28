import Wikipedia.NoExoticSixSphere.BallExteriorHomology
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology

/-!
# Actual local evaluation of a class supported on a closed ball

For every point of a closed ball, including its boundary, the original
evaluation map is an isomorphism on relative homology. The proof uses the
constructed exterior-to-puncture homology equivalence and the actual pair
sequences, then their native coefficient sequences.
-/

noncomputable section

open CategoryTheory Metric
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.ClosedBallLocalHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem point_mapsTo (R : ℝ) (x : E) (hx : x ∈ closedBall (0 : E) R) :
    Set.MapsTo (ContinuousMap.id E) (closedBall (0 : E) R)ᶜ ({x}ᶜ : Set E) := by
  intro y hy
  change y ≠ x
  intro he
  apply hy
  exact he.symm ▸ hx

omit [NormedSpace ℝ E] in
theorem restrictedPointMap_eq (R : ℝ) (x : E) (hx : x ∈ closedBall (0 : E) R) :
    RelativeSingularHomology.restrictedMap (ContinuousMap.id E) (point_mapsTo R x hx) =
      BallExterior.toPointPuncture R x (mem_closedBall_zero_iff.mp hx) := by
  ext y
  rfl

/-- The actual relative integral map associated with evaluation at a point of the ball. -/
def evaluationChain (R : ℝ) (x : E) (hx : x ∈ closedBall (0 : E) R) :
    RelativeSingularHomology.complex (closedBall (0 : E) R)ᶜ ⟶
      RelativeSingularHomology.complex ({x}ᶜ : Set E) :=
  RelativeSingularHomology.mapChain (ContinuousMap.id E) (point_mapsTo R x hx)

/-- The original integral evaluation map is a quasi-isomorphism, in all degrees. -/
theorem evaluationChain_quasiIso (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) : QuasiIso (evaluationChain R x hx) := by
  have h₁ : QuasiIso (singularChainMap
      (RelativeSingularHomology.restrictedMap (ContinuousMap.id E) (point_mapsTo R x hx))) := by
    rw [restrictedPointMap_eq R x hx]
    exact BallExterior.toPointPuncture_quasiIso R hR x (mem_closedBall_zero_iff.mp hx)
  have h₂ : QuasiIso (singularChainMap (ContinuousMap.id E)) := by
    rw [RelativeSingularHomology.chainMap_id]
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (RelativeSingularHomology.sequenceMap (ContinuousMap.id E) (point_mapsTo R x hx))
    (RelativeSingularHomology.sequence_shortExact (closedBall (0 : E) R)ᶜ)
    (RelativeSingularHomology.sequence_shortExact ({x}ᶜ : Set E)) h₁ h₂

/-- Native finite-cyclic coefficient reduction preserves this actual evaluation isomorphism. -/
theorem restrictChain_quasiIso (p : ℕ) (hp : p ≠ 0) (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) :
    QuasiIso (SupportedRelativeHomology.restrictChain (ModuleCat.of ℤ (ZMod p))
      (show {x} ⊆ closedBall (0 : E) R from Set.singleton_subset_iff.mpr hx)) :=
  RelativeCoefficients.mapChain_mod_quasiIso_of_integral p hp (ContinuousMap.id E)
    (point_mapsTo R x hx) (evaluationChain_quasiIso R hR x hx)

/-- Evaluation at every point of the actual ball is an equivalence of actual relative groups. -/
def evaluateEquiv (p : ℕ) (hp : p ≠ 0) (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) (n : ℕ) :
    SupportedRelativeHomology.Homology (ModuleCat.of ℤ (ZMod p)) (closedBall (0 : E) R) n ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p ({x}ᶜ : Set E) n := by
  let := restrictChain_quasiIso p hp R hR x hx
  exact (isoOfQuasiIsoAt (SupportedRelativeHomology.restrictChain (ModuleCat.of ℤ (ZMod p))
    (show {x} ⊆ closedBall (0 : E) R from Set.singleton_subset_iff.mpr hx)) n).toLinearEquiv

theorem evaluateEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) (n : ℕ) :
    (evaluateEquiv p hp R hR x hx n).toLinearMap =
      SupportedRelativeHomology.evaluate (ModuleCat.of ℤ (ZMod p)) (closedBall (0 : E) R)
        x hx n := rfl

end NoExoticSixSphere.ClosedBallLocalHomology
