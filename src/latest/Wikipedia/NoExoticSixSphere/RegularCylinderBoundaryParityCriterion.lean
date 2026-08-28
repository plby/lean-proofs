import Wikipedia.NoExoticSixSphere.CollaredBoundaryOperatorCoordinates
import Wikipedia.NoExoticSixSphere.BoundaryOperatorParityCriterion
import Wikipedia.NoExoticSixSphere.RegularCylinderFiberCollarCoordinates

/-!
# The original endpoint parity from the exact raw cylinder boundary operator

The ordered cylinder normal coordinates carry its equation frame exactly
to the original endpoint equation frame. Apply the fixed source and target
coordinate changes and the checked five-axis stabilization. The actual
collar derivative and its positive radial height then identify extension
of the original raw boundary operator with zero original sphere parity.
Both implications are proved; no disk extension is assumed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularCylinderFiber

open GLOrthonormalization Stiefel DiskBoundary CollaredDiskFrame

variable {m n : ℕ} (f : C(ℝ × Sphere m, Sphere n))
  (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f) (z : Sphere n)
  (hreg : ∀ p, f p = z → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))

theorem sphereParity_zero_iff_raw_boundaryOperator_extends (hd : m = n + 6)
    (f₀ : C(Sphere m, Sphere n)) (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg₀ : ∀ x, f₀ x = z → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    (U : Set ℝ) (hU : IsOpen U)
    (hconstant : ∀ c ∈ U, ∀ x, f (c, x) = f₀ x)
    (c : ℝ) (hc : c ∈ U) (a : Sphere m)
    (u : C(Sphere 3, {x : Sphere m // f₀ x = z})) :
    letI := regularFiberAtlas f hf z hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    letI := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
    let e₀ := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
    let a₀ := RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a
    ∀ (hu : ContMDiff (𝓡 3) (𝓡 6) ∞ u) (hi : Injective u)
      (hdu : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 6) u q))
      (F : Vector 4 → Vector (m + 1) × ℝ)
      (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
      (hb : ∀ q : Sphere 3, F q.val = (e₀.toFun (u q), 0))
      (R : Vector 4 ≃L[ℝ] Vector 4)
      (T : Sphere 3 → Vector 4 →L[ℝ] Vector (m + 2))
      (G : C(Sphere 3, Monomorphism.Space (m + 2) ((m + 2 - 7) + 4))),
      (∀ q, (G q).val = OperatorSum.operator
        ((normalFrame f hf z hreg 6 hd a).ambient
          ⟨(c, (u q).val), (hconstant c hc (u q).val).trans (u q).property⟩) (T q)) →
      (∀ q : Sphere 3, fderiv ℝ F q.val = (collarTargetCoordinates m).toContinuousLinearMap.comp
        ((T q).comp R.toContinuousLinearMap)) →
      (∀ q : Sphere 3, 0 < (fderiv ℝ F q.val q.val).2) →
      (e₀.sphereParity a₀ u hu hi hdu = 0 ↔ Extends G) := by
  let := regularFiberAtlas f hf z hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
  let e₀ := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
  let a₀ := RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a
  dsimp only
  intro hu hi hdu F hF hb R T G hG hD hheight
  let C : Vector (m + 2) ≃L[ℝ] (Vector (m + 1) × ℝ) := collarTargetCoordinates m
  let Q : Vector (m + 1 - 6) ≃L[ℝ] Vector (m + 2 - 7) := collarNormalCoordinates 6 hd
  let B : C(Sphere 3, Monomorphism.Space ((m + 1) + 6) (((m + 1 - 6) + 5) + 4)) :=
    (stabilizationMapCoordinates C Q R).comp G
  have hB (q : Sphere 3) : (B q).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector (m + 1)) ℝ).comp
        (a₀.ambient (u q))) (fderiv ℝ F q.val) := by
    dsimp only [B, ContinuousMap.comp_apply]
    have hv := stabilizationMapCoordinates_operator C Q R (G q) _ (T q) (hG q)
    have ha := normalFrame_collar_coordinates 6 hd f f₀ z a hconstant hf hf₀
      hreg hreg₀ hU c hc (u q)
    exact hv.trans (congrArg₂ combined ha (hD q).symm)
  exact (e₀.sphereParity_zero_iff_boundaryOperator_extends a₀ u hu hi hdu
    F hF hb B hB hheight).trans
      (extends_stabilizationMapCoordinates_iff (by omega) C Q R G)

end NoExoticSixSphere.RegularCylinderFiber
