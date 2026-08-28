import Wikipedia.NoExoticSixSphere.SphereEquationChartChange
import Wikipedia.NoExoticSixSphere.GeometricArfNormalCoordinates

/-!
# Actual regular-fiber normal frames and Arf invariants in alternative target charts

The new frame has exactly the orthogonal right inverse of the equations
formed with the supplied genuine target chart. The proved equation
comparison constructs it from the old frame by one fixed normal-coordinate
equivalence. The original embedding and native regular-fiber atlas remain
unchanged. In dimension six this preserves the original geometric Arf
invariant, without an orientation or orthogonality condition on the chart.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSphereFiber

open GLOrthonormalization CenteredChartCoordinates EuclideanEmbedding

def normalTargetChartChange {m n : ℕ} (b : Sphere n)
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)
    (hb : b ∈ c.source) (k : ℕ) (hd : m = n + k) :
    Vector (m + 1 - k) ≃L[ℝ] Vector (m + 1 - k) :=
  (normalCoordinates k hd).trans
    ((SphereLevelEquations.equationChange
      (differentialChange (modelChartPartialDiffeomorph (I := 𝓡 n) b) c b
        (mem_extChartAt_source b) hb)).symm.trans (normalCoordinates k hd).symm)

theorem normalTargetChartChange_cancel {m n : ℕ} (b : Sphere n)
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)
    (hb : b ∈ c.source) (k : ℕ) (hd : m = n + k) (v : Vector (m + 1 - k)) :
    normalCoordinates k hd (normalTargetChartChange b c hb k hd v) =
      (SphereLevelEquations.equationChange
        (differentialChange (modelChartPartialDiffeomorph (I := 𝓡 n) b) c b
          (mem_extChartAt_source b) hb)).symm (normalCoordinates k hd v) := by
  simp only [normalTargetChartChange, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))

def frameWithTargetChart (k : ℕ) (hd : m = n + k) (a : Sphere m)
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞) (hb : b ∈ c.source) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    SmoothRangeFrame (𝓡 k) (embedding f hf b hreg k hd).normalProjection
      (embedding f hf b hreg k hd).NormalModel := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  exact (frame f hf b hreg k hd a).recoordinateModel (normalTargetChartChange b c hb k hd)

theorem frameWithTargetChart_ambient (k : ℕ) (hd : m = n + k) (a : Sphere m)
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞) (hb : b ∈ c.source)
    (x : {x : Sphere m // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    (frameWithTargetChart f hf b hreg k hd a c hb).ambient x =
      (orthogonalRightInverse (fderiv ℝ
        (SphereFiberNormalFrame.equationsWithTargetChart f b c a) x.val.val)).comp
          (normalCoordinates k hd).toContinuousLinearMap := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  change ((frame f hf b hreg k hd a).recoordinateModel
    (normalTargetChartChange b c hb k hd)).ambient x = _
  rw [(frame f hf b hreg k hd a).recoordinateModel_ambient
      (normalTargetChartChange b c hb k hd) x,
    frame_ambient f hf b hreg k hd a x,
    SphereFiberNormalFrame.normalOperator_targetChart f hf b
      (modelChartPartialDiffeomorph (I := 𝓡 n) b) c (mem_extChartAt_source b) hb
      a x.val x.property (hreg x.val x.property),
    SphereFiberNormalFrame.equationsWithTargetChart_default]
  apply ContinuousLinearMap.ext
  intro v
  let L : WithLp 2 (ℝ × Vector n) →L[ℝ] Vector (m + 1) :=
    orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equations f b a) x.val.val)
  change L (normalCoordinates k hd (normalTargetChartChange b c hb k hd v)) =
    L ((SphereLevelEquations.equationChange
      (differentialChange (modelChartPartialDiffeomorph (I := 𝓡 n) b) c b
        (mem_extChartAt_source b) hb)).symm (normalCoordinates k hd v))
  exact congrArg L (normalTargetChartChange_cancel b c hb k hd v)

variable (hd : m = n + 6) (a : Sphere m)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞) (hb : b ∈ c.source)
  [SimplyConnectedSpace {x : Sphere m // f x = b}]
  (x x' : {x : Sphere m // f x = b})
  [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]
  [Subsingleton (π_ 2 {x : Sphere m // f x = b} x')]

theorem geometricArf_frameWithTargetChart :
    letI := regularFiberAtlas f hf b hreg 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hreg 6 _;
    letI := fiber_compact f b;
    ∀ r r' : (embedding f hf b hreg 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hreg 6 hd)
        (frameWithTargetChart f hf b hreg 6 hd a c hb) r' x' =
      GeometricArf.invariant (embedding f hf b hreg 6 hd) (frame f hf b hreg 6 hd a) r x := by
  let := regularFiberAtlas f hf b hreg 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hreg 6 (by simpa using hd)
  let := fiber_compact f b
  intro r r'
  exact GeometricArf.invariant_recoordinateModel (embedding f hf b hreg 6 hd)
    (frame f hf b hreg 6 hd a) r r' x x' (normalTargetChartChange b c hb 6 hd)

end NoExoticSixSphere.RegularSphereFiber
