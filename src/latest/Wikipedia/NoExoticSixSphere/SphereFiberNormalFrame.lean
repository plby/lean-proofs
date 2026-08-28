import Wikipedia.NoExoticSixSphere.SphereLevelEquations
import Wikipedia.NoExoticSixSphere.CenteredChartCoordinates
import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations
import Wikipedia.NoExoticSixSphere.RegularFiberManifold

/-!
# An actual Euclidean normal frame of a regular sphere fiber

Center a genuine target chart, extend radially in the source, and add the
unit-sphere equation. The orthogonal right inverse of these equations is a
smooth normal frame of the actual fiber inclusion into Euclidean space.
The source fiber keeps its constructed regular-fiber atlas. Its codimension
in the Euclidean ambient space is one more than the sphere-map codimension.
-/

open scoped Manifold ContDiff
open Module Function

namespace NoExoticSixSphere.SphereFiberNormalFrame

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)

local instance sourceDimension :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨finrank_euclideanSpace_fin⟩

noncomputable def equations (a : Sphere m) :
    EuclideanSpace ℝ (Fin (m + 1)) → WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)) :=
  SphereLevelEquations.equations a
    (CenteredChartCoordinates.coordinates f (modelChartPartialDiffeomorph (I := 𝓡 n) b) b)

theorem equations_zero (a x : Sphere m) (hx : f x = b) : equations f b a (x.val) = 0 := by
  rw [equations, SphereLevelEquations.equations_coe,
    CenteredChartCoordinates.coordinates_eq_zero f _ b hx]
  rfl

include hf in
theorem contDiffAt_equations (a x : Sphere m) (hx : f x = b) :
    ContDiffAt ℝ ∞ (equations f b a) x.val := by
  apply SphereLevelEquations.contDiffAt_equations (m := m)
  apply CenteredChartCoordinates.contMDiffAt_coordinates f _ b (hf x)
  rw [hx]
  exact mem_extChartAt_source b

include hf in
theorem surjective_fderiv_equations (a x : Sphere m) (hx : f x = b)
    (hreg : Surjective (mfderiv (𝓡 m) (𝓡 n) f x)) :
    Surjective (fderiv ℝ (equations f b a) x.val) := by
  have hc : f x ∈ (modelChartPartialDiffeomorph (I := 𝓡 n) b).source := by
    rw [hx]
    exact mem_extChartAt_source b
  apply SphereLevelEquations.surjective_fderiv_equations (m := m)
  · exact CenteredChartCoordinates.contMDiffAt_coordinates f _ b (hf x) hc
  · exact CenteredChartCoordinates.surjective_mfderiv_coordinates f _ b (hf x) hc hreg

def ambientInclusion : {x : Sphere m // f x = b} → EuclideanSpace ℝ (Fin (m + 1)) :=
  fun x ↦ x.val.val

variable (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (k : ℕ) (hd : m = n + k)

theorem contMDiff_ambientInclusion :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    ContMDiff (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ (ambientInclusion f b) := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  exact (contMDiff_coe_sphere (n := m) (m := ∞)).comp
    (regularFiber_contMDiff_subtype_val f hf b hreg k (by simpa using hd))

theorem injective_ambientDifferential (x : {x : Sphere m // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    Injective (NormalFrameOfEquations.ambientDifferential (𝓡 k) (ambientInclusion f b) x) := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  have hi := (regularFiber_contMDiff_subtype_val f hf b hreg k (by simpa using hd)).mdifferentiable
    (by simp) x
  have hj := (contMDiff_coe_sphere (n := m) (m := ∞)).mdifferentiable (by simp) x.val
  change Injective (mfderiv (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
    ((Subtype.val : Sphere m → EuclideanSpace ℝ (Fin (m + 1))) ∘
      (Subtype.val : {x : Sphere m // f x = b} → Sphere m)) x)
  rw [mfderiv_comp x hj hi]
  have hinj : Injective (mfderiv (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
      (Subtype.val : Sphere m → EuclideanSpace ℝ (Fin (m + 1))) x.val) := by
    intro v w hvw
    exact (injective_mvfderiv_subtypeVal_sphere (n := m) x.val) hvw
  exact hinj.comp (regularFiber_injective_mfderiv_subtype_val f hf b hreg k (by simpa using hd) x)

noncomputable def normalFrame (a : Sphere m) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    SmoothRangeFrame (𝓡 k)
      (fun x : {x : Sphere m // f x = b} ↦
        (NormalFrameOfEquations.ambientDifferential (𝓡 k)
          (ambientInclusion f b) x).rangeᗮ.starProjection)
      (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  apply NormalFrameOfEquations.inducedFrame
    (contMDiff_ambientInclusion f hf b hreg k hd)
    (fun x ↦ contDiffAt_equations f hf b a x.val x.property)
    (fun x ↦ equations_zero f b a x.val x.property)
    (fun x ↦ surjective_fderiv_equations f hf b a x.val x.property (hreg x.val x.property))
    (injective_ambientDifferential f hf b hreg k hd)
  have hdim := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (EuclideanSpace ℝ (Fin n))).toLinearEquiv.finrank_eq
  rw [hdim, finrank_prod, finrank_self, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin]
  omega

theorem normalFrame_ambient (a : Sphere m) (x : {x : Sphere m // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    (normalFrame f hf b hreg k hd a).ambient x =
      orthogonalRightInverse (fderiv ℝ (equations f b a) x.val.val) := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  apply ContinuousLinearMap.ext
  intro v
  rfl

end NoExoticSixSphere.SphereFiberNormalFrame
