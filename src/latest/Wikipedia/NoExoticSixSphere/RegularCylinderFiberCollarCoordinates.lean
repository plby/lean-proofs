import Wikipedia.NoExoticSixSphere.RegularCylinderFiberNormalFrame
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding
import Wikipedia.NoExoticSixSphere.CylinderFrameCollar

/-!+# Ordered collar coordinates for the prescribed regular-fiber frames

The actual cylinder embedding puts time first. The quadratic collar puts
height last. This fixed change of target coordinates, together with the
ordered normal-model identifications, carries the original cylinder frame
exactly to the endpoint frame with zero height. No frame is replaced by
an independently chosen trivialization.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCylinderFiber

open Wikipedia.HopfProblem.DegreeCollapse EuclideanProduct

def collarTargetCoordinates (m : ℕ) : Vector (m + 2) ≃L[ℝ] (Vector (m + 1) × ℝ) :=
  (coordinates (m + 1)).symm.trans (ContinuousLinearEquiv.prodComm ℝ ℝ (Vector (m + 1)))

theorem collarTargetCoordinates_coordinates (m : ℕ) (p : ℝ × Vector (m + 1)) :
    collarTargetCoordinates m (coordinates (m + 1) p) = (p.2, p.1) := by
  change ((coordinates (m + 1)).symm (coordinates (m + 1) p)).swap = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

variable {m n : ℕ} (k : ℕ) (hd : m = n + k)

def collarNormalCoordinates : Vector (m + 1 - k) ≃L[ℝ] Vector ((m + 2) - (k + 1)) :=
  (RegularSphereFiber.normalCoordinates k hd).trans (normalModelCoordinates k hd).symm

theorem normalModelCoordinates_collarNormalCoordinates (v : Vector (m + 1 - k)) :
    normalModelCoordinates k hd (collarNormalCoordinates k hd v) =
      RegularSphereFiber.normalCoordinates k hd v :=
  (normalModelCoordinates k hd).apply_symm_apply _

variable (f : C(ℝ × Sphere m, Sphere n)) (f₀ : C(Sphere m, Sphere n))
  (b : Sphere n) (a : Sphere m) {U : Set ℝ}
  (hconstant : ∀ t ∈ U, ∀ x, f (t, x) = f₀ x)
  (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f)
  (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
  (hreg : ∀ p, f p = b → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))
  (hreg₀ : ∀ x, f₀ x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))

theorem normalFrame_collar_coordinates (hU : IsOpen U) (t : ℝ) (ht : t ∈ U)
    (x : {x : Sphere m // f₀ x = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    letI := regularFiberAtlas f₀ hf₀ b hreg₀ k (by simpa using hd)
    (collarTargetCoordinates m).toContinuousLinearMap.comp
      (((normalFrame f hf b hreg k hd a).ambient
        ⟨(t, x.val), (hconstant t ht x.val).trans x.property⟩).comp
          (collarNormalCoordinates k hd).toContinuousLinearMap) =
      (ContinuousLinearMap.inl ℝ (Vector (m + 1)) ℝ).comp
        ((RegularSphereFiber.frame f₀ hf₀ b hreg₀ k hd a).ambient x) := by
  let := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  let := regularFiberAtlas f₀ hf₀ b hreg₀ k (by simpa using hd)
  rw [normalFrame_ambient, normalOperator]
  have hc := CylinderFiberNormalFrame.normalFrame_ambient_on_collar f f₀ b a hconstant
    hf hf₀ hreg hreg₀ k hd hU t ht x
  apply ContinuousLinearMap.ext
  intro v
  change collarTargetCoordinates m ((headIsometry (m + 1))
    (((CylinderFiberNormalFrame.normalFrame f hf b hreg k hd a).ambient _)
      (normalModelCoordinates k hd (collarNormalCoordinates k hd v)))) = _
  rw [hc, normalModelCoordinates_collarNormalCoordinates]
  change collarTargetCoordinates m (coordinates (m + 1)
    (0, (SphereFiberNormalFrame.normalFrame f₀ hf₀ b hreg₀ k hd a).ambient x
      (RegularSphereFiber.normalCoordinates k hd v))) = _
  rw [collarTargetCoordinates_coordinates, SphereFiberNormalFrame.normalFrame_ambient,
    RegularSphereFiber.frame_ambient]
  rfl

end NoExoticSixSphere.RegularCylinderFiber
