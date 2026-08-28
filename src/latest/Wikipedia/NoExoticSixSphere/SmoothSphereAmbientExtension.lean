import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth ambient extension of a Euclidean-valued sphere map

Radial retraction extends the original map away from the origin. A smooth
cutoff makes it zero near the origin and leaves the entire unit sphere
unchanged. No extension into a nonlinear target is asserted here.
-/

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SmoothSphereAmbient

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def cutoff (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1))) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def extension (b : Sphere n) (f : Sphere n → F) (x : EuclideanSpace ℝ (Fin (n + 1))) : F :=
  (1 - cutoff n x) • f (SphereRadialRetraction.retract b x)

theorem extension_coe (b : Sphere n) (f : Sphere n → F) (s : Sphere n) :
    extension b f s.val = f s := by
  have hχ : cutoff n s.val = 0 := by
    apply (cutoff n).zero_of_le_dist
    change (1 / 2 : ℝ) ≤ dist s.val 0
    rw [dist_zero_right, ClosedHemisphere.unit_norm]
    norm_num
  rw [extension, hχ, sub_zero, one_smul, SphereRadialRetraction.retract_coe]

theorem contDiff_extension (b : Sphere n) (f : Sphere n → F)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ f) : ContDiff ℝ ∞ (extension b f) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have he : extension b f =ᶠ[𝓝 0] (fun _ ↦ (0 : F)) := by
      filter_upwards [(cutoff n).eventuallyEq_one] with y hy
      simp only [extension, hy, Pi.one_apply, sub_self, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hr : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 n) ∞
        (SphereRadialRetraction.retract b) x :=
      SphereRadialRetraction.contMDiffAt_retract b hx
    have hcomp : ContDiffAt ℝ ∞ (fun y ↦ f (SphereRadialRetraction.retract b y)) x :=
      (hf.contMDiffAt.comp x hr).contDiffAt
    exact (contDiffAt_const.sub (cutoff n).contDiff.contDiffAt).smul hcomp

end NoExoticSixSphere.SmoothSphereAmbient
