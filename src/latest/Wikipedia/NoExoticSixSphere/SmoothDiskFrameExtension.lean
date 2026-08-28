import Wikipedia.NoExoticSixSphere.RelativePartialFrameSmoothing
import Wikipedia.NoExoticSixSphere.FrameBoundaryInterpolation
import Wikipedia.NoExoticSixSphere.SmoothSphereAmbientExtension
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart
import Mathlib.Analysis.Complex.Tietze

/-!
# Smooth partial-frame extension with exact sphere boundary values

Extend the continuous ambient operator family from the closed disk by Tietze.
Install the smooth radial boundary extension on a neighborhood of the sphere
without losing projected injectivity. Relative approximation and rectangular
normalization then give a smooth frame in the original subspaces, retaining
the entire original boundary frame exactly.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N n : ℕ}

theorem exists_smoothDiskFrame_extension
    (P : Vector 4 → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector 4) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P x)
    (a : C(NoExoticSixSphere.Sphere 3, Space N n))
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector n →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (A : C(Disk (E := Vector 4), Space N n))
    (hAr : ∀ x, (A x).val.range ≤ (P x.val).range)
    (hAb : ∀ s, A (boundaryToDisk s) = a s) :
    ∃ T : Vector 4 → Vector n →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (P x).range) ∧
      ∀ s, T s.val = (a s).val := by
  let Ac : C(Disk (E := Vector 4), Vector n →L[ℝ] Vector N) :=
    ⟨fun x ↦ (A x).val, continuous_subtype_val.comp A.continuous⟩
  obtain ⟨A₀, hA₀⟩ := Ac.exists_restrict_eq isClosed_closedBall
  have heA (x : Disk (E := Vector 4)) : A₀ x.val = (A x).val :=
    ContinuousMap.congr_fun hA₀ x
  let F : C(Vector 4, Vector n →L[ℝ] Vector N) :=
    ⟨SmoothSphereAmbient.extension (spherePole 3) (fun s ↦ (a s).val),
      (SmoothSphereAmbient.contDiff_extension (spherePole 3) _ has).continuous⟩
  have hFs : ContDiff ℝ ∞ F :=
    SmoothSphereAmbient.contDiff_extension (spherePole 3) _ has
  have hF (s : NoExoticSixSphere.Sphere 3) : F s.val = (a s).val :=
    SmoothSphereAmbient.extension_coe (spherePole 3) (fun s ↦ (a s).val) s
  have hFA : EqOn F A₀ (sphere (0 : Vector 4) 1) := by
    intro x hx
    let s : NoExoticSixSphere.Sphere 3 := ⟨x, hx⟩
    exact (hF s).trans ((congrArg Subtype.val (hAb s)).symm.trans
      (heA (boundaryToDisk s)).symm)
  have hPA (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (P x).comp (A₀ x) = A₀ x := by
    rw [heA ⟨x, hx⟩]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P x) (hP x hx)
      ⟨(A ⟨x, hx⟩).val w, hAr ⟨x, hx⟩ ⟨w, rfl⟩⟩
  have hAi (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      Function.Injective ((P x).comp (A₀ x)) := by
    rw [hPA x hx, heA ⟨x, hx⟩]
    exact Stiefel.injective (A ⟨x, hx⟩)
  have hPc : ContinuousOn P (closedBall (0 : Vector 4) 1) :=
    fun x hx ↦ (hPs x hx).continuousAt.continuousWithinAt
  obtain ⟨B, hBi, U, hU, hSU, hBF⟩ := exists_boundaryInterpolation
    (isCompact_closedBall (0 : Vector 4) 1) (isCompact_sphere (0 : Vector 4) 1)
    A₀ F P hPc hAi hFA
  have hBA : EqOn B A₀ (sphere (0 : Vector 4) 1) :=
    fun x hx ↦ (hBF (hSU hx)).trans (hFA hx)
  have hBP (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ sphere 0 1) :
      (P x).comp (B x) = B x := by rw [hBA hx.2, hPA x hx.1]
  have hBn (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ sphere 0 1)
      (w : Vector n) : ‖B x w‖ = ‖w‖ := by
    rw [hBA hx.2, heA ⟨x, hx.1⟩]
    exact (A ⟨x, hx.1⟩).property w
  have hBs : ContDiffOn ℝ ∞ B U := hFs.contDiffOn.congr hBF
  obtain ⟨T, hTs, hTn, hTr, hT⟩ := exists_smoothPartialFrame_rel
    (isCompact_closedBall (0 : Vector 4) 1) B B.continuous P hPs hBi hBP hBn
    isClosed_sphere (hU.mem_nhdsSet.mpr hSU) hBs
  refine ⟨T, hTs, hTn, hTr, ?_⟩
  intro s
  exact (hT ⟨sphere_subset_closedBall s.property, s.property⟩).trans
    ((hBF (hSU s.property)).trans (hF s))

end NoExoticSixSphere.Stiefel
