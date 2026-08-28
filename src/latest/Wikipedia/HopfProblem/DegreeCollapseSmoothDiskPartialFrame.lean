import Wikipedia.HopfProblem.DegreeCollapseDiskPartialFrameExtension
import Wikipedia.NoExoticSixSphere.SmoothDiskFrameExtension

/-!

# Smooth partial frames on disks of arbitrary positive dimension

Smooth the constructed continuous frame in its actual projection ranges,
keeping every original boundary column exactly. The ambient extension,
boundary interpolation, relative approximation and orthonormalization use
the original disk and sphere dimensions throughout. No smooth extension
or separately chosen normal-plane family is assumed.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame

open NoExoticSixSphere GLOrthonormalization Stiefel DiskCylinder

theorem exists_smooth_extension_of_continuous {d N n : ℕ}
    (P : Vector (d + 1) → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ P x)
    (a : C(NoExoticSixSphere.Sphere d, Space N n))
    (has : ContMDiff (𝓡 d) 𝓘(ℝ, Vector n →L[ℝ] Vector N) ∞ (fun s => (a s).val))
    (A : C(Disk (E := Vector (d + 1)), Space N n))
    (hAr : ∀ x, (A x).val.range ≤ (P x.val).range)
    (hAb : ∀ s, A (boundaryToDisk s) = a s) :
    ∃ T : Vector (d + 1) → Vector n →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, (T x).range ≤ (P x).range) ∧
      ∀ s, T s.val = (a s).val := by
  let Ac : C(Disk (E := Vector (d + 1)), Vector n →L[ℝ] Vector N) :=
    ⟨fun x => (A x).val, continuous_subtype_val.comp A.continuous⟩
  obtain ⟨A₀, hA₀⟩ := Ac.exists_restrict_eq isClosed_closedBall
  have heA (x : Disk (E := Vector (d + 1))) : A₀ x.val = (A x).val :=
    ContinuousMap.congr_fun hA₀ x
  let F : C(Vector (d + 1), Vector n →L[ℝ] Vector N) :=
    ⟨SmoothSphereAmbient.extension (spherePole d) (fun s => (a s).val),
      (SmoothSphereAmbient.contDiff_extension (spherePole d) _ has).continuous⟩
  have hFs : ContDiff ℝ ∞ F :=
    SmoothSphereAmbient.contDiff_extension (spherePole d) _ has
  have hF (s : NoExoticSixSphere.Sphere d) : F s.val = (a s).val :=
    SmoothSphereAmbient.extension_coe (spherePole d) (fun s => (a s).val) s
  have hFA : EqOn F A₀ (sphere (0 : Vector (d + 1)) 1) := by
    intro x hx
    let s : NoExoticSixSphere.Sphere d := ⟨x, hx⟩
    exact (hF s).trans ((congrArg Subtype.val (hAb s)).symm.trans
      (heA (boundaryToDisk s)).symm)
  have hPA (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (P x).comp (A₀ x) = A₀ x := by
    rw [heA ⟨x, hx⟩]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P x) (hP x hx)
      ⟨(A ⟨x, hx⟩).val w, hAr ⟨x, hx⟩ ⟨w, rfl⟩⟩
  have hAi (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      Function.Injective ((P x).comp (A₀ x)) := by
    rw [hPA x hx, heA ⟨x, hx⟩]
    exact Stiefel.injective (A ⟨x, hx⟩)
  have hPc : ContinuousOn P (closedBall (0 : Vector (d + 1)) 1) :=
    fun x hx => (hPs x hx).continuousAt.continuousWithinAt
  obtain ⟨B, hBi, U, hU, hSU, hBF⟩ := exists_boundaryInterpolation
    (isCompact_closedBall (0 : Vector (d + 1)) 1) (isCompact_sphere (0 : Vector (d + 1)) 1)
    A₀ F P hPc hAi hFA
  have hBA : EqOn B A₀ (sphere (0 : Vector (d + 1)) 1) :=
    fun x hx => (hBF (hSU hx)).trans (hFA hx)
  have hBP (x : Vector (d + 1))
      (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ sphere 0 1) :
      (P x).comp (B x) = B x := by rw [hBA hx.2, hPA x hx.1]
  have hBn (x : Vector (d + 1))
      (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ sphere 0 1)
      (w : Vector n) : ‖B x w‖ = ‖w‖ := by
    rw [hBA hx.2, heA ⟨x, hx.1⟩]
    exact (A ⟨x, hx.1⟩).property w
  have hBs : ContDiffOn ℝ ∞ B U := hFs.contDiffOn.congr hBF
  obtain ⟨T, hTs, hTn, hTr, hT⟩ := exists_smoothPartialFrame_rel
    (isCompact_closedBall (0 : Vector (d + 1)) 1) B B.continuous P hPs hBi hBP hBn
    isClosed_sphere (hU.mem_nhdsSet.mpr hSU) hBs
  refine ⟨T, hTs, hTn, hTr, ?_⟩
  intro s
  exact (hT ⟨sphere_subset_closedBall s.property, s.property⟩).trans
    ((hBF (hSU s.property)).trans (hF s))

theorem exists_smooth_projection_extension {d N c r : ℕ} (hd : 0 < d) (hc : d < c)
    (P : Vector (d + 1) → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ P x)
    (hr : Module.finrank ℝ (P 0).range = c + r)
    (a : C(NoExoticSixSphere.Sphere d, Space N r))
    (has : ContMDiff (𝓡 d) 𝓘(ℝ, Vector r →L[ℝ] Vector N) ∞ (fun s => (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (P s.val).range) :
    ∃ T : Vector (d + 1) → Vector r →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, (T x).range ≤ (P x).range) ∧
      ∀ s, T s.val = (a s).val := by
  have hPc : Continuous (fun x : Disk (E := Vector (d + 1)) => P x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hPs x x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let Pc : C(Disk (E := Vector (d + 1)), Vector N →L[ℝ] Vector N) := ⟨_, hPc⟩
  obtain ⟨A, hAr, hAb⟩ := exists_projection_extension hd hc Pc
    (fun x => hP x x.property) hr a ha
  exact exists_smooth_extension_of_continuous P hP hPs a has A hAr hAb

end Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame
