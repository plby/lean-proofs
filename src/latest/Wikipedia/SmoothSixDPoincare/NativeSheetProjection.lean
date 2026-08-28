import Wikipedia.SmoothSixDPoincare.SheetNormalCoordinates
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse

/-!
# Native coordinates induced on an immersed sheet by a clean ambient chart

The first component of the inverse ambient chart, restricted to the original
sheet, has injective differential: the second component vanishes identically
near every sheet point. In the sheet dimension this is a local diffeomorphism,
with the original native smooth structure retained.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeSheetCoordinates

variable {D B E G H M N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace H N]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)

/-- The first actual ambient inverse-chart coordinate on the original sheet domain. -/
def projection (x : N) : D := (Φ.symm (F x)).1

theorem contMDiffOn_projection (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) :
    ContMDiffOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hcoord : ContMDiffOn I 𝓘(ℝ, D × B) ∞ (Φ.symm ∘ F) (F ⁻¹' Φ.target) :=
    Φ.contMDiffOn_invFun.comp hF.contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoord

/-- Vanishing normal coordinates leave an injective first-coordinate differential. -/
theorem injective_mfderiv_projection (hF : ContMDiff I 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ range F ↔ z.2 = 0) {x : N} (hx : F x ∈ Φ.target)
    (hiF : Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    Injective (mfderiv I 𝓘(ℝ, D) (projection Φ F) x) := by
  let C : N → (D × B) := Φ.symm ∘ F
  let T : G →L[ℝ] (D × B) := mfderiv I 𝓘(ℝ, D × B) C x
  have hC : ContMDiffAt I 𝓘(ℝ, D × B) ∞ C x :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hx)).comp x hF.contMDiffAt
  have hTi : Injective T := by
    change Injective (mfderiv I 𝓘(ℝ, D × B) (Φ.symm ∘ F) x)
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hx)
      (hF.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ.symm hx).injective.comp hiF
  have hfst : (mfderiv I 𝓘(ℝ, D) (projection Φ F) x : G →L[ℝ] D) =
      (ContinuousLinearMap.fst ℝ D B).comp T := by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, D) ∞ (Prod.fst : D × B → D) :=
      contDiff_fst.contMDiff
    have hd : mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, D) (Prod.fst : D × B → D) (C x) =
        ContinuousLinearMap.fst ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.fst ℝ D B).fderiv
    change mfderiv I 𝓘(ℝ, D) (Prod.fst ∘ C) x = _
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp))
      (hC.mdifferentiableAt (by simp)), hd]
    rfl
  have hzero : (Prod.snd ∘ C) =ᶠ[𝓝 x] (fun _ => (0 : B)) := by
    filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds hx)] with y hy
    exact (hclean _ (Φ.map_target' hy)).mp ⟨y, (Φ.right_inv' hy).symm⟩
  have hsnd : (ContinuousLinearMap.snd ℝ D B).comp T = 0 := by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) :=
      contDiff_snd.contMDiff
    have hd : mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (C x) =
        ContinuousLinearMap.snd ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.snd ℝ D B).fderiv
    have hz : (mfderiv I 𝓘(ℝ, B) (Prod.snd ∘ C) x : G →L[ℝ] B) = 0 := by
      rw [hzero.mfderiv_eq, mfderiv_const]
      rfl
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp))
      (hC.mdifferentiableAt (by simp)), hd] at hz
    exact hz
  intro u v huv
  apply hTi
  apply Prod.ext
  · exact (congrArg (fun L : G →L[ℝ] D => L u) hfst).symm.trans
      (huv.trans (congrArg (fun L : G →L[ℝ] D => L v) hfst))
  · have hz (w : G) : (T w).2 = 0 :=
      congrArg (fun L : G →L[ℝ] B => L w) hsnd
    rw [hz u, hz v]

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ G]
  [I.Boundaryless] [IsManifold I ∞ N]

/-- Equal sheet dimension turns the actual projection into a native local diffeomorphism. -/
theorem isLocalDiffeomorphOn_projection (hF : ContMDiff I 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    IsLocalDiffeomorphOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hU : IsOpen (F ⁻¹' Φ.target) := Φ.open_target.preimage hF.continuous
  intro x
  let A : G →L[ℝ] D := mfderiv I 𝓘(ℝ, D) (projection Φ F) x.1
  have hi : Injective A := injective_mfderiv_projection Φ F hF hclean x.2 (hiF x.1)
  have hb : Bijective A := ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
  have hA : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  exact isLocalDiffeomorphAt_boundaryless hU x.2 (contMDiffOn_projection Φ F hF) hA

end Wikipedia.SmoothSixDPoincare.NativeSheetCoordinates
