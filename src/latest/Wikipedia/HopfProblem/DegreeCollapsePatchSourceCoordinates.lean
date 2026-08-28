import Wikipedia.HopfProblem.DegreeCollapsePatchNormalDerivative

/-!
# Actual source coordinates induced by a clean branch chart

Project the inverse ambient branch chart to its sheet coordinates. On the
original immersed source this is a smooth coordinate map. Its derivative
is invertible wherever the selected patch contains a neighborhood and the
original tangent map is injective. No global inverse of the immersion is
used. The original tangent map factors through these coordinates.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D B E M G N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace N] [ChartedSpace G N]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)

def patchSourceCoordinates : N → D := Prod.fst ∘ (Φ.symm ∘ F)

theorem contMDiffOn_patchSourceCoordinates (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) :
    ContMDiffOn 𝓘(ℝ, G) 𝓘(ℝ, D) ∞ (patchSourceCoordinates Φ F) (F ⁻¹' Φ.target) :=
  contDiff_fst.contMDiff.comp_contMDiffOn
    (Φ.contMDiffOn_invFun.comp hF.contMDiffOn (fun _ hx => hx))

theorem mfderiv_patchSourceCoordinates
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) {x : N} (hx : F x ∈ Φ.target) :
    mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D) (patchSourceCoordinates Φ F) x =
      (ContinuousLinearMap.fst ℝ D B).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (F x)).comp
          (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x)) := by
  have hc := (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hx)).comp x hF.contMDiffAt
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, D) ∞ (Prod.fst : D × B → D) :=
    contDiff_fst.contMDiff
  have hfst : mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, D) (Prod.fst : D × B → D) (Φ.symm (F x)) =
      ContinuousLinearMap.fst ℝ D B := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.fst ℝ D B).fderiv
  have h₁ : (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D) (patchSourceCoordinates Φ F) x : G →L[ℝ] D) =
      (mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, D) (Prod.fst : D × B → D) (Φ.symm (F x)) :
        (D × B) →L[ℝ] D).comp
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D × B) (Φ.symm ∘ F) x : G →L[ℝ] (D × B)) :=
    mfderiv_comp x (hs.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp))
  rw [hfst] at h₁
  have h₂ : (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D × B) (Φ.symm ∘ F) x : G →L[ℝ] (D × B)) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (F x) : E →L[ℝ] (D × B)).comp
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x : G →L[ℝ] E) :=
    mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hx) (hF.mdifferentiableAt (by simp))
  exact h₁.trans (congrArg (fun L : G →L[ℝ] (D × B) => (ContinuousLinearMap.fst ℝ D B).comp L) h₂)

theorem patch_inverse_derivative_normal_zero
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) {K : Set N}
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    {x : N} (hK : K ∈ 𝓝 x) (hx : F x ∈ Φ.target) (v : G) :
    ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (F x))
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) v)).2 = 0 := by
  have hz := normalDerivative_comp_patch_eq_zero Φ hF hclean hK hx
  rw [mfderiv_normalCoordinate Φ hx] at hz
  exact congrArg (fun L : G →L[ℝ] B => L v) hz

theorem bijective_mfderiv_patchSourceCoordinates [FiniteDimensional ℝ G] [FiniteDimensional ℝ D]
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) {K : Set N}
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    {x : N} (hK : K ∈ 𝓝 x) (hx : F x ∈ Φ.target)
    (hi : Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D) :
    Bijective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D) (patchSourceCoordinates Φ F) x) := by
  have hri := (PartialChart.bijective_mfderiv Φ.symm hx).1
  have hinj : Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D) (patchSourceCoordinates Φ F) x) := by
    intro v w he
    rw [mfderiv_patchSourceCoordinates Φ F hF hx] at he
    apply hi
    apply hri
    apply Prod.ext
    · exact he
    · rw [patch_inverse_derivative_normal_zero Φ F hF hclean hK hx v,
        patch_inverse_derivative_normal_zero Φ F hF hclean hK hx w]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

theorem original_patch_derivative_factor
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) {K : Set N}
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    {x : N} (hK : K ∈ 𝓝 x) (hx : F x ∈ Φ.target) :
    mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x =
      (mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (Φ.symm (F x))).comp
        ((ContinuousLinearMap.inl ℝ D B).comp
          (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D) (patchSourceCoordinates Φ F) x)) := by
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, D × B) 𝓘(ℝ, E) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  have hTR := hdiff.comp_symm_deriv hx
  rw [mfderiv_patchSourceCoordinates Φ F hF hx]
  apply ContinuousLinearMap.ext
  intro v
  have hz := patch_inverse_derivative_normal_zero Φ F hF hclean hK hx v
  have he : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (F x))
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) v) =
      (((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (F x))
        ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) v)).1, 0) := Prod.ext rfl hz
  have hid := congrArg (fun L : E →L[ℝ] E => L ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) v)) hTR
  change (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) v = _
  exact hid.symm.trans (congrArg
    (mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (Φ.symm (F x))) he)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
