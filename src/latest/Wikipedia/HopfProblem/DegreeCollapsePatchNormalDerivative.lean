import Wikipedia.SmoothSixDPoincare.TransverseSheetNormalDerivative

/-!
# Native normal derivatives for a selected source patch

It is enough that the selected patch contains a neighborhood of the source
point. Its clean ambient chart annihilates the original tangent map there.
Native transversality then makes the other branch's normal derivative
invertible. Other branches of the original immersion are not identified
with this zero section.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D B E M A Z N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace A N]
  [TopologicalSpace P] [ChartedSpace Z P]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞)

omit [FiniteDimensional ℝ B] in
theorem normalDerivative_comp_patch_eq_zero {F : N → M} {K : Set N}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    {x : N} (hK : K ∈ 𝓝 x) (hx : F x ∈ Φ.target) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)).comp
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x) = 0 := by
  have heq : (normalCoordinate Φ ∘ F) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hK,
      hF.continuous.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with y hyK hy
    have hq : Φ.invFun (F y) ∈ Φ.source := Φ.map_target' hy
    exact (hclean _ hq).mp ⟨y, hyK, (Φ.right_inv' hy).symm⟩
  have hzero : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, B) (normalCoordinate Φ ∘ F) x = 0 := by
    rw [heq.mfderiv_eq]
    simp only [mfderiv_const]
    rfl
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hx)
  rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp))
    (hF.mdifferentiableAt (by simp))] at hzero
  exact hzero

theorem bijective_normalDerivative_transverse_patch {F : N → M} {G : P → M} {K : Set N}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    {x : N} {y : P} (hK : K ∈ 𝓝 x) (hx : F x ∈ Φ.target) (hxy : G y = F x)
    (ht : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Bijective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y) := by
  let Q : E →L[ℝ] B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)
  let DF : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x
  let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y
  have hQ : Surjective Q := surjective_mfderiv_normalCoordinate Φ hx
  have hQA : Q.comp DF = 0 := normalDerivative_comp_patch_eq_zero Φ hF hclean hK hx
  have hb : Bijective (Q.comp DG) := bijective_normal_comp Q DF DG hQ ht hQA hdim
  have hy : G y ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hderiv : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y = Q.comp DG := by
    rw [mfderiv_comp y (hnormal.mdifferentiableAt (by simp))
      (hG.mdifferentiableAt (by simp)), hxy]
    rfl
  rw [hderiv]
  exact hb

variable {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z']

theorem bijective_normalDerivative_patch_parametrization {F : N → M} {G : P → M} {K : Set N}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) {z : Z'} (hz : z ∈ c.source)
    {x : N} (hK : K ∈ 𝓝 x) (hx : F x ∈ Φ.target) (hxy : G (c z) = F x)
    (ht : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c z))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Bijective (fderiv ℝ ((normalCoordinate Φ ∘ G) ∘ c) z) := by
  have hb := bijective_normalDerivative_transverse_patch Φ hF hG hclean hK hx hxy ht hdim
  have hy : G (c z) ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, B) ∞ (normalCoordinate Φ ∘ G) (c z) :=
    hnormal.comp (c z) hG.contMDiffAt
  rw [← mfderiv_eq_fderiv, mfderiv_comp z (hg.mdifferentiableAt (by simp))
    (c.mdifferentiableAt (by simp) hz)]
  exact hb.comp (PartialChart.bijective_mfderiv c hz)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
