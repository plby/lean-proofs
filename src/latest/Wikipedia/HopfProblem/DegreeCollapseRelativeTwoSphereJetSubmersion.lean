import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereFamily
import Wikipedia.NoExoticSixSphere.WeightedAffineJetSubmersion

/-!
# Actual spatial-jet submersion off the protected source region

The source-dependent cutoff is retained in the actual manifold perturbation.
In valid native charts, the weighted affine calculation gives surjectivity
of the parameter derivative of its spatial jet wherever the cutoff is nonzero.
The cutoff derivative is included; no local constancy is assumed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere

open GLOrthonormalization RelativeDoublePointPerturbation EuclideanEmbedding
open TwoSpherePerturbation (Parameters)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

theorem surjective_fderiv_chart_spatial_parameter
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s : PartialDiffeomorph (𝓡 2) (𝓡 2) (Sphere 2) (Vector 2) ∞)
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (p : Parameters e) (t : ℝ) (x : Vector 2)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hx : x ∈ s.target) (hχx : χ (s.symm x) ≠ 0)
    (hp : ambient e f χ p t (s.symm x) ∈ r.domain)
    (hc : map e r f χ p t (s.symm x) ∈ c.source) :
    Surjective (fderiv ℝ
      (fun q : Parameters e ↦
        fderiv ℝ (fun z : Vector 2 ↦ c (map e r f χ q t (s.symm z))) x) p) := by
  let : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
    ⟨by simp [GLOrthonormalization.Vector]⟩
  let g : Vector 2 → Vector e.ambientDimension := fun z ↦ e.toFun (f t (s.symm z))
  let i : Vector 2 → Vector 3 := fun z ↦ (s.symm z : Vector 3)
  let R : Vector e.ambientDimension → Vector n := fun y ↦ c (r.toFun y)
  let a : Vector 2 → ℝ := fun z ↦ cutoff t * χ (s.symm z)
  let y := ambient e f χ p t (s.symm x)
  have hy : WeightedAffineComposite.ambient g i a p x = y :=
    (ambient_apply e f χ p t (s.symm x)).symm
  have hsmooth : ContMDiffAt (𝓡 2) (𝓡 2) ∞ s.symm x :=
    s.contMDiffOn_invFun.contMDiffAt (s.open_target.mem_nhds hx)
  have hslice : ContMDiff (𝓡 2) (𝓡 n) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hg : ContDiffAt ℝ ∞ g x :=
    ((e.smooth.comp hslice).contMDiffAt.comp x hsmooth).contDiffAt
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : Sphere 2 → Vector 3) :=
    contMDiff_coe_sphere (E := Vector 3) (n := 2) (m := ∞)
  have hi : ContDiffAt ℝ ∞ i x := (hcoe.contMDiffAt.comp x hsmooth).contDiffAt
  have ha : ContDiffAt ℝ ∞ a x :=
    contDiffAt_const.mul (hχ.contMDiffAt.comp x hsmooth).contDiffAt
  have ha0 : a x ≠ 0 := mul_ne_zero (cutoff_pos ht).ne' hχx
  have hsLocal : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ s.symm x :=
    ⟨s.symm, hx, fun _ _ ↦ rfl⟩
  have hsi := (hsLocal.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv (𝓡 2) (𝓡 2) s.symm x) at hsi
  have hinc : Injective (mfderiv (𝓡 2) (𝓡 3)
      (Subtype.val : Sphere 2 → Vector 3) (s.symm x)) := by
    convert! injective_mvfderiv_subtypeVal_sphere (s.symm x)
  have hii : Injective (fderiv ℝ i x) := by
    change Injective (fderiv ℝ ((Subtype.val : Sphere 2 → Vector 3) ∘ s.symm) x)
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp x (hcoe.mdifferentiableAt (by simp)) (hsmooth.mdifferentiableAt (by simp))]
    exact hinc.comp hsi
  have hrsmooth : ContMDiffAt (𝓡 e.ambientDimension) (𝓡 n) ∞ r.toFun y :=
    r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)
  have hcsmooth : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (r.toFun y) :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc)
  have hR : ContDiffAt ℝ ∞ R y := (hcsmooth.comp y hrsmooth).contDiffAt
  have hcLocal : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (r.toFun y) :=
    ⟨c, hc, fun _ _ ↦ rfl⟩
  have hcs := (hcLocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  change Surjective (mfderiv (𝓡 n) (𝓡 n) c (r.toFun y)) at hcs
  have hRs : Surjective (fderiv ℝ R y) := by
    change Surjective (fderiv ℝ (c ∘ r.toFun) y)
    rw [← mfderiv_eq_fderiv, mfderiv_comp y (hcsmooth.mdifferentiableAt (by simp))
      (hrsmooth.mdifferentiableAt (by simp))]
    exact hcs.comp (r.submersive y hp)
  have hR' : ContDiffAt ℝ ∞ R (WeightedAffineComposite.ambient g i a p x) := hy ▸ hR
  have hRs' : Surjective (fderiv ℝ R (WeightedAffineComposite.ambient g i a p x)) :=
    hy ▸ hRs
  have hjet := WeightedAffineComposite.surjective_fderiv_spatial_parameter
    g i R a p x ha0 hg hi ha hR' hii hRs'
  have he (q : Parameters e) :
      (fun z : Vector 2 ↦ c (map e r f χ q t (s.symm z))) =
        WeightedAffineComposite.composite g i R a q := by
    funext z
    simp only [map, ambient_apply, WeightedAffineComposite.composite,
      WeightedAffineComposite.ambient, g, i, R, a]
  simpa only [he] using hjet

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
