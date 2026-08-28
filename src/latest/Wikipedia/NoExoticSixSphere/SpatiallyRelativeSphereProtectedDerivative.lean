import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereParameterSubmersion
import Wikipedia.NoExoticSixSphere.WeightedAffineProtectedDerivative
import Wikipedia.NoExoticSixSphere.ManifoldChartDerivativeComparison
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Native derivative preservation on the protected source set

The cutoff is assumed nonnegative, not locally constant. Its zero derivative
at every zero removes both terms of the weighted affine variation. Equality
of actual chart derivatives is then transferred to the original native atlas.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SpatiallyRelativeSphereFamily

open GLOrthonormalization RelativeDoublePointPerturbation EuclideanEmbedding
open ManifoldAffineSphereFamily (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 3 → M) (χ : Sphere 3 → ℝ)

theorem contMDiffAt_map_slice
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (p : Parameters e) (t : ℝ) (x : Sphere 3) (hp : ambient e f χ p t x ∈ r.domain) :
    ContMDiffAt (𝓡 3) (𝓡 n) ∞ (map e r f χ p t) x := by
  have ha : ContMDiff (𝓡 3) (𝓡 e.ambientDimension) ∞ (ambient e f χ p t) :=
    (contMDiff_ambient e f χ hf hχ).comp
      (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))
  exact (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)).comp x ha.contMDiffAt

theorem fderiv_chart_spatial_eq_of_zero_cutoff
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hn : ∀ z, 0 ≤ χ z)
    (s : SourceChart) (c : TargetChart n M) (p : Parameters e) (t : ℝ) (x : Vector 3)
    (hx : x ∈ s.target) (hχx : χ (s.symm x) = 0) (hc : f t (s.symm x) ∈ c.source) :
    fderiv ℝ (fun z ↦ c (map e r f χ p t (s.symm z))) x =
      fderiv ℝ (fun z ↦ c (f t (s.symm z))) x := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
    ⟨by simp [GLOrthonormalization.Vector]⟩
  let g : Vector 3 → Vector e.ambientDimension := fun z ↦ e.toFun (f t (s.symm z))
  let i : Vector 3 → Vector 4 := fun z ↦ (s.symm z : Vector 4)
  let R : Vector e.ambientDimension → Vector n := fun y ↦ c (r.toFun y)
  let a : Vector 3 → ℝ := fun z ↦ cutoff t * χ (s.symm z)
  have ha0 : a x = 0 := by simp only [a, hχx, mul_zero]
  have han : ∀ z, 0 ≤ a z := fun z ↦ mul_nonneg (cutoff_nonneg t) (hn (s.symm z))
  have hsmooth : ContMDiffAt (𝓡 3) (𝓡 3) ∞ s.symm x :=
    s.contMDiffOn_invFun.contMDiffAt (s.open_target.mem_nhds hx)
  have hslice : ContMDiff (𝓡 3) (𝓡 n) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hg : ContDiffAt ℝ ∞ g x :=
    ((e.smooth.comp hslice).contMDiffAt.comp x hsmooth).contDiffAt
  have hcoe : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere (E := Vector 4) (n := 3) (m := ∞)
  have hi : ContDiffAt ℝ ∞ i x := (hcoe.contMDiffAt.comp x hsmooth).contDiffAt
  have ha : ContDiffAt ℝ ∞ a x :=
    contDiffAt_const.mul (hχ.contMDiffAt.comp x hsmooth).contDiffAt
  have hy : WeightedAffineComposite.ambient g i a p x = e.toFun (f t (s.symm x)) := by
    simp only [WeightedAffineComposite.ambient, ha0, zero_smul, add_zero, g]
  have hp : WeightedAffineComposite.ambient g i a p x ∈ r.domain :=
    hy.symm ▸ r.contains (mem_range_self (f t (s.symm x)))
  have hc' : r.toFun (WeightedAffineComposite.ambient g i a p x) ∈ c.source := by
    rw [hy, r.fixes]
    exact hc
  have hR : ContDiffAt ℝ ∞ R (WeightedAffineComposite.ambient g i a p x) :=
    contDiffAt_chartRetraction e r c _ hp hc'
  have hjet := WeightedAffineComposite.fderiv_composite_eq_zero_parameter_of_zero_cutoff
    g i R a p x (hg.differentiableAt (by simp)) (hi.differentiableAt (by simp))
    (ha.differentiableAt (by simp)) (hR.differentiableAt (by simp)) han ha0
  have heq (q : Parameters e) :
      (fun z : Vector 3 ↦ c (map e r f χ q t (s.symm z))) =
        WeightedAffineComposite.composite g i R a q := by
    funext z
    simp only [map, ambient_apply, WeightedAffineComposite.composite,
      WeightedAffineComposite.ambient, g, i, R, a]
  rw [← heq p, ← heq 0] at hjet
  simpa only [map_zero_parameter] using hjet

theorem mfderiv_map_of_zero_cutoff [IsManifold (𝓡 n) ∞ M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ) (hn : ∀ z, 0 ≤ χ z)
    (p : Parameters e) (t : ℝ) (x : Sphere 3) (hx : χ x = 0) :
    mfderiv (𝓡 3) (𝓡 n) (map e r f χ p t) x = mfderiv (𝓡 3) (𝓡 n) (f t) x := by
  let s := modelChartPartialDiffeomorph (I := 𝓡 3) x
  let c := modelChartPartialDiffeomorph (I := 𝓡 n) (f t x)
  have hxs : x ∈ s.source := mem_extChartAt_source x
  have hxc : f t x ∈ c.source := mem_extChartAt_source (f t x)
  have he : s.symm (s x) = x := s.left_inv hxs
  have hp : ambient e f χ p t x ∈ r.domain := by
    rw [ambient_apply, hx, mul_zero, zero_smul, add_zero]
    exact r.contains (mem_range_self (f t x))
  have hmap := (contMDiffAt_map_slice e r f χ hf hχ p t x hp).mdifferentiableAt (by simp)
  have hslice : ContMDiff (𝓡 3) (𝓡 n) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hc : map e r f χ p t (s.symm (s x)) ∈ c.source := by
    rw [he, map_eq_zero_cutoff e r f χ p t x hx]
    exact hxc
  have hjet := fderiv_chart_spatial_eq_of_zero_cutoff e r f χ hf hχ hn s c p t (s x)
    (s.map_source hxs) (by rwa [he]) (by rwa [he])
  have hD := ManifoldCoordinates.mfderiv_eq_of_fderiv_in_charts_eq
    (map e r f χ p t) (f t) s c (s x) (s.map_source hxs) hc
    (by simpa only [he] using hmap) (hslice.mdifferentiableAt (by simp))
    (by rw [he, map_eq_zero_cutoff e r f χ p t x hx]) hjet
  convert! hD using 1
  rw [he]

end NoExoticSixSphere.SpatiallyRelativeSphereFamily
