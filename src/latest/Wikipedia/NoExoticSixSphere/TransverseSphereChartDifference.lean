import Wikipedia.NoExoticSixSphere.IntersectionTraceFullCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative

/-!
# Native endpoint transversality makes the spatial coincidence derivative invertible

Both source-chart derivatives and the shared target-chart derivative are
actual linear equivalences. The sign on the second sheet changes a sum to a
difference without losing surjectivity. In dimension three plus three, the
spatial derivative is therefore bijective, as required by the parameter-
preserving inverse-function theorem at an endpoint.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization

theorem surjective_signed_chart_coprod
    (A B : Vector 3 →L[ℝ] Vector 6) (C : Vector 6 →L[ℝ] Vector 6)
    (S T : Vector 3 →L[ℝ] Vector 3) (hAB : Surjective (A.coprod B))
    (hC : Surjective C) (hS : Surjective S) (hT : Surjective T) :
    Surjective ((C.comp (A.comp S)).coprod (-(C.comp (B.comp T)))) := by
  intro w
  obtain ⟨v, hv⟩ := hC w
  obtain ⟨q, hq⟩ := hAB v
  obtain ⟨x, hx⟩ := hS q.1
  obtain ⟨y, hy⟩ := hT (-q.2)
  refine ⟨(x, y), ?_⟩
  change C (A (S x)) + -C (B (T y)) = w
  rw [hx, hy, map_neg, map_neg, neg_neg, ← map_add]
  change A q.1 + B q.2 = v at hq
  rw [hq, hv]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hf hg in
theorem fderiv_spatial_difference_formula (t : ℝ) (x y : Sphere 3)
    (s z : SphereChart) (c : ManifoldChart M) (hx : x ∈ s.source) (hy : y ∈ z.source)
    (hc : f t x ∈ c.source) (hxy : f t x = g t y) :
    fderiv ℝ (fun q : Vector 3 × Vector 3 ↦
      coordinateDifference f g s z c (t, q)) (s x, z y) =
      ((mfderiv (𝓡 6) (𝓡 6) c (f t x)).comp
        ((mfderiv (𝓡 3) (𝓡 6) (f t) x).comp
          (mfderiv (𝓡 3) (𝓡 3) s.symm (s x)))).coprod
      (-((mfderiv (𝓡 6) (𝓡 6) c (f t x)).comp
        ((mfderiv (𝓡 3) (𝓡 6) (g t) y).comp
          (mfderiv (𝓡 3) (𝓡 3) z.symm (z y))))) := by
  have hsx : s.symm (s x) = x := s.left_inv hx
  have hzy : z.symm (z y) = y := z.left_inv hy
  have hc' : g t y ∈ c.source := hxy ▸ hc
  have hfs : ContMDiff (𝓡 3) (𝓡 6) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hgs : ContMDiff (𝓡 3) (𝓡 6) ∞ (g t) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  let F : Vector 3 → Vector 6 := fun u ↦ c (f t (s.symm u))
  let G : Vector 3 → Vector 6 := fun v ↦ c (g t (z.symm v))
  have hcf : f t (s.symm (s x)) ∈ c.source := hsx.symm ▸ hc
  have hcg : g t (z.symm (z y)) ∈ c.source := hzy.symm ▸ hc'
  have hFd : DifferentiableAt ℝ F (s x) :=
    ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hcf)).comp (s x)
      (hfs.contMDiffAt.comp (s x)
        (s.contMDiffOn_invFun.contMDiffAt
          (s.open_target.mem_nhds (s.map_source hx))))).contDiffAt.differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G (z y) :=
    ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hcg)).comp (z y)
      (hgs.contMDiffAt.comp (z y)
        (z.contMDiffOn_invFun.contMDiffAt
          (z.open_target.mem_nhds (z.map_source hy))))).contDiffAt.differentiableAt (by simp)
  have hF := ManifoldCoordinates.fderiv_in_charts (f t) s c (s x) (s.map_source hx) hcf
    (hfs.mdifferentiableAt (by simp))
  have hG := ManifoldCoordinates.fderiv_in_charts (g t) z c (z y) (z.map_source hy) hcg
    (hgs.mdifferentiableAt (by simp))
  rw [hsx] at hF
  rw [hzy, ← hxy] at hG
  have hd := (hFd.hasFDerivAt.comp (s x, z y)
    ((ContinuousLinearMap.fst ℝ (Vector 3) (Vector 3)).hasFDerivAt)).sub
      (hGd.hasFDerivAt.comp (s x, z y)
        ((ContinuousLinearMap.snd ℝ (Vector 3) (Vector 3)).hasFDerivAt))
  change HasFDerivAt (fun q : Vector 3 × Vector 3 ↦
    coordinateDifference f g s z c (t, q)) _ (s x, z y) at hd
  have he : fderiv ℝ (fun q : Vector 3 × Vector 3 ↦
      coordinateDifference f g s z c (t, q)) (s x, z y) =
      (fderiv ℝ F (s x)).coprod (-(fderiv ℝ G (z y))) := by
    rw [hd.fderiv]
    apply ContinuousLinearMap.ext
    intro q
    rfl
  rw [he]
  change (fderiv ℝ (fun u ↦ c (f t (s.symm u))) (s x)).coprod
    (-(fderiv ℝ (fun v ↦ c (g t (z.symm v))) (z y))) = _
  rw [hF, hG]
  rfl

include hf hg in
theorem surjective_fderiv_spatial_difference (t : ℝ) (x y : Sphere 3)
    (s z : SphereChart) (c : ManifoldChart M) (hx : x ∈ s.source) (hy : y ∈ z.source)
    (hc : f t x ∈ c.source) (hxy : f t x = g t y)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g t) y))) :
    Surjective (fderiv ℝ (fun q : Vector 3 × Vector 3 ↦
      coordinateDifference f g s z c (t, q)) (s x, z y)) := by
  have hS : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ s.symm (s x) :=
    ⟨s.symm, s.map_source hx, fun _ _ ↦ rfl⟩
  have hT : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ z.symm (z y) :=
    ⟨z.symm, z.map_source hy, fun _ _ ↦ rfl⟩
  have hC : IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞ c (f t x) :=
    ⟨c, hc, fun _ _ ↦ rfl⟩
  rw [fderiv_spatial_difference_formula f g hf hg t x y s z c hx hy hc hxy]
  exact surjective_signed_chart_coprod _ _ _ _ _ ht
    (hC.mfderivToContinuousLinearEquiv (by simp)).surjective
    (hS.mfderivToContinuousLinearEquiv (by simp)).surjective
    (hT.mfderivToContinuousLinearEquiv (by simp)).surjective

include hf hg in
theorem bijective_fderiv_spatial_difference (t : ℝ) (x y : Sphere 3)
    (s z : SphereChart) (c : ManifoldChart M) (hx : x ∈ s.source) (hy : y ∈ z.source)
    (hc : f t x ∈ c.source) (hxy : f t x = g t y)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g t) y))) :
    Bijective (fderiv ℝ (fun q : Vector 3 × Vector 3 ↦
      coordinateDifference f g s z c (t, q)) (s x, z y)) := by
  have hs := surjective_fderiv_spatial_difference f g hf hg t x y s z c hx hy hc hxy ht
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs, hs⟩
  simp [GLOrthonormalization.Vector]

end NoExoticSixSphere.IntersectionTrace
