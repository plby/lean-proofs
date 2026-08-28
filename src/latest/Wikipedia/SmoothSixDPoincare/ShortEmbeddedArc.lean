import Wikipedia.SmoothSixDPoincare.CurveEndpointRepair
import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# A short embedded immersive arc in any prescribed point neighborhood

The native endpoint-derivative repair supplies a nonzero tangent at the
chosen point. Local injectivity and openness of immersion give a genuine
embedded short interval, which is rescaled to the unit interval. The curve
remains globally smooth and its whole interval lies in the prescribed open set.
-/

noncomputable section

open Set Function Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N] [T2Space N]

/-- Construct an actual short smooth embedded arc starting at the given point. -/
theorem exists_short_embedded_arc {U : Set N} (hU : IsOpen U) {x : N} (hx : x ∈ U)
    (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ f 0 = x ∧ f 1 ≠ x ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ U := by
  let c : C(ℝ, N) := ContinuousMap.const ℝ x
  obtain ⟨g, hg, hrel, hi⟩ :=
    ManifoldImmersion.exists_curve_endpoint_derivative_repair (J := J) c contMDiff_const hdim
  have hg0 : g 0 = x := (hrel.fst_eq_snd (by simp)).symm
  have hi0 : Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := hi 0 (by simp)
  obtain ⟨V, hV, h0V, hinj⟩ :=
    ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative hg hi0
  let W := V ∩ ({t : ℝ | Injective (mfderiv 𝓘(ℝ, ℝ) J g t)} ∩ g ⁻¹' U)
  have hW : IsOpen W := hV.inter
    ((ManifoldImmersion.isOpen_injective_derivative hg).inter (hU.preimage g.continuous))
  have h0W : (0 : ℝ) ∈ W := ⟨h0V, hi0, (show g 0 ∈ U from hg0.symm ▸ hx)⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
  let L : ℝ →L[ℝ] ℝ := (r / 2) • ContinuousLinearMap.id ℝ ℝ
  have hLs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ L := L.contDiff.contMDiff
  have hL (t : ℝ) : L t = (r / 2) * t := rfl
  have hscale : 0 < r / 2 := by positivity
  have hLinj : Injective L := by
    intro s t hst
    exact mul_left_cancel₀ hscale.ne' hst
  have hLW : ∀ t ∈ Icc (0 : ℝ) 1, L t ∈ W := by
    intro t ht
    apply hball
    change dist (L t) 0 < r
    rw [dist_zero_right, Real.norm_eq_abs, hL,
      abs_of_nonneg (mul_nonneg hscale.le ht.1)]
    have hbound := mul_le_mul_of_nonneg_left ht.2 hscale.le
    linarith
  let f : C(ℝ, N) := ⟨g ∘ L, g.continuous.comp L.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := hg.comp hLs
  have hfinj : InjOn f (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact hLinj (hinj (hLW s hs).1 (hLW t ht).1 hst)
  have hf0 : f 0 = x := by
    change g (L 0) = x
    rw [map_zero, hg0]
  have hemb : Topology.IsClosedEmbedding (fun t : unitInterval => f t) := by
    apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact Subtype.ext (hfinj s.property t.property hst)
  refine ⟨f, hf, hf0, ?_, hemb, ?_, ?_⟩
  · intro hfx
    have h10 : (1 : ℝ) = 0 := hfinj (by simp) (by simp) (hfx.trans hf0.symm)
    exact one_ne_zero h10
  · intro t ht
    change Injective (mfderiv 𝓘(ℝ, ℝ) J (g ∘ L) t)
    rw [mfderiv_comp t (hg.mdifferentiableAt (by simp))
      (hLs.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, L.fderiv]
    exact (hLW t ht).2.1.comp hLinj
  · intro t ht
    exact (hLW t ht).2.2

end Wikipedia.SmoothSixDPoincare
