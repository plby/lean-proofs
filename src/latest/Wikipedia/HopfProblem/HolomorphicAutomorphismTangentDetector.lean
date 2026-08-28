import Wikipedia.HopfProblem.HolomorphicAutomorphismTangentLimits

/-!
# A preserved local detector annihilates the limiting native field

The detector need only be holomorphic near the normalization point. If
its value there is eventually preserved by genuine automorphisms tending
to the identity, its actual manifold differential annihilates any native
tangent field obtained from their normalized coordinate differences.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismTangentDetector

open HolomorphicAutomorphismTangentGluing HolomorphicAutomorphismTangentLimits

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- The local detector, expressed in an actual preferred chart, is strictly
complex differentiable at the coordinate of the normalization point. -/
theorem detectorInChart_hasStrictFDerivAt (a : M) {p : M}
    (hp : p ∈ (chartAt E a).source) {τ : M → ℂ}
    (hτ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω τ p) :
    HasStrictFDerivAt (τ ∘ (chartAt E a).symm)
      (fderiv ℂ (τ ∘ (chartAt E a).symm) ((chartAt E a) p)) ((chartAt E a) p) := by
  have hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E a).symm
      ((chartAt E a) p) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a)
      ((chartAt E a).map_source hp)
  have ht : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω τ
      ((chartAt E a).symm ((chartAt E a) p)) := by
    rwa [(chartAt E a).left_inv hp]
  exact (ht.comp ((chartAt E a) p) hi).contDiffAt.hasStrictFDerivAt (by simp)

/-- The coordinate derivative is the genuine detector differential on the
native vector obtained by the inverse-chart pushforward. -/
theorem fderiv_detectorInChart (a : M) {p : M}
    (hp : p ∈ (chartAt E a).source) {τ : M → ℂ}
    (hτ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω τ p) (w : E) :
    fderiv ℂ (τ ∘ (chartAt E a).symm) ((chartAt E a) p) w =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ) τ p (chartVector a p w) := by
  have hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E a).symm
      ((chartAt E a) p) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a)
      ((chartAt E a).map_source hp)
  have hchain := mfderiv_comp_apply_of_eq (I := 𝓘(ℂ, E)) (I' := 𝓘(ℂ, E))
    (I'' := 𝓘(ℂ)) ((chartAt E a) p) (hτ.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp)) ((chartAt E a).left_inv hp) w
  rw [mfderiv_eq_fderiv] at hchain
  exact hchain.trans (congrArg (mfderiv 𝓘(ℂ, E) 𝓘(ℂ) τ p)
    (chartVector_eq_mfderiv_symm a hp w).symm)

variable {f : ℕ → HolomorphicAutomorphism 𝓘(ℂ, E) M} {c : ℕ → ℂ}

/-- Preserving a local detector forces the differential to vanish on an
actual normalized coordinate limit, pushed into the original tangent space. -/
theorem mfderiv_eq_zero_of_coordinate_limit
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a : M) {p : M} (hp : p ∈ (chartAt E a).source) {τ : M → ℂ}
    (hτ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω τ p) {w : E}
    (hw : Tendsto (fun n => normalizedCoordinate f c a n ((chartAt E a) p))
      atTop (𝓝 w))
    (hfix : ∀ᶠ n in atTop, τ (f n p) = τ p) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ) τ p (chartVector a p w) = 0 := by
  have hfp := tendsto_apply_of_tendsto_one hf p
  have ha : Tendsto (fun n => (chartAt E a) (f n p)) atTop
      (𝓝 ((chartAt E a) p)) := ((chartAt E a).continuousAt hp).tendsto.comp hfp
  have hsource : Tendsto (fun n => c n • ((chartAt E a) (f n p) - (chartAt E a) p))
      atTop (𝓝 w) := by
    simpa only [normalizedCoordinate, (chartAt E a).left_inv hp] using hw
  have hlin := HolomorphicAutomorphismLinearization.tendsto_scaled_difference
    (detectorInChart_hasStrictFDerivAt a hp hτ) ha tendsto_const_nhds hsource
  have hmem : ∀ᶠ n in atTop, f n p ∈ (chartAt E a).source :=
    hfp.eventually ((chartAt E a).open_source.mem_nhds hp)
  have hzero : (fun n => c n •
      ((τ ∘ (chartAt E a).symm) ((chartAt E a) (f n p)) -
        (τ ∘ (chartAt E a).symm) ((chartAt E a) p))) =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
    filter_upwards [hmem, hfix] with n hn hτn
    simp only [Function.comp_apply, (chartAt E a).left_inv hn,
      (chartAt E a).left_inv hp, hτn, sub_self, smul_zero]
  have htarget : Tendsto (fun n => c n •
      ((τ ∘ (chartAt E a).symm) ((chartAt E a) (f n p)) -
        (τ ∘ (chartAt E a).symm) ((chartAt E a) p))) atTop (𝓝 (0 : ℂ)) :=
    tendsto_const_nhds.congr' hzero.symm
  have hd := tendsto_nhds_unique hlin htarget
  exact (fderiv_detectorInChart a hp hτ w).symm.trans hd

/-- The same conclusion stated directly for an original native tangent vector. -/
theorem mfderiv_eq_zero_of_native_coordinate_limit
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a : M) {p : M} (hp : p ∈ (chartAt E a).source) {τ : M → ℂ}
    (hτ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω τ p) (v : TangentSpace 𝓘(ℂ, E) p)
    (hv : Tendsto (fun n => normalizedCoordinate f c a n ((chartAt E a) p))
      atTop (𝓝 (chartCoordinate a p v)))
    (hfix : ∀ᶠ n in atTop, τ (f n p) = τ p) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ) τ p v = 0 := by
  have h := mfderiv_eq_zero_of_coordinate_limit hf a hp hτ hv hfix
  rwa [chartVector_chartCoordinate a hp v] at h

/-- A local detector fixed by the original automorphism sequence annihilates
the native field constructed from its holomorphic coordinate limits. -/
theorem fieldOfCoordinateLimits_mfderiv_eq_zero {ι : Type*}
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a : ι → M) (V : ι → Opens E)
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set E))
    (h : ι → E → E) (hh : ∀ i, ContDiffOn ℂ ω (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate f c (a i))
      (h i) atTop (V i)) {p : M} {τ : M → ℂ}
    (hτ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω τ p)
    (hfix : ∀ᶠ n in atTop, τ (f n p) = τ p) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ) τ p (fieldOfCoordinateLimits hf a V hcover h hh hlim p) = 0 := by
  obtain ⟨i, hi⟩ := hcover p
  apply mfderiv_eq_zero_of_native_coordinate_limit (c := c) hf (a i) hi.1 hτ _ _ hfix
  rw [fieldOfCoordinateLimits_coordinate hf a V hcover h hh hlim i hi]
  exact (hlim i).tendsto_at hi.2

section NativeModel

open HolomorphicAutomorphismNormalFamily.AnalyticThreefold

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (ℂ × ComplexPlane₂) N]
  [IsManifold 𝓘(ℂ, ℂ × ComplexPlane₂) ω N]
  {fn : ℕ → HolomorphicAutomorphism 𝓘(ℂ, ℂ × ComplexPlane₂) N} {cn : ℕ → ℂ}

/-- Native threefold version: complex differentiability of the coordinate
limits is enough, since their analytic regularity was genuinely proved. -/
theorem fieldOfNativeCoordinateLimits_mfderiv_eq_zero {ι : Type*}
    (hf : Tendsto fn atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, ℂ × ComplexPlane₂) N)))
    (a : ι → N) (V : ι → Opens (ℂ × ComplexPlane₂))
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set (ℂ × ComplexPlane₂)))
    (h : ι → (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂))
    (hd : ∀ i, DifferentiableOn ℂ (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate fn cn (a i))
      (h i) atTop (V i)) {p : N} {τ : N → ℂ}
    (hτ : ContMDiffAt 𝓘(ℂ, ℂ × ComplexPlane₂) 𝓘(ℂ) ω τ p)
    (hfix : ∀ᶠ n in atTop, τ (fn n p) = τ p) :
    mfderiv 𝓘(ℂ, ℂ × ComplexPlane₂) 𝓘(ℂ) τ p
      (fieldOfNativeCoordinateLimits hf a V hcover h hd hlim p) = 0 :=
  fieldOfCoordinateLimits_mfderiv_eq_zero hf a V hcover h
    (fun i => contDiffOn_nativeModel_of_differentiableOn (V i).isOpen (hd i)) hlim hτ hfix

end NativeModel

end Wikipedia.HopfProblem.HolomorphicAutomorphismTangentDetector
