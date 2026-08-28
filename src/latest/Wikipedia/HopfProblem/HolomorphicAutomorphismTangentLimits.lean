import Wikipedia.HopfProblem.HolomorphicAutomorphismTopology
import Wikipedia.HopfProblem.HolomorphicAutomorphismLinearization
import Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluing
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalytic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Native tangent fields from normalized automorphism limits

Normalized coordinate differences of genuine holomorphic automorphisms
converging to the identity satisfy the derivative transition law in the limit.
Thus holomorphic coordinate limits glue to an actual section of the original
tangent bundle. Transition compatibility is proved, not assumed.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismTangentLimits

open HolomorphicAutomorphismTangentGluing

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The rescaled displacement of the actual automorphism in a preferred chart. -/
def normalizedCoordinate (f : ℕ → HolomorphicAutomorphism 𝓘(ℂ, E) M)
    (c : ℕ → ℂ) (a : M) (n : ℕ) (z : E) : E :=
  c n • ((chartAt E a) (f n ((chartAt E a).symm z)) - z)

variable {f : ℕ → HolomorphicAutomorphism 𝓘(ℂ, E) M} {c : ℕ → ℂ}

/-- The native automorphism topology gives convergence at each fixed point;
this uses continuous evaluation in the compact-open topology. -/
theorem tendsto_apply_of_tendsto_one
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M))) (x : M) :
    Tendsto (fun n => f n x) atTop (𝓝 x) := by
  have he : Continuous (fun g : C(M, M) => g x) := continuous_eval_const x
  have hc := he.comp (HolomorphicAutomorphism.continuous_toContinuousMap 𝓘(ℂ, E) M)
  simpa only [Function.comp_def, HolomorphicAutomorphism.toContinuousMap_apply,
    HolomorphicAutomorphism.one_apply] using (hc.tendsto 1).comp hf

variable [IsManifold 𝓘(ℂ, E) ω M]

/-- The original preferred-chart transition is strictly differentiable at every
point of the actual overlap. -/
theorem chartTransition_hasStrictFDerivAt (a b : M) {x : M}
    (ha : x ∈ (chartAt E a).source) (hb : x ∈ (chartAt E b).source) :
    HasStrictFDerivAt ((chartAt E b) ∘ (chartAt E a).symm)
      (fderiv ℂ ((chartAt E b) ∘ (chartAt E a).symm) ((chartAt E a) x))
      ((chartAt E a) x) := by
  have h₁ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E a).symm
      ((chartAt E a) x) :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas a) ((chartAt E a).mapsTo ha)
  have h₂ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E b)
      ((chartAt E a).symm ((chartAt E a) x)) := by
    rw [(chartAt E a).left_inv ha]
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas b) hb
  exact (h₂.comp ((chartAt E a) x) h₁).contDiffAt.hasStrictFDerivAt (by simp)

/-- Two pointwise normalized-coordinate limits on an overlap are related by
the genuine derivative of the coordinate change. -/
theorem coordinateLimits_transition
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a b : M) {x : M} (ha : x ∈ (chartAt E a).source)
    (hb : x ∈ (chartAt E b).source) {u v : E}
    (hu : Tendsto (fun n => normalizedCoordinate f c a n ((chartAt E a) x))
      atTop (𝓝 u))
    (hv : Tendsto (fun n => normalizedCoordinate f c b n ((chartAt E b) x))
      atTop (𝓝 v)) :
    fderiv ℂ ((chartAt E b) ∘ (chartAt E a).symm) ((chartAt E a) x) u = v := by
  have hfx := tendsto_apply_of_tendsto_one hf x
  have ha' : Tendsto (fun n => (chartAt E a) (f n x)) atTop
      (𝓝 ((chartAt E a) x)) := ((chartAt E a).continuousAt ha).tendsto.comp hfx
  have hsource : Tendsto (fun n => c n • ((chartAt E a) (f n x) - (chartAt E a) x))
      atTop (𝓝 u) := by
    simpa only [normalizedCoordinate, (chartAt E a).left_inv ha] using hu
  have htarget : Tendsto (fun n => c n • ((chartAt E b) (f n x) - (chartAt E b) x))
      atTop (𝓝 v) := by
    simpa only [normalizedCoordinate, (chartAt E b).left_inv hb] using hv
  have hlin := HolomorphicAutomorphismLinearization.tendsto_scaled_difference
    (chartTransition_hasStrictFDerivAt a b ha hb) ha' tendsto_const_nhds hsource
  have hmem : ∀ᶠ n in atTop, f n x ∈ (chartAt E a).source :=
    hfx.eventually ((chartAt E a).open_source.mem_nhds ha)
  have hlin' : Tendsto (fun n => c n • ((chartAt E b) (f n x) - (chartAt E b) x))
      atTop (𝓝 (fderiv ℂ ((chartAt E b) ∘ (chartAt E a).symm)
        ((chartAt E a) x) u)) := by
    apply hlin.congr'
    filter_upwards [hmem] with n hn
    simp only [Function.comp_apply, (chartAt E a).left_inv hn, (chartAt E a).left_inv ha]
  exact tendsto_nhds_unique hlin' htarget

/-- Actual locally uniform limits of the normalized native automorphisms
satisfy the tangent transition law on every overlap. -/
theorem chartCompatible_of_coordinateLimits {ι : Type*}
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a : ι → M) (V : ι → Opens E) (h : ι → E → E)
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate f c (a i))
      (h i) atTop (V i)) : ChartCompatible a V h := by
  intro i j x hi hj
  exact coordinateLimits_transition hf (a i) (a j) hi.1 hj.1
    ((hlim i).tendsto_at hi.2) ((hlim j).tendsto_at hj.2)

/-- Holomorphic normalized coordinate limits of genuine automorphisms define
a global native holomorphic vector field, with no transition hypothesis. -/
def fieldOfCoordinateLimits {ι : Type*}
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a : ι → M) (V : ι → Opens E)
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set E))
    (h : ι → E → E) (hh : ∀ i, ContDiffOn ℂ ω (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate f c (a i))
      (h i) atTop (V i)) : HolomorphicVectorFields.Field E M :=
  glueChartFields a V hcover h hh (chartCompatible_of_coordinateLimits hf a V h hlim)

/-- The field has exactly the prescribed coordinates in the original tangent charts. -/
theorem fieldOfCoordinateLimits_coordinate {ι : Type*}
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a : ι → M) (V : ι → Opens E)
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set E))
    (h : ι → E → E) (hh : ∀ i, ContDiffOn ℂ ω (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate f c (a i))
      (h i) atTop (V i)) (i : ι) {x : M} (hx : x ∈ chartDomain (a i) (V i : Set E)) :
    chartCoordinate (a i) x (fieldOfCoordinateLimits hf a V hcover h hh hlim x) =
      h i ((chartAt E (a i)) x) :=
  glueChartFields_coordinate a V hcover h hh _ i hx

/-- The resulting native field is nonzero exactly when a coordinate limit
has a nonzero value in one of the actual chart domains. -/
theorem fieldOfCoordinateLimits_ne_zero_iff {ι : Type*}
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (a : ι → M) (V : ι → Opens E)
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set E))
    (h : ι → E → E) (hh : ∀ i, ContDiffOn ℂ ω (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate f c (a i))
      (h i) atTop (V i))
    (hV : ∀ i, (V i : Set E) ⊆ (chartAt E (a i)).target) :
    fieldOfCoordinateLimits hf a V hcover h hh hlim ≠ 0 ↔
      ∃ i q, q ∈ V i ∧ h i q ≠ 0 :=
  glueChartFields_ne_zero_iff a V hcover h hh _ hV

section NativeModel

open HolomorphicAutomorphismNormalFamily.AnalyticThreefold

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (ℂ × ComplexPlane₂) N]
  [IsManifold 𝓘(ℂ, ℂ × ComplexPlane₂) ω N]
  {fn : ℕ → HolomorphicAutomorphism 𝓘(ℂ, ℂ × ComplexPlane₂) N} {cn : ℕ → ℂ}

/-- On the original threefold model, complex differentiability of the coordinate
limits already gives the analytic regularity required for the native field.
Neither analytic upgrade nor tangent compatibility is an input premise. -/
def fieldOfNativeCoordinateLimits {ι : Type*}
    (hf : Tendsto fn atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, ℂ × ComplexPlane₂) N)))
    (a : ι → N) (V : ι → Opens (ℂ × ComplexPlane₂))
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set (ℂ × ComplexPlane₂)))
    (h : ι → (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂))
    (hd : ∀ i, DifferentiableOn ℂ (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate fn cn (a i))
      (h i) atTop (V i)) : HolomorphicVectorFields.Field (ℂ × ComplexPlane₂) N :=
  fieldOfCoordinateLimits hf a V hcover h
    (fun i => contDiffOn_nativeModel_of_differentiableOn (V i).isOpen (hd i)) hlim

/-- The native-model construction keeps the actual limiting chart coefficients. -/
theorem fieldOfNativeCoordinateLimits_coordinate {ι : Type*}
    (hf : Tendsto fn atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, ℂ × ComplexPlane₂) N)))
    (a : ι → N) (V : ι → Opens (ℂ × ComplexPlane₂))
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set (ℂ × ComplexPlane₂)))
    (h : ι → (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂))
    (hd : ∀ i, DifferentiableOn ℂ (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate fn cn (a i))
      (h i) atTop (V i)) (i : ι) {x : N}
    (hx : x ∈ chartDomain (a i) (V i : Set (ℂ × ComplexPlane₂))) :
    chartCoordinate (a i) x (fieldOfNativeCoordinateLimits hf a V hcover h hd hlim x) =
      h i ((chartAt (ℂ × ComplexPlane₂) (a i)) x) :=
  fieldOfCoordinateLimits_coordinate hf a V hcover h _ hlim i hx

/-- A nonzero genuine coordinate limit is equivalent to a nonzero native field
also when only complex differentiability of the limits was supplied. -/
theorem fieldOfNativeCoordinateLimits_ne_zero_iff {ι : Type*}
    (hf : Tendsto fn atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, ℂ × ComplexPlane₂) N)))
    (a : ι → N) (V : ι → Opens (ℂ × ComplexPlane₂))
    (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set (ℂ × ComplexPlane₂)))
    (h : ι → (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂))
    (hd : ∀ i, DifferentiableOn ℂ (h i) (V i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn (normalizedCoordinate fn cn (a i))
      (h i) atTop (V i))
    (hV : ∀ i, (V i : Set (ℂ × ComplexPlane₂)) ⊆ (chartAt (ℂ × ComplexPlane₂) (a i)).target) :
    fieldOfNativeCoordinateLimits hf a V hcover h hd hlim ≠ 0 ↔
      ∃ i q, q ∈ V i ∧ h i q ≠ 0 :=
  fieldOfCoordinateLimits_ne_zero_iff hf a V hcover h _ hlim hV

end NativeModel

end Wikipedia.HopfProblem.HolomorphicAutomorphismTangentLimits
