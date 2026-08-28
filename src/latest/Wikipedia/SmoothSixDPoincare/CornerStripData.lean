import Wikipedia.SmoothSixDPoincare.NativeTransverseCorner
import Wikipedia.SmoothSixDPoincare.StripReflection

/-!
# Shared native corner maps and clean strip data

These records retain the actual maps and all their proved smoothness,
embedding, and contact properties. Swapping the two corner axes preserves
the same native map, so two constructed strips can use common corner germs.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- An actual clean native corner with its two specified boundary arcs. -/
structure CleanCornerPatch (S T : Set M) (a b : ℝ → M) where
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_zero : (0 : ℝ × ℝ) ∈ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : InjOn map domain
  derivative_injective : ∀ p ∈ domain, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  sheets : ∀ p ∈ domain, (map p ∈ S ↔ p.2 = 0) ∧ (map p ∈ T ↔ p.1 = 0)
  axis_first : ∀ t, (t, 0) ∈ domain → map (t, 0) = a t
  axis_second : ∀ t, (0, t) ∈ domain → map (0, t) = b t

namespace CleanCornerPatch

variable {S T : Set M} {a b : ℝ → M} (c : CleanCornerPatch (E := E) S T a b)

/-- Interchange the two axes of the same native corner map. -/
def swap : CleanCornerPatch (E := E) T S b a := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have he : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (e : (ℝ × ℝ) → ℝ × ℝ) :=
    e.contDiff.contMDiff
  refine {
    domain := e ⁻¹' c.domain
    open_domain := c.open_domain.preimage e.continuous
    contains_zero := ?_
    map := c.map ∘ e
    smooth := c.smooth.comp he.contMDiffOn (fun _ hp => hp)
    injective := ?_
    derivative_injective := ?_
    sheets := fun p hp => ⟨(c.sheets (e p) hp).2, (c.sheets (e p) hp).1⟩
    axis_first := fun t ht => c.axis_second t ht
    axis_second := fun t ht => c.axis_first t ht }
  · change e 0 ∈ c.domain
    rw [map_zero]
    exact c.contains_zero
  · intro p hp q hq hpq
    exact e.injective (c.injective hp hq hpq)
  · intro p hp
    have hc := c.smooth.contMDiffAt (c.open_domain.mem_nhds hp)
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
    exact (c.derivative_injective (e p) hp).comp
      (PartialChart.bijective_mfderiv e.toDiffeomorph.toPartialDiffeomorph (mem_univ p)).1

theorem swap_map (p : ℝ × ℝ) : c.swap.map p = c.map p.swap := rfl

end CleanCornerPatch

/-- A positive-width native strip with fixed full endpoint corner germs and exact sheet contacts. -/
structure CleanStripPatch (S T : Set M) (a : ℝ → M) (k₀ k₁ : (ℝ × ℝ) → M) where
  width : ℝ
  width_pos : 0 < width
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_strip : Icc (0 : ℝ) 1 ×ˢ Icc (-width) width ⊆ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : InjOn map domain
  closed_embedding : IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-width) width => map p)
  derivative_injective : ∀ p ∈ domain, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  first_sheet : ∀ p ∈ domain, map p ∈ S ↔ p.2 = 0
  second_sheet : ∀ p ∈ domain, map p ∈ T ↔ p.1 = 0 ∨ p.1 = 1
  center : ∀ t ∈ Icc (0 : ℝ) 1, map (t, 0) = a t
  left_germ : map =ᶠ[𝓝 (0, 0)] k₀
  right_germ : map =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {D Z N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]

/-- Construct the shared corner record directly from the native transverse crossing. -/
theorem nonempty_cleanCornerPatch_of_native_crossing {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G)
    (x : N) (y : P) (hxy : G y = F x)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0) :
    Nonempty (CleanCornerPatch (E := E) (range F) (range G)
      (fun t => F (NativeParametrization.centered (D := D) x (t • u)))
      (fun t => G (NativeParametrization.centered (D := Z) y (t • v)))) := by
  obtain ⟨U, hU, h0U, k, hk, hinj, _, _, hi, hsheets, hleft, hright⟩ :=
    exists_native_clean_corner hF hG hembF hembG x y hxy hdim ht hu hv
      isOpen_univ (mem_univ _)
  exact ⟨{
    domain := U
    open_domain := hU
    contains_zero := h0U
    map := k
    smooth := hk
    injective := hinj
    derivative_injective := hi
    sheets := hsheets
    axis_first := hleft
    axis_second := hright }⟩

end Wikipedia.SmoothSixDPoincare
