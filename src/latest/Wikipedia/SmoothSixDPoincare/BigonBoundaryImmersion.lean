import Wikipedia.SmoothSixDPoincare.BigonStripImmersion
import Wikipedia.SmoothSixDPoincare.BigonBoundaryParametrization
import Wikipedia.SmoothSixDPoincare.StripArcInjectivity
import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# Embedding and immersion near the assembled native bigon boundary

Full local equality with the actual strips transfers their injective native
derivatives to the glued map. Its boundary is injective by the checked strip
overlap relation. Compactness then gives one embedded immersive neighborhood
of the entire boundary, with the original map unchanged.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Pulling a native strip back by immersive coordinates preserves the injective derivative. -/
theorem injective_nativeDerivative_of_strip_germ
    {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁)
    {r : (ℝ × ℝ) → ℝ × ℝ} (hr : ContDiff ℝ ∞ r)
    {f : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (heq : EqOn f (k.map ∘ r) U) (hmap : MapsTo r U k.domain)
    {p : ℝ × ℝ} (hp : p ∈ U) (hi : Injective (fderiv ℝ r p)) :
    Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hgerm : f =ᶠ[𝓝 p] k.map ∘ r :=
    mem_of_superset (hU.mem_nhds hp) (fun _ hx => heq hx)
  rw [hgerm.mfderiv_eq]
  have hk := k.smooth.contMDiffAt (k.open_domain.mem_nhds (hmap hp))
  rw [mfderiv_comp p (hk.mdifferentiableAt (by simp))
    (hr.contMDiff.mdifferentiableAt (by simp))]
  have hri : Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) r p) := by
    rw [mfderiv_eq_fderiv]
    exact hi
  exact (k.derivative_injective (r p) (hmap hp)).comp hri

/-- The glued map is immersive on the full frontier, including both corners. -/
theorem injective_nativeDerivative_bigon_boundary {h : ℝ} (hh : 0 < h)
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hlowU : MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Icc 0 1) U)
    (huppV : MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Icc 0 1) V)
    (hmapU : MapsTo (lowerStripCoordinates h) U k.domain)
    (hmapV : MapsTo (upperStripCoordinates h) V l.domain)
    (hflo : EqOn f (k.map ∘ lowerStripCoordinates h) U)
    (hfhi : EqOn f (l.map ∘ upperStripCoordinates h) V) :
    ∀ p ∈ frontier (bigon h), Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  intro p hp
  obtain ⟨t, ht, rfl | rfl⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
  · exact injective_nativeDerivative_of_strip_germ k (contDiff_lowerStripCoordinates hh.ne')
      hU hflo hmapU (hlowU ht) (injective_fderiv_lowerStripCoordinates hh.ne' _)
  · exact injective_nativeDerivative_of_strip_germ l (contDiff_upperStripCoordinates hh.ne')
      hV hfhi hmapV (huppV ht) (injective_fderiv_upperStripCoordinates hh.ne' _)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The actual assembled map has one embedded immersive neighborhood of the entire boundary. -/
theorem exists_embedded_bigon_boundary_neighborhood {h : ℝ} (hh : 0 < h)
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover : ∀ p ∈ k.domain, ∀ q ∈ l.domain, k.map p = l.map q →
      p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap)
    {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hfront : frontier (bigon h) ⊆ U ∪ V)
    (hlowU : MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Icc 0 1) U)
    (huppV : MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Icc 0 1) V)
    (hmapU : MapsTo (lowerStripCoordinates h) U k.domain)
    (hmapV : MapsTo (upperStripCoordinates h) V l.domain)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V))
    (hflo : EqOn f (k.map ∘ lowerStripCoordinates h) U)
    (hfhi : EqOn f (l.map ∘ upperStripCoordinates h) V) :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ frontier (bigon h) ⊆ W ∧ W ⊆ U ∪ V ∧
      InjOn f W ∧ ∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t := by
    intro t ht
    rw [hflo (hlowU ht)]
    change k.map (lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [lowerStripCoordinates_lower]
    exact k.center t ht
  have hupp : ∀ t ∈ Icc (0 : ℝ) 1,
      f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t := by
    intro t ht
    rw [hfhi (huppV ht)]
    change l.map (upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) = b t
    rw [upperStripCoordinates_upper]
    exact l.center t ht
  have hinj := injOn_frontier_bigon_of_arcs hh k.center_injOn l.center_injOn hlow hupp
    (strip_center_coincidences_of_corner_overlap k l hover)
  have hi := injective_nativeDerivative_bigon_boundary hh k l hU hV hlowU huppV
    hmapU hmapV hflo hfhi
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  exact ManifoldImmersion.exists_open_embedded_immersive_neighborhood (hU.union hV) hf
    hcompact hfront hinj hi

end Wikipedia.SmoothSixDPoincare
