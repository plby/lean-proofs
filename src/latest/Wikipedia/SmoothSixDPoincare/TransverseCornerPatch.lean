import Wikipedia.SmoothSixDPoincare.CleanTransverseSheetChart

/-!
# A constructed clean corner between two transverse embedded sheets

Choose a unit direction in each sheet. The native transverse chart then gives
an actual embedded immersive planar corner. Its two axes agree with the sheet
arcs, and its off-axis points avoid both full sheet patch images. Smoothness
holds on an open ambient neighborhood of a positive-size closed quadrant,
including its corner and both boundary edges.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def cornerLinear (u : D) (v : Z) : (ℝ × ℝ) →L[ℝ] (D × Z) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v)

theorem cornerLinear_apply (u : D) (v : Z) (p : ℝ × ℝ) :
    cornerLinear u v p = (p.1 • u, p.2 • v) := rfl

theorem injective_cornerLinear {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0) :
    Injective (cornerLinear u v) := by
  intro p q hpq
  exact Prod.ext ((smul_left_injective ℝ hu) (congrArg Prod.fst hpq))
    ((smul_left_injective ℝ hv) (congrArg Prod.snd hpq))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞)

def cornerMap (u : D) (v : Z) : (ℝ × ℝ) → M := Φ ∘ cornerLinear u v

theorem contMDiffOn_cornerMap (u : D) (v : Z) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (cornerMap Φ u v)
      (cornerLinear u v ⁻¹' Φ.source) :=
  Φ.contMDiffOn_toFun.comp (cornerLinear u v).contDiff.contMDiff.contMDiffOn (fun _ hx => hx)

theorem injOn_cornerMap {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0) :
    InjOn (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) := by
  intro p hp q hq heq
  exact injective_cornerLinear hu hv (Φ.toPartialEquiv.injOn hp hq heq)

theorem injective_mfderiv_cornerMap {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0)
    {p : ℝ × ℝ} (hp : p ∈ cornerLinear u v ⁻¹' Φ.source) :
    Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (cornerMap Φ u v) p) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, D × Z) ∞ (cornerLinear u v) :=
    (cornerLinear u v).contDiff.contMDiff
  rw [cornerMap, mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp)
    (hL.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (cornerLinear u v).fderiv]
  exact (PartialChart.bijective_mfderiv Φ hp).1.comp (injective_cornerLinear hu hv)

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- A clean, smooth, embedded corner is constructed from actual native transversality. -/
theorem exists_clean_transverse_corner {f : D → M} {g : Z → M}
    {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V)
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hembf : IsEmbedding (fun x : U => f x)) (hembg : IsEmbedding (fun z : V => g z))
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {u : D} {v : Z} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ a : ℝ, 0 < a ∧ ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a ⊆ W ∧ ∃ k : (ℝ × ℝ) → M,
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧ InjOn k W ∧ MapsTo k W O ∧
        Topology.IsClosedEmbedding (fun p : Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a => k p) ∧
        (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
        (∀ p ∈ W, (k p ∈ f '' U ↔ p.2 = 0) ∧ (k p ∈ g '' V ↔ p.1 = 0)) ∧
        (∀ s ∈ Icc (0 : ℝ) a, k (s, 0) = f (s • u)) ∧
        (∀ t ∈ Icc (0 : ℝ) a, k (0, t) = g (t • v)) := by
  obtain ⟨a, ha, Φ, hprod, -, htarget, hleft, hright, himages⟩ :=
    exists_clean_simultaneous_sheetChart hU hV h0U h0V hf hg hzero hembf hembg hdim ht hO h0O
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  let L := TransverseCoordinates.cornerLinear u v
  let W := L ⁻¹' Φ.source
  let k := TransverseCoordinates.cornerMap Φ u v
  let K := Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a
  have hW : IsOpen W := Φ.open_source.preimage L.continuous
  have hKW : K ⊆ W := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    apply hprod
    change s • u ∈ closedBall 0 a ∧ t • v ∈ closedBall 0 a
    constructor
    · simpa only [mem_closedBall, dist_zero_right, norm_smul, hu, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hs.1] using hs.2
    · simpa only [mem_closedBall, dist_zero_right, norm_smul, hv, mul_one,
        Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W :=
    TransverseCoordinates.contMDiffOn_cornerMap Φ u v
  have hinj : InjOn k W := TransverseCoordinates.injOn_cornerMap Φ hu0 hv0
  have hemb : IsClosedEmbedding (fun p : K => k p) := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    apply (continuousOn_iff_continuous_domRestrict.mp (hk.continuousOn.mono hKW)).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinj (hKW p.property) (hKW q.property) hpq)
  refine ⟨a, ha, W, hW, hKW, k, hk, hinj, ?_, hemb, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact htarget (Φ.map_source' hp)
  · intro p hp
    exact TransverseCoordinates.injective_mfderiv_cornerMap Φ hu0 hv0 hp
  · intro p hp
    have him := himages (L p) hp
    simpa only [L, k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, smul_eq_zero, hu0, hv0,
      or_false] using him
  · intro s hs
    have hs0 : (s, 0) ∈ W := hKW ⟨hs, ⟨le_rfl, ha.le⟩⟩
    have haxis : (s • u, 0) ∈ Φ.source := by
      change L (s, 0) ∈ Φ.source at hs0
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using hs0
    simpa only [k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hleft (s • u) haxis
  · intro t ht
    have h0t : (0, t) ∈ W := hKW ⟨⟨le_rfl, ha.le⟩, ht⟩
    have haxis : (0, t • v) ∈ Φ.source := by
      change L (0, t) ∈ Φ.source at h0t
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using h0t
    simpa only [k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hright (t • v) haxis

end Wikipedia.SmoothSixDPoincare
