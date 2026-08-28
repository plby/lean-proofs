import Wikipedia.HopfProblem.DegreeCollapseFlatLocalCorrection

/-!
# Full endpoint germs with the entire axis first jet retained

The local endpoint maps need only be smooth on their actual open domains.
Two separated compact cutoffs insert them into a global model, keeping the
values and full derivatives on the entire scalar axis unchanged.
-/

noncomputable section

open Set Filter Function
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Match both complete local endpoint maps without altering any axis first jet. -/
theorem exists_axis_germ_correction {H R₀ R₁ : (ℝ × V) → F} {U₀ U₁ : Set (ℝ × V)}
    {p q : ℝ} (hpq : p < q) (hH : ContDiff ℝ ∞ H)
    (hR₀ : ContDiffOn ℝ ∞ R₀ U₀) (hR₁ : ContDiffOn ℝ ∞ R₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0 : (p, (0 : V)) ∈ U₀) (h1 : (q, (0 : V)) ∈ U₁)
    (hv₀ : (fun s : ℝ => R₀ (s, 0)) =ᶠ[𝓝 p] (fun s => H (s, 0)))
    (hv₁ : (fun s : ℝ => R₁ (s, 0)) =ᶠ[𝓝 q] (fun s => H (s, 0)))
    (hd₀ : (fun s : ℝ => fderiv ℝ R₀ (s, 0)) =ᶠ[𝓝 p]
      (fun s => fderiv ℝ H (s, 0)))
    (hd₁ : (fun s : ℝ => fderiv ℝ R₁ (s, 0)) =ᶠ[𝓝 q]
      (fun s => fderiv ℝ H (s, 0))) :
    ∃ G : (ℝ × V) → F, ContDiff ℝ ∞ G ∧
      (∀ s : ℝ, G (s, 0) = H (s, 0)) ∧
      (∀ s : ℝ, fderiv ℝ G (s, 0) = fderiv ℝ H (s, 0)) ∧
      (G =ᶠ[𝓝 (p, (0 : V))] R₀) ∧ (G =ᶠ[𝓝 (q, (0 : V))] R₁) := by
  obtain ⟨I₀, hI₀sub, hI₀, h0I⟩ := mem_nhds_iff.mp (hv₀.and hd₀)
  obtain ⟨I₁, hI₁sub, hI₁, h1I⟩ := mem_nhds_iff.mp (hv₁.and hd₁)
  let W₀ := U₀ ∩ Prod.fst ⁻¹' (I₀ ∩ Iio ((p + q) / 2))
  let W₁ := U₁ ∩ Prod.fst ⁻¹' (I₁ ∩ Ioi ((p + q) / 2))
  have hW₀ : IsOpen W₀ := hU₀.inter ((hI₀.inter isOpen_Iio).preimage continuous_fst)
  have hW₁ : IsOpen W₁ := hU₁.inter ((hI₁.inter isOpen_Ioi).preimage continuous_fst)
  have h0W : (p, (0 : V)) ∈ W₀ := ⟨h0, h0I, by change p < (p + q) / 2; linarith⟩
  have h1W : (q, (0 : V)) ∈ W₁ := ⟨h1, h1I, by change (p + q) / 2 < q; linarith⟩
  let K : Set (ℝ × V) := univ ×ˢ {0}
  have hv0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : R₀ y = H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : fderiv ℝ R₀ y = fderiv ℝ H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G₀, hG₀, hg₀, -, hvG₀, hdG₀⟩ := exists_flat_local_correction hH
    (hR₀.mono inter_subset_left) hW₀ h0W hv0 hd0
  have hv1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : R₁ y = G₀ y := by
    rw [hvG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : fderiv ℝ R₁ y = fderiv ℝ G₀ y := by
    rw [hdG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G, hG, hg₁, hoff, hvG, hdG⟩ := exists_flat_local_correction hG₀
    (hR₁.mono inter_subset_left) hW₁ h1W hv1 hd1
  have h0not : (p, (0 : V)) ∉ W₁ := by
    intro hh
    have hbad : (p + q) / 2 < p := hh.2.2
    linarith
  refine ⟨G, hG, ?_, ?_, (hoff _ h0not).trans hg₀, hg₁⟩
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨mem_univ s, rfl⟩
    exact (hvG hs).trans (hvG₀ hs)
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨mem_univ s, rfl⟩
    exact (hdG hs).trans (hdG₀ hs)

end Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates
