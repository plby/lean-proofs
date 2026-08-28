import Wikipedia.SmoothSixDPoincare.StripNormalDetector
import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity
import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood

/-!
# A genuine clean embedded neighborhood of the strip center

Compact local injectivity supplies one neighborhood for the strip map and
one for its normal detector. Their intersection is immersive and lies inside
the prescribed coordinate domain. Detector injectivity shows that the normal
coordinate vanishes exactly on the center. Compactness gives a uniform
positive strip width, including both endpoints.
-/

noncomputable section

open Set Function Metric Topology
open scoped ContDiff Manifold InnerProductSpace

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]

/-- The coordinate strip is clean, embedded, and immersive on a positive-width neighborhood. -/
theorem exists_clean_strip_neighborhood {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = center t) (hD : ∀ t, normalDerivative F t = v t)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, v t ≠ 0)
    {O : Set (Space A B)} (hO : IsOpen O) (hcenterO : MapsTo center (Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ W ∧ InjOn F W ∧ MapsTo F W O ∧
      (∀ p ∈ W, Injective (fderiv ℝ F p)) ∧
      (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
      IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => F p) := by
  let K := Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hFK : InjOn F K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := by
      simpa only [hc, center] using congrArg (fun q : Space A B => q.1.1) heq
    exact Prod.ext htu rfl
  have hiF : ∀ p ∈ K, Injective (fderiv ℝ F p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    apply injective_fderiv_at_center (hF.contDiffAt.differentiableAt (by simp)) hc
    rw [hD t]
    exact hn t ht
  have hiFM : ∀ p ∈ K, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Space A B) F p) := by
    intro p hp
    rw [mfderiv_eq_fderiv]
    exact hiF p hp
  obtain ⟨V, hV, hKV, hinjV⟩ :=
    ManifoldImmersion.exists_open_injOn_near_compact hF.contMDiff hK hFK hiFM
  let Q := detector v F
  have hQ : ContDiff ℝ ∞ Q := contDiff_detector hv hF
  have hQK : InjOn Q K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := congrArg Prod.fst heq
    exact Prod.ext htu rfl
  have hiQ : ∀ p ∈ K, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) Q p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    rw [mfderiv_eq_fderiv]
    exact injective_fderiv_detector_at_center hv hF hc hD (hn t ht)
  obtain ⟨T, hT, hKT, hinjT⟩ :=
    ManifoldImmersion.exists_open_injOn_near_compact hQ.contMDiff hK hQK hiQ
  let I := {p : ℝ × ℝ | Injective (fderiv ℝ F p)}
  have hI : IsOpen I := ContinuousLinearMap.isOpen_injective.preimage
    (hF.continuous_fderiv (by simp))
  let W := ((V ∩ T) ∩ I) ∩ (F ⁻¹' O ∩ (fun p : ℝ × ℝ => (p.1, 0)) ⁻¹' T)
  have hW : IsOpen W := ((hV.inter hT).inter hI).inter
    ((hO.preimage hF.continuous).inter (hT.preimage (continuous_fst.prodMk continuous_const)))
  have hKW : K ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have hpK : (t, (0 : ℝ)) ∈ K := ⟨ht, rfl⟩
    refine ⟨⟨⟨hKV hpK, hKT hpK⟩, hiF _ hpK⟩, ⟨?_, hKT hpK⟩⟩
    change F (t, 0) ∈ O
    rw [hc]
    exact hcenterO ht
  obtain ⟨ε, hε, hprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset isCompact_Icc hW hKW
  have hrect : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  have hinjW : InjOn F W := hinjV.mono (fun _ hp => hp.1.1.1)
  refine ⟨ε, hε, W, hW, hrect, hinjW, fun _ hp => hp.2.1,
    fun _ hp => hp.1.2, ?_, ?_⟩
  · rintro ⟨t, s⟩ hp
    constructor
    · intro hz
      have heq : Q (t, s) = Q (t, 0) := by
        change detector v F (t, s) = detector v F (t, 0)
        rw [detector_zero hc]
        change (t, ⟪v t, (F (t, s)).2⟫_ℝ) = (t, 0)
        rw [hz, inner_zero_right]
      exact congrArg Prod.snd (hinjT hp.1.1.2 hp.2.2 heq)
    · intro hs
      change s = 0 at hs
      subst s
      rw [hc]
      rfl
  · let R := Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε
    let : CompactSpace R := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    apply (hF.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjW (hrect p.property) (hrect q.property) hpq)

end Wikipedia.SmoothSixDPoincare.StripCoordinates
