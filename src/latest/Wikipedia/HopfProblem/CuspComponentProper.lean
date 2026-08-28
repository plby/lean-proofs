import Wikipedia.HopfProblem.ToricCentralAction

/-!
# Properness of the component projection and compactness of the ray components

The saturation of a closed subset of `E₀` is a locally finite union of closed
translates. Its quotient image is therefore closed. Together with the already
proved finite fibres this makes the actual component projection proper.
Compactness of the central cusp fibre then proves compactness of `E₀`.
Using constant zero cusp data gives unconditional compactness of every ray
component of the toric space, without assuming a del Pezzo identification.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem componentProjection_saturation (K : Set (rayDivisor 0)) :
    quotientMap C ε ⁻¹' (componentProjection C ε hε '' K) =
      (Subtype.val : Tube (disc ε) → Space) ⁻¹'
        ⋃ v : Fin 2 → ℤ, centralTranslationHomeomorph C v ''
          ((Subtype.val : rayDivisor 0 → Space) '' K) := by
  let := tubeAction C (disc ε)
  ext a
  constructor
  · rintro ⟨x, hx, he⟩
    have horb := Quotient.exact he.symm
    change a ∈ MulAction.orbit LatticeGroup (componentLift ε hε x) at horb
    obtain ⟨g, hg⟩ := horb
    have hspace : centralTranslationHomeomorph C g.toAdd (x : Space) = (a : Space) :=
      (centralTranslationHomeomorph_eq_twistedTranslate C g.toAdd x
        (time_eq_zero_of_mem_rayDivisor x.2)).trans (congrArg Subtype.val hg)
    exact Set.mem_iUnion.mpr ⟨g.toAdd, (x : Space), ⟨x, hx, rfl⟩, hspace⟩
  · intro ha
    obtain ⟨v, y, ⟨x, hx, rfl⟩, he⟩ := Set.mem_iUnion.mp ha
    refine ⟨x, hx, ?_⟩
    have hspace : twistedTranslate C v (x : Space) = (a : Space) :=
      (centralTranslationHomeomorph_eq_twistedTranslate C v x
        (time_eq_zero_of_mem_rayDivisor x.2)).symm.trans he
    have htube : tubeTranslate C (disc ε) v (componentLift ε hε x) = a := Subtype.ext hspace
    have hq := congrArg (quotientMap C ε) htube
    rw [quotientMap_translate] at hq
    exact hq

theorem componentProjection_isClosedMap : IsClosedMap (componentProjection C ε hε) := by
  intro K hK
  let K' : Set Space := (Subtype.val : rayDivisor 0 → Space) '' K
  have hK' : IsClosed K' := (rayDivisor_isClosed 0).isClosedMap_subtype_val K hK
  have hsub : K' ⊆ rayDivisor 0 := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hclosed : IsClosed (⋃ v : Fin 2 → ℤ, centralTranslationHomeomorph C v '' K') :=
    (centralTranslation_images_locallyFinite C hsub).isClosed_iUnion
      (fun v => (centralTranslationHomeomorph C v).isClosedMap K' hK')
  have hq : IsQuotientMap (quotientMap C ε) := isQuotientMap_quotient_mk'
  apply hq.isClosed_preimage.mp
  rw [componentProjection_saturation]
  exact hclosed.preimage continuous_subtype_val

theorem componentProjection_proper (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : IsProperMap (componentProjection C ε hε) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨componentProjection_continuous C ε hε, componentProjection_isClosedMap C ε hε,
      fun x => (componentProjection_fibre_finite C ε hε hε1 hC hR x).isCompact⟩

include hε in
theorem component_compactSpace_of_cusp (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : CompactSpace (rayDivisor 0) := by
  have h := (componentProjection_proper C ε hε hε1 hC hR).isCompact_preimage
    (central_fibre_compact C ε hε hε1 hC hR)
  have he : componentProjection C ε hε ⁻¹' (projection C ε ⁻¹' {0}) = univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, projection_componentProjection,
      Set.mem_univ]
  rw [he] at h
  exact ⟨h⟩

end Wikipedia.HopfProblem.CuspQuotient

namespace Wikipedia.HopfProblem.ToricSpace

theorem zero_rayDivisor_compactSpace : CompactSpace (rayDivisor 0) := by
  let C : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 0
  have hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 (1 : ℝ)) := by
    intro i j
    exact contDiffOn_const
  obtain ⟨ε, hε, _, hε1, hR, hCε⟩ := CuspQuotient.exists_admissible_radius C (by norm_num) hC
  exact CuspQuotient.component_compactSpace_of_cusp C ε hε hε1 hCε hR

theorem rayDivisor_isCompact (v : Fin 2 → ℤ) : IsCompact (rayDivisor v) := by
  have h0 : IsCompact (rayDivisor 0) := isCompact_iff_compactSpace.mpr zero_rayDivisor_compactSpace
  rw [← translate_zero_rayDivisor v]
  exact h0.image (translate_holomorphic v).continuous

instance rayDivisor_compactSpace (v : Fin 2 → ℤ) : CompactSpace (rayDivisor v) :=
  isCompact_iff_compactSpace.mp (rayDivisor_isCompact v)

end Wikipedia.HopfProblem.ToricSpace
