import Wikipedia.HopfProblem.CuspCentralHomologySpecializationTransport

/-!
# The independently prescribed cusp collapse on actual first singular homology

The collapse here is the previously defined straightened polar/honeycomb
map, not a map chosen to have the desired homology.  The constructed
controlled deformation identifies its restriction on each chosen small
nonzero fibre with an actual retraction endpoint.  Consequently its
genuine singular first-homology map is the source lattice projection,
is surjective, and has kernel exactly the integral image of `M₀ - 1`.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspQuotient CuspRetraction CuspControlledRetraction
open SingularMayerVietoris

theorem cuspLatticeProjection_surjective :
    Function.Surjective CuspUniformization.cuspLatticeProjection := by
  intro v
  exact ⟨CuspUniformization.sourcePeriodCoordinates.symm (0, v),
    CuspUniformization.cuspLatticeProjection_sourcePeriodCoordinates_symm (0, v)⟩

theorem cuspLatticeProjection_eq_zero_iff_monodromy_image (v : Lattice) :
    CuspUniformization.cuspLatticeProjection v = 0 ↔
      ∃ w : Lattice, (M₀ - 1) *ᵥ w = v :=
  (CuspUniformization.cuspLatticeProjection_eq_zero_iff v).trans
    ((M₀_sub_one_kernel v).trans (M₀_sub_one_range v).symm)

/-- The genuine source collapse on every sufficiently small nonzero
fibre induces the exact integral degree-one specialization map.  Its
continuity, markings, surjectivity, and monodromy-image kernel are all
derived, without a supplied retraction or a supplied homology map. -/
theorem exists_prescribed_specialization_singularH1
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (_hη : 0 < η), η ≤ η₀ →
        ∀ (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ < η) (hηr : η < r),
          ∃ hc : Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη.le),
            ∃ ef : SingularHomology (ActualQuotientFibre C r t) 1 ≃ₗ[ℤ] Lattice,
              ∃ eq : SingularHomology (QuotientCentralFibre C r) 1 ≃ₗ[ℤ] (Fin 2 → ℤ),
                (∀ a, eq (singularHomologyMap
                    ⟨prescribedActualFibreCollapse C r hr hηr t ht htη.le, hc⟩ 1 a) =
                  CuspUniformization.cuspLatticeProjection (ef a)) ∧
                Function.Surjective (singularHomologyMap
                  ⟨prescribedActualFibreCollapse C r hr hηr t ht htη.le, hc⟩ 1) ∧
                (∀ a, singularHomologyMap
                    ⟨prescribedActualFibreCollapse C r hr hηr t ht htη.le, hc⟩ 1 a = 0 ↔
                  ∃ v : Lattice, (M₀ - 1) *ᵥ v = ef a) := by
  obtain ⟨ηc, hηc, hηcr, hηc1, hret⟩ :=
    exists_controlled_actual_fibre_retraction C hr hC
  obtain ⟨ηa, hηa, _hηar, hηa1, hRa, _hCa⟩ := exists_admissible_radius C hr hC
  refine ⟨min ηc ηa, lt_min hηc hηa, (min_le_left _ _).trans_lt hηcr,
    (min_le_left _ _).trans_lt hηc1, ?_⟩
  intro η hη hηη₀ t ht htη hηr
  obtain ⟨R, hR, H, hmono, hend⟩ :=
    hret η hη (hηη₀.trans (min_le_left _ _)) t ht htη.le
  obtain ⟨hc, hendpoint, _hrep⟩ := hend hηr
  have hη1 : η < 1 := (hηη₀.trans (min_le_right _ _)).trans_lt hηa1
  have hDrift : SmallDrift C η := hRa.mono (hηη₀.trans (min_le_right _ _))
  obtain ⟨ef, eq, hm⟩ := retractedFibreMap_singularH1_projection C r η η hη le_rfl
    hηr.le hC R hR H hmono hη1 hDrift t ht htη
  have hmap : retractedFibreMap C r η η le_rfl R t htη =
      (⟨prescribedActualFibreCollapse C r hr hηr t ht htη.le, hc⟩ :
        C(ActualQuotientFibre C r t, QuotientCentralFibre C r)) := by
    apply ContinuousMap.ext
    intro q
    exact hendpoint q
  rw [hmap] at hm
  refine ⟨hc, ef, eq, hm, ?_, ?_⟩
  · intro b
    obtain ⟨v, hv⟩ := cuspLatticeProjection_surjective (eq b)
    refine ⟨ef.symm v, eq.injective ?_⟩
    rw [hm, ef.apply_symm_apply, hv]
  · intro a
    rw [← eq.map_eq_zero_iff, hm, cuspLatticeProjection_eq_zero_iff_monodromy_image]

end Wikipedia.HopfProblem.CuspCentralHomology
