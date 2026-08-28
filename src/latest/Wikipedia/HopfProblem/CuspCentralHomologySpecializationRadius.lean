import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusFibre
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusMaps
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusEquivariance

/-!
# The independently prescribed collapse commutes with radius comparison

Both the nonzero-fibre and central-fibre radius homeomorphisms preserve
the original toric representative.  The prescribed collapse is the same
straightened polar formula on those representatives.  Its proved deck
equivariance on a smaller admissible tube therefore gives the exact
commuting square for the literal fibres at any larger ambient radius.

The larger radius is only required to carry the original holomorphic
period data.  Small-drift estimates are used on the smaller radius, not
assumed at the larger radius, and no chosen retraction enters the map.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hδ1 : δ < 1) (hRC : SmallDrift C δ) (hRF : SmallDrift (frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)

include hδ1 hRC hRF in
/-- The original independently prescribed maps commute exactly with
the actual representative-preserving radius homeomorphisms. -/
theorem prescribedActualFibreCollapse_radius (q : ActualQuotientFibre C δ t) :
    prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη
      (fibreRadiusHomeomorph C r δ t hδr hC (htη.trans_lt hηδ) q) =
        centralRadiusHomeomorph C r δ hδr hC hδ
          (prescribedActualFibreCollapse C δ hδ hηδ t ht htη q) := by
  obtain ⟨x, rfl⟩ := fibreProjection_surjective C δ t (htη.trans_lt hηδ) q
  rw [fibreRadiusHomeomorph_fibreProjection,
    prescribedActualFibreCollapse_fibreProjection C hδ1 hRC hRF hηδ r hr
      (hηδ.trans_le hδr) t ht htη,
    prescribedActualFibreCollapse_fibreProjection C hδ1 hRC hRF hηδ δ hδ hηδ t ht htη,
    centralRadiusHomeomorph_centralProject]

include hδ1 hRC hRF in
/-- The same naturality square as an equality of the literal functions. -/
theorem prescribedActualFibreCollapse_radius_comp :
    prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη ∘
        fibreRadiusHomeomorph C r δ t hδr hC (htη.trans_lt hηδ) =
      centralRadiusHomeomorph C r δ hδr hC hδ ∘
        prescribedActualFibreCollapse C δ hδ hηδ t ht htη :=
  funext (prescribedActualFibreCollapse_radius C r δ hr hδ hδr hC hδ1 hRC hRF
    η hηδ t ht htη)

include hδ1 hRC hRF in
/-- Inverse radius transport retains the same independently prescribed
collapse, including its chosen closed-tube parameter. -/
theorem prescribedActualFibreCollapse_radius_symm (q : ActualQuotientFibre C r t) :
    prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη q =
      centralRadiusHomeomorph C r δ hδr hC hδ
        (prescribedActualFibreCollapse C δ hδ hηδ t ht htη
          ((fibreRadiusHomeomorph C r δ t hδr hC (htη.trans_lt hηδ)).symm q)) := by
  simpa only [Homeomorph.apply_symm_apply] using
    prescribedActualFibreCollapse_radius C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t ht htη
      ((fibreRadiusHomeomorph C r δ t hδr hC (htη.trans_lt hηδ)).symm q)

/-- The literal toric fibre inclusion into a containing punctured closed
tube is continuous for the original subspace topologies. -/
theorem toricFibrePunctured_continuous : Continuous (toricFibrePunctured η t ht htη) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_subtype_val

end Wikipedia.HopfProblem.CuspCentralHomology
