import Wikipedia.HopfProblem.DegreeCollapsePhaseClockSupport

/-!
# A complete compact phase-flow construction

The original scalar phase germ constructs its bounded extension, clock,
autonomous positive vertical field, compact perturbation support, and
complete flow. The left tail is unchanged, the right tail has precisely
the prescribed phase, and the entire reference-axis motion is unchanged.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

open FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual diffeomorphism defining the compact phase flow, including
its unchanged transverse coordinate and exact exterior phase formulas. -/
structure PhaseFlowCoordinates (g : E → ℝ)
    (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)) where
  chart : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞
  field_eq : W = suspensionField chart
  flow_eq : F = suspensionFlow chart
  base : ∀ p, (chart p).1 = p.1
  lower : ∀ p, p.2 ≤ 1 / 3 → chart p = p
  upper : ∀ p, 2 / 3 ≤ p.2 → chart p = (p.1, p.2 + g p.1)
  axis : ∀ t : ℝ, chart (0, t) = (0, t)

/-- Realize the actual phase germ by a complete flow with a compact positive speed change. -/
theorem exists_compact_phase_flow {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) :
    ∃ (K : Set E) (C : Set (E × ℝ)) (g : E → ℝ) (W : E × ℝ → E × ℝ) (F : Flow ℝ (E × ℝ)),
      IsCompact K ∧ K ⊆ U ∧ IsCompact C ∧ C ⊆ K ×ˢ Ioo (0 : ℝ) 1 ∧
      ContDiff ℝ ∞ g ∧ tsupport g ⊆ K ∧ g =ᶠ[𝓝 0] v ∧ g 0 = 0 ∧
      ContDiff ℝ ∞ W ∧ (∀ p, (W p).1 = 0) ∧ (∀ p, 1 / 2 < (W p).2) ∧
      (∀ p ∉ C, W p = (0, 1)) ∧
      (∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t) ∧
      (∀ p t, (F t p).1 = p.1) ∧
      (∀ z t, t ≤ 1 / 3 → F t (z, 0) = (z, t)) ∧
      (∀ z t, 2 / 3 ≤ t → F t (z, 0) = (z, t + g z)) ∧
      (∀ s t : ℝ, F t (0, s) = (0, s + t)) ∧
      Nonempty (PhaseFlowCoordinates g W F) := by
  obtain ⟨K, g, τ, D, hK, hKU, hg, hsupp, hgerm, hg0, hsmall, hτ, hrange,
    hD, haxis, hleft, hright, hpos⟩ := exists_supported_phase_clock hv hv0 hU h0U
  let Q := phaseConjugatingDiffeomorph D
  let W := suspensionField Q
  let F := suspensionFlow Q
  have hbase (p : ℝ × E) : (D p).2 = p.2 := by rw [hD]
  obtain ⟨C, hC, hCsub, hoff⟩ := exists_compact_phase_field_support D hK hsupp hsmall
    hrange hD hleft hright
  have hinitial (z : E) : Q (z, 0) = (z, 0) := by
    change ((D (0, z)).2, (D (0, z)).1) = (z, 0)
    rw [hleft (0, z) (by norm_num)]
  have hinverse (z : E) : Q.symm (z, 0) = (z, 0) := by
    have hh := Q.symm_apply_apply (z, 0)
    rw [hinitial] at hh
    exact hh
  have hfromzero (z : E) (t : ℝ) : F t (z, 0) = ((D (t, z)).2, (D (t, z)).1) := by
    change Q ((Q.symm (z, 0)).1, (Q.symm (z, 0)).2 + t) = _
    rw [hinverse, zero_add]
    rfl
  have hcoords : PhaseFlowCoordinates g W F := by
    refine ⟨Q, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro p
      change (D (p.2, p.1)).2 = p.1
      rw [hD]
    · intro p hp
      change ((D (p.2, p.1)).2, (D (p.2, p.1)).1) = p
      rw [hleft (p.2, p.1) hp]
    · intro p hp
      change ((D (p.2, p.1)).2, (D (p.2, p.1)).1) = (p.1, p.2 + g p.1)
      rw [hright (p.2, p.1) hp]
    · intro t
      change ((D (t, 0)).2, (D (t, 0)).1) = (0, t)
      rw [haxis]
  refine ⟨K, C, g, W, F, hK, hKU, hC, hCsub, hg, hsupp, hgerm, hg0,
    contDiff_suspensionField Q, phaseClockField_base_zero D hbase,
    phaseClockField_time_positive D hpos, hoff, hasDerivAt_suspensionFlow Q,
    phaseClockFlow_base D hbase, ?_, ?_, ?_, ⟨hcoords⟩⟩
  · intro z t ht
    rw [hfromzero, hleft (t, z) ht]
  · intro z t ht
    rw [hfromzero, hright (t, z) ht]
  · intro s t
    have hQaxis (r : ℝ) : Q (0, r) = (0, r) := by
      change ((D (r, 0)).2, (D (r, 0)).1) = (0, r)
      rw [haxis]
    have hiaxis : Q.symm (0, s) = (0, s) := by
      have hh := Q.symm_apply_apply (0, s)
      rw [hQaxis] at hh
      exact hh
    change Q ((Q.symm (0, s)).1, (Q.symm (0, s)).2 + t) = _
    rw [hiaxis, hQaxis]

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
