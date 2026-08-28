import Wikipedia.HopfProblem.DegreeCollapseSuspensionVectorField
import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A compact field perturbation realizing a supported coordinate isotopy

Retiming makes the isotopy stationary near both endpoint slices. Its
suspension is an actual complete smooth field with vertical speed one,
compact perturbation support inside the open slab, and the prescribed
endpoint transition. Every point of the isotopy's fixed locus follows
the unchanged vertical trajectory for all times.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Retain the actual time-preserving diffeomorphism used to construct
the suspension, including its domain invariance and two exterior formulas. -/
structure SuspensionCoordinates
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E)
    (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)) where
  chart : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞
  field_eq : W = suspensionField chart
  flow_eq : F = suspensionFlow chart
  height : ∀ p, (chart p).2 = p.2
  base_iff : ∀ U : Set E, K ⊆ U → ∀ p, (chart p).1 ∈ U ↔ p.1 ∈ U
  lower : ∀ p, p.2 ≤ 0 → chart p = p
  upper : ∀ p, 1 ≤ p.2 → chart p = (D p.1, p.2)

/-- Realize the original supported relative isotopy by a complete smooth
autonomous field, with its exact compact support and transition retained. -/
theorem exists_compact_isotopy_suspension
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {K S : Set E} (hK : IsCompact K)
    (I : SupportedRelativeIsotopy D K S) :
    ∃ (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)), ContDiff ℝ ∞ W ∧
      (∀ p, (W p).2 = 1) ∧ HasCompactSupport (fun p => W p - (0, 1)) ∧
      tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3) ∧
      (∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t) ∧
      (∀ x, F 1 (x, 0) = (D x, 1)) ∧
      (∀ t p, (F t p).2 = p.2 + t) ∧
      (∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
      (∀ x ∈ S, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
      Nonempty (SuspensionCoordinates D K W F) := by
  let τ : ℝ → ℝ := fun s => Real.smoothTransition (3 * s - 1)
  have hτ : ContDiff ℝ ∞ τ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hτlower (s : ℝ) (hs : s ≤ 1 / 3) : τ s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hτupper (s : ℝ) (hs : 2 / 3 ≤ s) : τ s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  let A : ℝ × E → E := fun p => I.family (τ p.1, p.2)
  have hInorm : ContDiff ℝ ∞ I.family :=
    (I.smooth.comp (PartialChart.vectorProduct ℝ E).contMDiff).contDiff
  have hA : ContDiff ℝ ∞ A := hInorm.comp ((hτ.comp contDiff_fst).prodMk contDiff_snd)
  have hslice (s : ℝ) : ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ∀ x, d x = A (s, x) := I.slices (τ s)
  have hA0 (x : E) : A (0, x) = x := by
    change I.family (τ 0, x) = x
    rw [hτlower 0 (by norm_num)]
    exact I.zero x
  have hA1 (x : E) : A (1, x) = D x := by
    change I.family (τ 1, x) = D x
    rw [hτupper 1 (by norm_num)]
    exact I.one x
  have hfix (s : ℝ) (x : E) (hx : x ∉ K) : A (s, x) = x := I.fixedOutside (τ s) x hx
  have hstationary (s : ℝ) (hs : s ∉ Icc (1 / 3 : ℝ) (2 / 3)) :
      ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x) := by
    by_cases hlo : s < 1 / 3
    · filter_upwards [eventually_lt_nhds hlo] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτlower r hr.le, hτlower s hlo.le]
    · have hhi : 2 / 3 < s := lt_of_not_ge (fun h => hs ⟨le_of_not_gt hlo, h⟩)
      filter_upwards [eventually_gt_nhds hhi] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτupper r hr.le, hτupper s hhi.le]
  obtain ⟨Ψ, hΨ⟩ := exists_isotopy_suspension_diffeomorph hA hslice
  let W := suspensionField Ψ
  let F := suspensionFlow Ψ
  have hvertical (p : E × ℝ) (hp : p ∉ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)) : W p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · exact suspensionField_eq_vertical_of_stationary Ψ hΨ p
        (hstationary p.2 (fun h => hp ⟨hx, h⟩))
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  have hsupp : tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3) := by
    apply closure_minimal _ (hK.isClosed.prod isClosed_Icc)
    intro p hp
    by_contra hout
    apply hp
    change W p - (0, 1) = 0
    rw [hvertical p hout, sub_self]
  have hcoords : SuspensionCoordinates D K W F := by
    refine ⟨Ψ, rfl, rfl, fun p => by rw [hΨ], ?_, ?_, ?_⟩
    · intro U hKU p
      have hfixU (z : E × ℝ) (hz : z ∉ U ×ˢ univ) : Ψ z = z := by
        have hn : z.1 ∉ K := fun h => hz ⟨hKU h, mem_univ _⟩
        rw [hΨ, hfix z.2 z.1 hn]
      have hmaps := mapsTo_of_fixed_outside Ψ.toEquiv hfixU
      have hmapsInv := mapsTo_of_fixed_outside Ψ.symm.toEquiv
        (inverse_fixed_outside Ψ.toEquiv hfixU)
      constructor
      · intro hp
        have hh := hmapsInv ⟨hp, mem_univ (Ψ p).2⟩
        have hh' : (Ψ.symm (Ψ p)).1 ∈ U := hh.1
        simpa only [Ψ.symm_apply_apply] using hh'
      · intro hp
        exact (hmaps ⟨hp, mem_univ p.2⟩).1
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = p
      rw [hτlower p.2 (by linarith), I.zero]
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = (D p.1, p.2)
      rw [hτupper p.2 (by linarith), I.one]
  refine ⟨W, F, contDiff_suspensionField Ψ,
    suspensionField_height Ψ (fun p => by rw [hΨ]) ,
    hasCompactSupport_suspensionField_sub_vertical Ψ hΨ hK hfix hstationary,
    hsupp, hasDerivAt_suspensionFlow Ψ, ?_,
    suspensionFlow_height Ψ (fun p => by rw [hΨ]), ?_, ?_, ⟨hcoords⟩⟩
  · intro x
    exact (suspensionFlow_endpoint Ψ hΨ hA0 x).trans (congrArg (fun y : E => (y, (1 : ℝ))) (hA1 x))
  · intro x hx s t
    exact suspensionFlow_vertical_off_support Ψ hΨ hfix (p := (x, s)) hx t
  · intro x hx s t
    have hΨfix (r : ℝ) : Ψ (x, r) = (x, r) := by
      rw [hΨ]
      change (I.family (τ r, x), r) = (x, r)
      rw [I.fixedOn (τ r) x hx]
    change suspensionFlow Ψ t (x, s) = (x, s + t)
    rw [← hΨfix s, suspensionFlow_chart, hΨfix]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
