import Wikipedia.HopfProblem.DegreeCollapseCompactFieldLyapunov
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# Uniform finite residence for the modified cubic field

A strict Lyapunov function is only required on the compact region itself.
The curve equation is only required while the curve is in that region and
in the constructed finite time interval. This applies to actual local chart
coordinates without postulating a globally defined model trajectory.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Local strict Lyapunov decrease gives a uniform exit time on a compact region. -/
theorem exists_compact_lyapunov_residence {L : D → ℝ} {W : D → D}
    (hL : ContDiff ℝ ∞ L) (hW : Continuous W) {C : Set D} (hC : IsCompact C)
    (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → D,
      (∀ t ∈ Icc (0 : ℝ) T, γ t ∈ C → HasDerivAt γ (W (γ t)) t) →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ =>
      ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed : Continuous (fun x => fderiv ℝ L x (W x)) :=
    (hL.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk hW)
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -fderiv ℝ L v (W v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : D) (hx : x ∈ C) : fderiv ℝ L x (W x) ≤ -δ := by
    have hh : fderiv ℝ L x (W x) ≤ fderiv ℝ L v (W v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hL.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hL.continuous.continuousOn
  let T := (L q - L p + 1) / δ
  have hpq : L p ≤ L q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = L q - L p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun u => L (γ u)) (fderiv ℝ L (γ t) (W (γ t))) t :=
    (hL.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t
      (hγ t ht (hstay t ht))
  have hcont : ContinuousOn (fun t => L (γ t)) (Icc (0 : ℝ) T) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t => L (γ t)) (Icc (0 : ℝ) T) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hcont
    (hdiff.mono interior_subset)
    (fun t ht => by
      rw [(hd t (interior_subset ht)).deriv]
      exact hbound (γ t) (hstay t (interior_subset ht))) 0 h0 T hlast hT.le
  simp only [sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : L p ≤ L (γ T) := hmin (hstay T hlast)
  have hhi : L (γ 0) ≤ L q := hmax (hstay 0 h0)
  linarith

/-- The modified cubic field cannot stay in any compact coordinate region indefinitely. -/
theorem exists_cancelledDescent_residence_bound {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Icc (-a) a, φ (s, 0) = 1) {C : Set (Model m)} (hC : IsCompact C) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → Model m,
      (∀ t ∈ Icc (0 : ℝ) T, γ t ∈ C → HasDerivAt γ (cancelledDescent σ a φ (γ t)) t) →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ C := by
  obtain ⟨k, -, hL, hneg⟩ := exists_compact_fieldLyapunov σ hσ ha hφ hφnonneg hone hC
  exact exists_compact_lyapunov_residence hL (contDiff_cancelledDescent σ a hφ).continuous hC hneg

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
