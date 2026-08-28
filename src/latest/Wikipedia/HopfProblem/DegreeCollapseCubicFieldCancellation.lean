import Wikipedia.HopfProblem.DegreeCollapseCubicDescent
import Wikipedia.SmoothSixDPoincare.CompactSmoothCutoff

/-!
# Removing the model field zeros in an arbitrarily thin axis neighborhood

Unlike a supported replacement of the scalar function, this modification
only changes the longitudinal vector component. There is no derivative of
the cutoff in the field formula. Any open neighborhood of the full closed
axis contains a compact supported modification with no zeros. Constructing
a global Lyapunov function for the modified field is a separate obligation.
-/

noncomputable section

open Set Filter Function
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ} (σ : Fin m → ℝ)

def cancelledDescent (a : ℝ) (φ : Model m → ℝ) (p : Model m) : Model m :=
  (a ^ 2 - p.1 ^ 2 - 2 * a ^ 2 * φ p, fun i => -σ i * p.2 i)

theorem contDiff_cancelledDescent (a : ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (cancelledDescent σ a φ) := by
  unfold cancelledDescent
  fun_prop

theorem cancelledDescent_axis_negative {a : ℝ} (ha : 0 < a) {φ : Model m → ℝ}
    (hφ : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Icc (-a) a, φ (s, 0) = 1) (s : ℝ) :
    (cancelledDescent σ a φ (s, 0)).1 < 0 := by
  change a ^ 2 - s ^ 2 - 2 * a ^ 2 * φ (s, 0) < 0
  by_cases hs : s ∈ Icc (-a) a
  · rw [hone s hs]
    nlinarith [sq_pos_of_pos ha, sq_nonneg s]
  · have hsq : a ^ 2 < s ^ 2 := by
      by_cases hl : -a ≤ s
      · have hr : a < s := lt_of_not_ge (fun h => hs ⟨hl, h⟩)
        nlinarith
      · have hh : s < -a := lt_of_not_ge hl
        nlinarith
    have hnonneg : 0 ≤ 2 * a ^ 2 * φ (s, 0) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) (hφ (s, 0))
    linarith

/-- The unchanged transverse linear field forces a possible zero onto the axis. -/
theorem cancelledDescent_ne_zero (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    {φ : Model m → ℝ} (hφ : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Icc (-a) a, φ (s, 0) = 1) (p : Model m) :
    cancelledDescent σ a φ p ≠ 0 := by
  intro hp
  have hz : p.2 = 0 := by
    funext i
    have hi := congrArg (fun q : Model m => q.2 i) hp
    change -σ i * p.2 i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr (hσ i))
  have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
  have hx := congrArg Prod.fst hp
  rw [he] at hx
  exact (cancelledDescent_axis_negative σ ha hφ hone p.1).ne hx

theorem cancelledDescent_germ_off_support (a : ℝ) {φ : Model m → ℝ} {p : Model m}
    (hp : p ∉ tsupport φ) :
    cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
  apply Prod.ext
  · simp only [cancelledDescent, cubicDescent, hq, Pi.zero_apply, mul_zero, sub_zero]
    ring
  · rfl

/-- Every actual open neighborhood of the closed axis supports a zero-free field replacement. -/
theorem exists_cubic_field_cancellation (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    {U : Set (Model m)} (hU : IsOpen U)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ U) :
    ∃ φ : Model m → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      (∀ p, φ p ∈ Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (-a) a, φ (s, 0) = 1) ∧
      ContDiff ℝ ∞ (cancelledDescent σ a φ) ∧
      (∀ p, cancelledDescent σ a φ p ≠ 0) ∧
      ∀ p ∉ tsupport φ,
        cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  obtain ⟨φ, hφ, hc, hsupp, hone, hrange⟩ := exists_compact_smooth_cutoff
    (isCompact_Icc.prod isCompact_singleton) hU haxis
  have hone' (s : ℝ) (hs : s ∈ Icc (-a) a) : φ (s, (0 : Fin m → ℝ)) = 1 := by
    have hn : ∀ᶠ p in 𝓝 (s, (0 : Fin m → ℝ)), φ p = 1 :=
      (nhds_le_nhdsSet (show (s, (0 : Fin m → ℝ)) ∈ Icc (-a) a ×ˢ {0} from ⟨hs, rfl⟩)) hone
    exact hn.self_of_nhds
  exact ⟨φ, hφ, hc, hsupp, hrange, hone', contDiff_cancelledDescent σ a hφ,
    cancelledDescent_ne_zero σ hσ ha (fun p => (hrange p).1) hone',
    fun p hp => cancelledDescent_germ_off_support σ a hp⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
