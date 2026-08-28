import Wikipedia.HopfProblem.DegreeCollapseCubicFieldCancellation
import Mathlib.Topology.Compactness.Compact

/-!
# A polynomial Lyapunov function for the modified field on each compact region

The transverse equations give a negative sum of squares after weighting
the signed quadratic form. Increasing its coefficient makes the derivative
negative away from the axis; the modified longitudinal field is already
negative on the axis. A directed open cover makes one coefficient work on
the whole compact region. This avoids a separate exponential-trajectory argument.
-/

noncomputable section

open Set Filter Function
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ} (σ : Fin m → ℝ)

def transverseEnergy (p : Model m) : ℝ := ∑ i, (σ i * p.2 i) ^ 2

theorem transverseEnergy_nonneg (p : Model m) : 0 ≤ transverseEnergy σ p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem transverseEnergy_zero_iff (hσ : ∀ i, σ i ≠ 0) (p : Model m) :
    transverseEnergy σ p = 0 ↔ p.2 = 0 := by
  constructor
  · intro h
    funext i
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (σ i * p.2 i))).mp h i (Finset.mem_univ i)
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hh)).resolve_left (hσ i)
  · intro h
    simp [transverseEnergy, h]

def fieldLyapunov (k : ℝ) (p : Model m) : ℝ := p.1 + k * ∑ i, σ i * p.2 i ^ 2

theorem contDiff_fieldLyapunov (k : ℝ) : ContDiff ℝ ∞ (fieldLyapunov σ k) := by
  unfold fieldLyapunov
  fun_prop

theorem hasFDerivAt_fieldLyapunov (k : ℝ) (p : Model m) :
    HasFDerivAt (fieldLyapunov σ k)
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) + k •
        ∑ i, (2 * σ i * p.2 i) • ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) := ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! hx.add (hq.const_mul k) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [mul_assoc, mul_comm]

theorem fieldLyapunov_speed (k a : ℝ) (φ : Model m → ℝ) (p : Model m) :
    fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) =
      (cancelledDescent σ a φ p).1 - 2 * k * transverseEnergy σ p := by
  rw [(hasFDerivAt_fieldLyapunov σ k p).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (cancelledDescent σ a φ p).1 +
    k * (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = _
  have hsum : (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) =
      -2 * transverseEnergy σ p := by
    rw [transverseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change 2 * σ i * p.2 i * (-σ i * p.2 i) = _
    ring
  rw [hsum]
  ring

/-- One polynomial coefficient makes the actual field strictly decrease height throughout `C`. -/
theorem exists_compact_fieldLyapunov (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Icc (-a) a, φ (s, 0) = 1)
    {C : Set (Model m)} (hC : IsCompact C) :
    ∃ k : ℝ, 0 ≤ k ∧ ContDiff ℝ ∞ (fieldLyapunov σ k) ∧
      ∀ p ∈ C, fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) < 0 := by
  let O : ℕ → Set (Model m) := fun n =>
    {p | (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0}
  have henergy : Continuous (transverseEnergy σ) := by
    unfold transverseEnergy
    fun_prop
  have hO (n : ℕ) : IsOpen (O n) :=
    isOpen_lt ((contDiff_cancelledDescent σ a hφ).continuous.fst.sub
      (continuous_const.mul henergy)) continuous_const
  have hcover : C ⊆ ⋃ n, O n := by
    intro p hp
    by_cases hz : p.2 = 0
    · apply mem_iUnion.mpr
      refine ⟨0, ?_⟩
      have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
      have hh := cancelledDescent_axis_negative σ ha hφnonneg hone p.1
      have hneg : (cancelledDescent σ a φ p).1 < 0 :=
        (congrArg (fun q : Model m => (cancelledDescent σ a φ q).1) he).trans_lt hh
      simpa only [O, mem_ofPred_eq, Nat.cast_zero, mul_zero, zero_mul, sub_zero] using hneg
    · have hpos : 0 < transverseEnergy σ p :=
        lt_of_le_of_ne (transverseEnergy_nonneg σ p)
          (Ne.symm (fun he => hz ((transverseEnergy_zero_iff σ hσ p).mp he)))
      obtain ⟨n, hn⟩ := exists_nat_gt
        ((cancelledDescent σ a φ p).1 / (2 * transverseEnergy σ p))
      have hh := (div_lt_iff₀ (mul_pos (by norm_num) hpos)).mp hn
      apply mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0
      nlinarith
  have hmono : Monotone O := by
    intro i j hij p hp
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have he := transverseEnergy_nonneg σ p
    change (cancelledDescent σ a φ p).1 - 2 * (i : ℝ) * transverseEnergy σ p < 0 at hp
    change (cancelledDescent σ a φ p).1 - 2 * (j : ℝ) * transverseEnergy σ p < 0
    nlinarith
  obtain ⟨n, hn⟩ := hC.elim_directed_cover O hO hcover
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)
  refine ⟨n, by positivity, contDiff_fieldLyapunov σ n, ?_⟩
  intro p hp
  rw [fieldLyapunov_speed]
  exact hn hp

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
