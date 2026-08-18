/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.Flow

/-!
# The limiting real flow for circle squaring

This file completes the analytic part of the dyadic flow construction begun in
`ErdosProblems.Erdos1124.Flow`.  If the cube averages of a real-valued demand
decay uniformly like `C * n ^ (-1 - δ)` at dyadic side lengths, then the flow
at scale `2 ^ q` is bounded by a geometric sequence with ratio `2 ^ (-δ)`.
Consequently the scale flows are absolutely summable, their partial sums are
uniformly bounded, and their limit has divergence equal to the negative of the
demand.

In the circle-squaring application the demand is `1_A - 1_B`, so the last
identity reads `div φ = 1_B - 1_A`, with the sign convention for divergence
from `Flow.lean` (incoming minus outgoing).
-/

open scoped BigOperators
open Filter

namespace Erdos1124.Flow

noncomputable section

/-- A negative real power at a dyadic natural scale is a geometric sequence. -/
lemma dyadic_rpow_neg_eq (q : ℕ) (δ : ℝ) :
    (((2 ^ q : ℕ) : ℝ) ^ (-δ)) = ((2 : ℝ) ^ (-δ)) ^ q := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  calc
    ((2 : ℝ) ^ q) ^ (-δ) = (2 : ℝ) ^ ((q : ℝ) * (-δ)) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = (2 : ℝ) ^ ((-δ) * (q : ℝ)) := by ring_nf
    _ = ((2 : ℝ) ^ (-δ)) ^ (q : ℝ) :=
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
    _ = ((2 : ℝ) ^ (-δ)) ^ q := Real.rpow_natCast _ _

/-- Multiplying the discrepancy bound by the path length removes one power. -/
lemma mul_rpow_neg_one_sub (x δ : ℝ) (hx : 0 < x) :
    x * x ^ (-1 - δ) = x ^ (-δ) := by
  rw [show -1 - δ = -1 + -δ by ring, Real.rpow_add hx]
  rw [Real.rpow_neg_one]
  field_simp

lemma dyadic_decay_rewrite (q : ℕ) (δ : ℝ) :
    (((2 ^ q : ℕ) : ℝ) * (((2 ^ q : ℕ) : ℝ) ^ (-1 - δ))) =
      ((2 : ℝ) ^ (-δ)) ^ q := by
  rw [mul_rpow_neg_one_sub _ _ (by positivity)]
  exact dyadic_rpow_neg_eq q δ

lemma abs_dyadicFactor_le_one (d : ℕ) :
    |dyadicFactor (d := d) (𝕜 := ℝ)| ≤ 1 := by
  unfold dyadicFactor
  have hp : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  rw [abs_of_pos (inv_pos.mpr hp)]
  exact (inv_le_one₀ hp).2 (one_le_pow₀ (by norm_num))

variable {d : ℕ} {X : Type*} [AddAction (Lattice d) X]

/-- A uniform `n ^ (-1 - δ)` cube-average estimate gives an `n ^ (-δ)`
bound for the length-`n` scale flow. -/
lemma abs_scaleFlow_le_of_average_decay (f : X → ℝ) (n : ℕ) (g : BitDirection d)
    (x : X) (C δ : ℝ) (hn : 0 < n)
    (hdecay : ∀ y : X,
      |cubeAverage (d := d) f n y| ≤
        C * ((n : ℝ) ^ (-1 - δ))) :
    |scaleFlow (d := d) f n g x| ≤ C * ((n : ℝ) ^ (-δ)) := by
  rw [scaleFlow, pathFlow]
  have hterm : ∀ m ∈ Finset.range n,
      |cubeAverage (d := d) f n (-(m • bitVector g) +ᵥ x)| ≤
        C * ((n : ℝ) ^ (-1 - δ)) := by
    intro m hm
    exact hdecay _
  calc
    |dyadicFactor (d := d) (𝕜 := ℝ) *
        ∑ m ∈ Finset.range n,
          cubeAverage (d := d) f n (-(m • bitVector g) +ᵥ x)| =
        |dyadicFactor (d := d) (𝕜 := ℝ)| *
          |∑ m ∈ Finset.range n,
            cubeAverage (d := d) f n (-(m • bitVector g) +ᵥ x)| := abs_mul _ _
    _ ≤ 1 * |∑ m ∈ Finset.range n,
            cubeAverage (d := d) f n (-(m • bitVector g) +ᵥ x)| := by
      exact mul_le_mul_of_nonneg_right (abs_dyadicFactor_le_one d) (abs_nonneg _)
    _ ≤ ∑ m ∈ Finset.range n,
            |cubeAverage (d := d) f n (-(m • bitVector g) +ᵥ x)| := by
      simpa only [Real.norm_eq_abs, one_mul] using norm_sum_le
        (s := Finset.range n)
        (f := fun m ↦ cubeAverage (d := d) f n (-(m • bitVector g) +ᵥ x))
    _ ≤ ∑ m ∈ Finset.range n, C * ((n : ℝ) ^ (-1 - δ)) := by
      exact Finset.sum_le_sum fun m hm ↦ hterm m hm
    _ = C * ((n : ℝ) * ((n : ℝ) ^ (-1 - δ))) := by
      simp
      ring
    _ = C * ((n : ℝ) ^ (-δ)) := by
      rw [mul_rpow_neg_one_sub _ _ (by exact_mod_cast hn)]

/-- Uniform positive-power decay of the dyadic cube averages. -/
def UniformDyadicDecay (f : X → ℝ) (C δ : ℝ) : Prop :=
  0 ≤ C ∧ 0 < δ ∧
    ∀ (q : ℕ) (x : X),
      |cubeAverage (d := d) f (2 ^ q) x| ≤
        C * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))

/-- The individual dyadic scale flows obey a bound uniform in both the vertex
and the bit direction. -/
lemma abs_scaleFlow_dyadic_le (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ)
    (q : ℕ) (g : BitDirection d) (x : X) :
    |scaleFlow (d := d) f (2 ^ q) g x| ≤
      C * (((2 : ℝ) ^ (-δ)) ^ q) := by
  have h := abs_scaleFlow_le_of_average_decay (d := d) f (2 ^ q) g x C δ
    (by positivity) (hdecay.2.2 q)
  rw [dyadic_rpow_neg_eq] at h
  exact h

lemma dyadicRatio_nonneg {δ : ℝ} : 0 ≤ (2 : ℝ) ^ (-δ) :=
  Real.rpow_nonneg (by norm_num) _

lemma dyadicRatio_lt_one {δ : ℝ} (hδ : 0 < δ) : (2 : ℝ) ^ (-δ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The scale-flow series is absolutely convergent at every directed edge. -/
theorem summable_scaleFlow_dyadic (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ)
    (g : BitDirection d) (x : X) :
    Summable (fun q : ℕ ↦ scaleFlow (d := d) f (2 ^ q) g x) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one dyadicRatio_nonneg
      (dyadicRatio_lt_one hdecay.2.1)).mul_left C)
  intro q
  simpa only [Real.norm_eq_abs] using abs_scaleFlow_dyadic_le
    (d := d) f C δ hdecay q g x

/-- The absolutely convergent flow obtained by adding all dyadic scales. -/
def dyadicFlow (f : X → ℝ) : DirectionalFlow (d := d) (X := X) (𝕜 := ℝ) :=
  fun g x ↦ ∑' q : ℕ, scaleFlow (d := d) f (2 ^ q) g x

lemma summable_norm_scaleFlow_dyadic (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ)
    (g : BitDirection d) (x : X) :
    Summable (fun q : ℕ ↦ ‖scaleFlow (d := d) f (2 ^ q) g x‖) := by
  apply Summable.of_nonneg_of_le (fun q ↦ norm_nonneg _)
    (fun q ↦ ?_)
    ((summable_geometric_of_lt_one dyadicRatio_nonneg
      (dyadicRatio_lt_one hdecay.2.1)).mul_left C)
  simpa only [Real.norm_eq_abs] using
    abs_scaleFlow_dyadic_le (d := d) f C δ hdecay q g x

/-- The closed-form geometric bound for both partial and limiting flows. -/
def geometricFlowBound (C δ : ℝ) : ℝ :=
  C * (1 - (2 : ℝ) ^ (-δ))⁻¹

/-- A bound independent of the vertex and direction for the full real flow. -/
theorem abs_dyadicFlow_le_geometricFlowBound (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ)
    (g : BitDirection d) (x : X) :
    |dyadicFlow (d := d) f g x| ≤ geometricFlowBound C δ := by
  let r : ℝ := (2 : ℝ) ^ (-δ)
  have hr0 : 0 ≤ r := dyadicRatio_nonneg
  have hr1 : r < 1 := dyadicRatio_lt_one hdecay.2.1
  have hgeom : Summable (fun q : ℕ ↦ C * r ^ q) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hnorm := summable_norm_scaleFlow_dyadic (d := d) f C δ hdecay g x
  calc
    |dyadicFlow (d := d) f g x| =
        ‖∑' q : ℕ, scaleFlow (d := d) f (2 ^ q) g x‖ := by
          simp only [dyadicFlow, Real.norm_eq_abs]
    _ ≤ ∑' q : ℕ, ‖scaleFlow (d := d) f (2 ^ q) g x‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, C * r ^ q := by
      apply Summable.tsum_le_tsum _ hnorm hgeom
      intro q
      simpa only [r, Real.norm_eq_abs] using
        abs_scaleFlow_dyadic_le (d := d) f C δ hdecay q g x
    _ = geometricFlowBound C δ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      rfl

/-- The same geometric bound holds uniformly for every finite partial flow. -/
theorem abs_dyadicPartialFlow_le_geometricFlowBound (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ)
    (m : ℕ) (g : BitDirection d) (x : X) :
    |dyadicPartialFlow (d := d) f m g x| ≤ geometricFlowBound C δ := by
  let r : ℝ := (2 : ℝ) ^ (-δ)
  have hr0 : 0 ≤ r := dyadicRatio_nonneg
  have hr1 : r < 1 := dyadicRatio_lt_one hdecay.2.1
  have hgeom : Summable (fun q : ℕ ↦ C * r ^ q) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  rw [dyadicPartialFlow]
  calc
    |∑ q ∈ Finset.range m, scaleFlow (d := d) f (2 ^ q) g x| ≤
        ∑ q ∈ Finset.range m, |scaleFlow (d := d) f (2 ^ q) g x| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le
        (s := Finset.range m)
        (f := fun q ↦ scaleFlow (d := d) f (2 ^ q) g x)
    _ ≤ ∑ q ∈ Finset.range m, C * r ^ q := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [r] using abs_scaleFlow_dyadic_le
        (d := d) f C δ hdecay q g x
    _ ≤ ∑' q : ℕ, C * r ^ q := by
      exact hgeom.sum_le_tsum (Finset.range m)
        (fun q hq ↦ mul_nonneg hdecay.1 (pow_nonneg hr0 q))
    _ = geometricFlowBound C δ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      rfl

/-- The finite dyadic flows converge pointwise to `dyadicFlow`. -/
theorem tendsto_dyadicPartialFlow (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ)
    (g : BitDirection d) (x : X) :
    Tendsto (fun m ↦ dyadicPartialFlow (d := d) f m g x) atTop
      (nhds (dyadicFlow (d := d) f g x)) := by
  simpa only [dyadicPartialFlow, dyadicFlow] using
    (summable_scaleFlow_dyadic (d := d) f C δ hdecay g x).hasSum.tendsto_sum_nat

lemma dyadic_average_decay_rewrite (q : ℕ) (δ : ℝ) :
    ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) =
      ((2 : ℝ) ^ (-1 - δ)) ^ q := by
  rw [show -1 - δ = -(1 + δ) by ring]
  exact dyadic_rpow_neg_eq q (1 + δ)

/-- Uniform discrepancy decay forces the residual dyadic cube average to
vanish pointwise. -/
theorem tendsto_cubeAverage_dyadic_zero (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ) (x : X) :
    Tendsto (fun q ↦ cubeAverage (d := d) f (2 ^ q) x) atTop (nhds 0) := by
  let r : ℝ := (2 : ℝ) ^ (-1 - δ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith [hdecay.2.1]
  have hgeom : Tendsto (fun q : ℕ ↦ C * r ^ q) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1))
  have habs : Tendsto
      (fun q ↦ |cubeAverage (d := d) f (2 ^ q) x|) atTop (nhds 0) := by
    apply squeeze_zero (fun q ↦ abs_nonneg _)
      (fun q ↦ ?_) hgeom
    simpa only [r, dyadic_average_decay_rewrite] using hdecay.2.2 q x
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using habs

/-- Divergence is a finite coordinate sum, so it commutes with the pointwise
limit of the partial flows. -/
theorem tendsto_divergence_dyadicPartialFlow (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ) (x : X) :
    Tendsto (fun m ↦ divergence (d := d) (dyadicPartialFlow (d := d) f m) x)
      atTop (nhds (divergence (d := d) (dyadicFlow (d := d) f) x)) := by
  unfold divergence
  apply tendsto_finsetSum
  intro g hg
  exact (tendsto_dyadicPartialFlow (d := d) f C δ hdecay g
      (-bitVector g +ᵥ x)).sub
    (tendsto_dyadicPartialFlow (d := d) f C δ hdecay g x)

/-- The limiting real flow has divergence `-f`.  For `f = 1_A - 1_B`, this
is the desired target-minus-source demand `1_B - 1_A`. -/
theorem divergence_dyadicFlow_eq_neg (f : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) f C δ) (x : X) :
    divergence (d := d) (dyadicFlow (d := d) f) x = -f x := by
  have hleft : Tendsto
      (fun m ↦ divergence (d := d) (dyadicPartialFlow (d := d) f m) x + f x)
      atTop (nhds (divergence (d := d) (dyadicFlow (d := d) f) x + f x)) :=
    (tendsto_divergence_dyadicPartialFlow (d := d) f C δ hdecay x).add_const _
  have hright : Tendsto
      (fun m ↦ divergence (d := d) (dyadicPartialFlow (d := d) f m) x + f x)
      atTop (nhds 0) := by
    convert tendsto_cubeAverage_dyadic_zero (d := d) f C δ hdecay x using 1
    funext m
    exact divergence_dyadicPartialFlow_add (d := d) f m x
  have hz : divergence (d := d) (dyadicFlow (d := d) f) x + f x = 0 :=
    tendsto_nhds_unique hleft hright
  linarith

/-- The application-facing sign convention: the demand `source - target`
produces divergence `target - source`. -/
theorem divergence_dyadicFlow_sub_eq_target_sub_source
    (source target : X → ℝ) (C δ : ℝ)
    (hdecay : UniformDyadicDecay (d := d) (fun x ↦ source x - target x) C δ)
    (x : X) :
    divergence (d := d) (dyadicFlow (d := d) (fun x ↦ source x - target x)) x =
      target x - source x := by
  rw [divergence_dyadicFlow_eq_neg (d := d) _ C δ hdecay]
  ring

end

end Erdos1124.Flow
