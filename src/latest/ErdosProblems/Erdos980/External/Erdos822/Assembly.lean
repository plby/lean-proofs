/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos980.External.Erdos822.Core
import ErdosProblems.Erdos980.External.Erdos822.FiniteEnergy

/-!
# Density bridges for Erdős Problem 822

The analytic part of the Gabdullin--Iudelevich--Luca proof produces a
uniform lower bound for the number of represented values below `2 * x + 1`.
This file contains the purely order-theoretic conversion of that estimate to
positive lower density.
-/

namespace Erdos822

open Filter

/-- An eventual pointwise lower bound for the partial densities passes to
the lower density. -/
theorem le_lowerDensity_of_eventually_le_partialDensity {S : Set ℕ} {c : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, c ≤ S.partialDensity Set.univ n) :
    c ≤ S.lowerDensity := by
  exact le_liminf_of_le
    (isCoboundedUnder_ge_of_le atTop fun n ↦ Set.partialDensity_le_one S Set.univ n) h

/-- Counting-form bridge: an eventual linear lower bound for `S ∩ [0,n)`
implies the corresponding lower-density bound. -/
theorem le_lowerDensity_of_eventually_count {S : Set ℕ} {c : ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ≤ ((S ∩ Set.Iio n).ncard : ℝ)) :
    c ≤ S.lowerDensity := by
  apply le_lowerDensity_of_eventually_le_partialDensity
  filter_upwards [h, eventually_gt_atTop 0] with n hn hnpos
  rw [Set.partialDensity]
  simp only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  apply (le_div_iff₀ (by exact_mod_cast hnpos)).2
  exact hn

/-- Positive-constant version of the counting bridge. -/
theorem lowerDensity_pos_of_eventually_count {S : Set ℕ} {c : ℝ}
    (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ≤ ((S ∩ Set.Iio n).ncard : ℝ)) :
    0 < S.lowerDensity :=
  hc.trans_le (le_lowerDensity_of_eventually_count h)

/-- Division by three still tends to infinity on the naturals. -/
lemma nat_div_three_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ n / 3) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨3 * b, fun n hn => by omega⟩

/-- The form of the density bridge used after the finite image argument.
If represented values below `2 * x + 1` are eventually at least `c * x`,
then the represented set has positive lower density.  The harmless factor
`1 / 6` absorbs the change from an arbitrary cutoff `N` to `x = N / 3`. -/
theorem lowerDensity_pos_of_eventually_doubled_count {S : Set ℕ} {c : ℝ}
    (hc : 0 < c)
    (h : ∀ᶠ x : ℕ in atTop,
      c * (x : ℝ) ≤ ((S ∩ Set.Iio (2 * x + 1)).ncard : ℝ)) :
    0 < S.lowerDensity := by
  apply lowerDensity_pos_of_eventually_count (c := c / 6) (by positivity)
  have h' := nat_div_three_tendsto_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 4] with n hn hfour
  have hcut : 2 * (n / 3) + 1 ≤ n := by omega
  have hsubset : S ∩ Set.Iio (2 * (n / 3) + 1) ⊆ S ∩ Set.Iio n := by
    intro m hm
    exact ⟨hm.1, hm.2.trans_le hcut⟩
  have hcard :
      ((S ∩ Set.Iio (2 * (n / 3) + 1)).ncard : ℝ) ≤
        ((S ∩ Set.Iio n).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsubset
      ((Set.finite_Iio n).subset Set.inter_subset_right)
  have hscale : n ≤ 6 * (n / 3) := by omega
  have hscaleR : (n : ℝ) ≤ 6 * (n / 3 : ℕ) := by exact_mod_cast hscale
  nlinarith

section GILEnergyAssembly

open Filter

/-- Problem-specific assembly of the GIL energy method.  Once a family of
finite input sets has eventual linear size and eventual linear collision
energy, finite Cauchy--Schwarz gives an eventual linear lower bound for the
number of shifted-totient values, and hence positive lower density. -/
theorem lowerDensity_pos_of_eventually_linear_energy
    (A : ℕ → Finset ℕ) {cA cE : ℝ}
    (hcA : 0 < cA) (hcE : 0 < cE)
    (hA_bound : ∀ᶠ x : ℕ in atTop, ∀ n ∈ A x, n ≤ x)
    (hA_card : ∀ᶠ x : ℕ in atTop, cA * (x : ℝ) ≤ (A x).card)
    (henergy : ∀ᶠ x : ℕ in atTop,
      (collisionEnergy (A x) shiftedTotient : ℝ) ≤ cE * (x : ℝ)) :
    0 < totientRange.lowerDensity := by
  let c : ℝ := cA ^ 2 / cE
  have hc : 0 < c := by
    dsimp [c]
    positivity
  apply lowerDensity_pos_of_eventually_doubled_count hc
  filter_upwards [hA_bound, hA_card, henergy, eventually_gt_atTop 0]
      with x hxbound hxcard hxenergy hxpos
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hcsNat := card_sq_le_image_card_mul_collisionEnergy (A x) shiftedTotient
  have hcs : ((A x).card : ℝ) ^ 2 ≤
      ((A x).image shiftedTotient).card *
        (collisionEnergy (A x) shiftedTotient : ℝ) := by
    exact_mod_cast hcsNat
  have henergy' :
      ((A x).image shiftedTotient).card *
          (collisionEnergy (A x) shiftedTotient : ℝ) ≤
        ((A x).image shiftedTotient).card * (cE * (x : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hxenergy (by positivity)
  have hsq : (cA * (x : ℝ)) ^ 2 ≤ ((A x).card : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hxcard
  have hchain : (cA * (x : ℝ)) ^ 2 ≤
      ((A x).image shiftedTotient).card * (cE * (x : ℝ)) :=
    hsq.trans (hcs.trans henergy')
  have hmain : cA ^ 2 * (x : ℝ) ≤
      cE * ((A x).image shiftedTotient).card := by
    nlinarith
  have himage : c * (x : ℝ) ≤ ((A x).image shiftedTotient).card := by
    calc
      c * (x : ℝ) = (cA ^ 2 * (x : ℝ)) / cE := by
        dsimp [c]
        ring
      _ ≤ ((A x).image shiftedTotient).card :=
        (div_le_iff₀ hcE).2 (by nlinarith)
  have hcountNat := image_card_le_totientRange_count hxbound
  have hcount : (((A x).image shiftedTotient).card : ℝ) ≤
      ((totientRange ∩ Set.Iio (2 * x + 1)).ncard : ℝ) := by
    exact_mod_cast hcountNat
  exact himage.trans hcount

end GILEnergyAssembly

end Erdos822
