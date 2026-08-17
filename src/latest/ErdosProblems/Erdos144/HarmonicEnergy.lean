/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicProb
import ErdosProblems.Erdos448.Basic

/-!
# Normalized signed energy for the harmonic model

This file isolates the exact finite implication used in the global-difference
part of the Maier--Tenenbaum argument.  A selected set has many proper
ternary states.  If the collision energy of their signed-sum map is small,
Cauchy--Schwarz forces many distinct represented differences.

The second half packages the corresponding exceptional-set calculation on
the finite harmonic Bernoulli space.  It is deliberately quantitative and
contains no limiting assertion: any later estimate for the mean normalized
energy can be inserted directly into `prob_stateRich_and_not_spread_le`.
-/

open scoped BigOperators

namespace Erdos144.HarmonicEnergy

noncomputable section

open HarmonicProb

attribute [local instance] Classical.propDecidable

/-! ## Signed states -/

/-- The signed contribution of a selected integer in one ternary state. -/
def signedTerm (i : ℕ) (a : Fin 3) : ℤ :=
  if a = 1 then (i : ℤ) else if a = 2 then -(i : ℤ) else 0

/-- The signed value of a ternary state. -/
def signedValue (S : Finset ℕ) (a : (↑S → Fin 3)) : ℤ :=
  ∑ i, signedTerm i.1 (a i)

/-- Both signs occur in a proper state. -/
def IsProperState {S : Finset ℕ} (a : (↑S → Fin 3)) : Prop :=
  (∃ i, a i = 1) ∧ ∃ i, a i = 2

/-- The finite set of proper ternary states. -/
noncomputable def properSignedStates (S : Finset ℕ) : Finset (↑S → Fin 3) := by
  classical
  exact Finset.univ.filter IsProperState

/-- The represented signed-difference image. -/
noncomputable def signedDifferenceSet (S : Finset ℕ) : Finset ℤ := by
  classical
  exact (properSignedStates S).image (signedValue S)

/-- The collision energy of the signed-value map. -/
noncomputable def signedDifferenceEnergy (S : Finset ℕ) : ℕ := by
  classical
  exact Erdos448.occupiedBinEnergy (properSignedStates S) (signedValue S)

/-- Finite Cauchy--Schwarz for proper signed states. -/
theorem properState_card_sq_le_difference_card_mul_energy (S : Finset ℕ) :
    (properSignedStates S).card ^ 2 ≤
      (signedDifferenceSet S).card * signedDifferenceEnergy S := by
  classical
  exact Erdos448.card_sq_le_card_image_mul_occupiedBinEnergy
    (properSignedStates S) (signedValue S)

/-! ## Pair-state encoding -/

/-- At one ambient coordinate, `none` means that the coordinate was not
selected, while `some (a,b)` records its values in a pair of ternary states.
This is the nine-state encoding used when the signed collision energy is
expanded coordinate by coordinate. -/
abbrev EnergyState := Option (Fin 3 × Fin 3)

/-- Extend a pair of ternary states on `T ⊆ I` to the ambient set `I`, using
`none` at unselected coordinates. -/
def energyProfile (I T : Finset ℕ) (_hTI : T ⊆ I)
    (a b : (↑T → Fin 3)) : ↑I → EnergyState :=
  fun i ↦ if hi : i.1 ∈ T then
    some (a ⟨i.1, hi⟩, b ⟨i.1, hi⟩)
  else none

@[simp] theorem energyProfile_apply_mem {I T : Finset ℕ} (hTI : T ⊆ I)
    (a b : (↑T → Fin 3)) (i : ↑I) (hi : i.1 ∈ T) :
    energyProfile I T hTI a b i = some (a ⟨i.1, hi⟩, b ⟨i.1, hi⟩) := by
  simp [energyProfile, hi]

@[simp] theorem energyProfile_apply_not_mem {I T : Finset ℕ} (hTI : T ⊆ I)
    (a b : (↑T → Fin 3)) (i : ↑I) (hi : i.1 ∉ T) :
    energyProfile I T hTI a b i = none := by
  simp [energyProfile, hi]

/-- The ambient profile loses no information about the two ternary states. -/
theorem energyProfile_injective {I T : Finset ℕ} (hTI : T ⊆ I) :
    Function.Injective (fun q : (↑T → Fin 3) × (↑T → Fin 3) ↦
      energyProfile I T hTI q.1 q.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  apply Prod.ext
  · funext i
    let j : ↑I := ⟨i.1, hTI i.2⟩
    have hj := congrFun h j
    have hp : some (a i, b i) = some (a' i, b' i) := by
      simpa [j, energyProfile] using hj
    exact congrArg Prod.fst (Option.some.inj hp)
  · funext i
    let j : ↑I := ⟨i.1, hTI i.2⟩
    have hj := congrFun h j
    have hp : some (a i, b i) = some (a' i, b' i) := by
      simpa [j, energyProfile] using hj
    exact congrArg Prod.snd (Option.some.inj hp)

/-! ## Deterministic normalized-energy implication -/

/-- The integer numerator of the normalized signed energy at scale `D`.
The analytic argument bounds this relative to
`xi * (properSignedStates S).card ^ 2`. -/
def scaledSignedEnergy (S : Finset ℕ) (D : ℕ) : ℕ :=
  D * signedDifferenceEnergy S

/-- A selected set is state-rich at level `M` if it has at least `M` proper
ternary signed states. -/
def StateRich (S : Finset ℕ) (M : ℕ) : Prop :=
  M ≤ (properSignedStates S).card

/-- The desired global spread conclusion at scale `D` and loss `xi`. -/
def DifferenceSpread (S : Finset ℕ) (D xi : ℕ) : Prop :=
  D ≤ xi * (signedDifferenceSet S).card

/-- The normalized energy condition with the exact numerator and
denominator left in `ℕ`; this avoids all rounding choices. -/
def NormalizedEnergyAtMost (S : Finset ℕ) (D xi : ℕ) : Prop :=
  scaledSignedEnergy S D ≤
    xi * (properSignedStates S).card ^ 2

/-- Strict normalized-energy control.  Its strictness is exactly what gives
the `D / xi` strict lower bound used in the fresh-block iteration. -/
def NormalizedEnergyLt (S : Finset ℕ) (D xi : ℕ) : Prop :=
  scaledSignedEnergy S D <
    xi * (properSignedStates S).card ^ 2

/-- The complete finite regularity package at an interval scale.  The first
field is the dyadic-block support condition, the second is the required
cardinality condition, and the third is the normalized collision-energy
condition furnished by the global-energy calculation. -/
def IsDyadicallyEnergyRegular
    (S : Finset ℕ) (C D xi : ℕ) : Prop :=
  S ⊆ Finset.Ioc C D ∧
    0 < (properSignedStates S).card ∧
    NormalizedEnergyLt S D xi

/-- Cauchy--Schwarz turns a normalized collision-energy bound into a lower
bound for the signed-difference image. -/
theorem differenceSpread_of_normalizedEnergyAtMost
    {S : Finset ℕ} {D xi : ℕ}
    (hstates : 0 < (properSignedStates S).card)
    (henergy : NormalizedEnergyAtMost S D xi) :
    DifferenceSpread S D xi := by
  let P := (properSignedStates S).card
  let R := (signedDifferenceSet S).card
  let E := signedDifferenceEnergy S
  have hcs : P ^ 2 ≤ R * E := by
    simpa [P, R, E] using properState_card_sq_le_difference_card_mul_energy S
  have hmul : D * P ^ 2 ≤ (xi * R) * P ^ 2 := by
    calc
      D * P ^ 2 ≤ D * (R * E) := Nat.mul_le_mul_left D hcs
      _ = R * (D * E) := by ac_rfl
      _ ≤ R * (xi * P ^ 2) := by
        exact Nat.mul_le_mul_left R (by simpa [NormalizedEnergyAtMost,
          scaledSignedEnergy, P, E] using henergy)
      _ = (xi * R) * P ^ 2 := by ac_rfl
  have hPpos : 0 < P ^ 2 := pow_pos (by simpa [P] using hstates) _
  have : D ≤ xi * R := Nat.le_of_mul_le_mul_right hmul hPpos
  simpa [DifferenceSpread, R] using this

/-- Strict form of the finite global-energy lemma. -/
theorem difference_card_large_of_normalizedEnergyLt
    {S : Finset ℕ} {D xi : ℕ}
    (hstates : 0 < (properSignedStates S).card)
    (henergy : NormalizedEnergyLt S D xi) :
    D < xi * (signedDifferenceSet S).card := by
  let P := (properSignedStates S).card
  let R := (signedDifferenceSet S).card
  let E := signedDifferenceEnergy S
  have hcs : P ^ 2 ≤ R * E := by
    simpa [P, R, E] using properState_card_sq_le_difference_card_mul_energy S
  have hmul : D * P ^ 2 < (xi * R) * P ^ 2 := by
    calc
      D * P ^ 2 ≤ D * (R * E) := Nat.mul_le_mul_left D hcs
      _ = R * (D * E) := by ac_rfl
      _ < R * (xi * P ^ 2) := by
        have hR : 0 < R := by
          have hP : 0 < P := by simpa [P] using hstates
          have hP2 : 0 < P ^ 2 := pow_pos hP _
          have hRE : 0 < R * E := lt_of_lt_of_le hP2 hcs
          by_contra hR0
          have : R = 0 := Nat.eq_zero_of_not_pos hR0
          simp [this] at hRE
        exact (Nat.mul_lt_mul_left hR).2 (by simpa [NormalizedEnergyLt,
          scaledSignedEnergy, P, E] using henergy)
      _ = (xi * R) * P ^ 2 := by ac_rfl
  have hP2 : 0 < P ^ 2 := pow_pos (by simpa [P] using hstates) _
  have hDR : D < xi * R := (Nat.mul_lt_mul_right hP2).mp hmul
  simpa [R] using hDR

/-- Real-division version of the strict global-energy conclusion. -/
theorem div_lt_difference_card_of_normalizedEnergyLt
    {S : Finset ℕ} {D xi : ℕ} (hxi : 0 < xi)
    (hstates : 0 < (properSignedStates S).card)
    (henergy : NormalizedEnergyLt S D xi) :
    (D : ℝ) / xi < (signedDifferenceSet S).card := by
  apply (div_lt_iff₀ (by exact_mod_cast hxi)).2
  rw [mul_comm]
  exact_mod_cast difference_card_large_of_normalizedEnergyLt hstates henergy

/-- Interval-supported regular sets have more than `D / xi` represented
signed differences.  This is the pointwise form consumed by a fresh-pair
block step. -/
theorem div_lt_difference_card_of_dyadicallyEnergyRegular
    {S : Finset ℕ} {C D xi : ℕ} (hxi : 0 < xi)
    (hregular : IsDyadicallyEnergyRegular S C D xi) :
    (D : ℝ) / xi < (signedDifferenceSet S).card :=
  div_lt_difference_card_of_normalizedEnergyLt hxi hregular.2.1 hregular.2.2

/-- A state-rich set which fails to have enough represented differences
must have large scaled energy.  This contrapositive form is the one needed
for Markov's inequality. -/
theorem energy_large_of_stateRich_of_not_differenceSpread
    {S : Finset ℕ} {D xi M : ℕ}
    (hrich : StateRich S M) (hspread : ¬ DifferenceSpread S D xi) :
    xi * M ^ 2 ≤ scaledSignedEnergy S D := by
  let P := (properSignedStates S).card
  let R := (signedDifferenceSet S).card
  let E := signedDifferenceEnergy S
  have hcs : P ^ 2 ≤ R * E := by
    simpa [P, R, E] using properState_card_sq_le_difference_card_mul_energy S
  have hMR : xi * M ^ 2 ≤ xi * P ^ 2 := by
    exact Nat.mul_le_mul_left xi (Nat.pow_le_pow_left (by
      simpa [StateRich, P] using hrich) 2)
  have hxiP : xi * P ^ 2 ≤ (xi * R) * E := by
    calc
      xi * P ^ 2 ≤ xi * (R * E) := Nat.mul_le_mul_left xi hcs
      _ = (xi * R) * E := by ac_rfl
  have hxiR : xi * R ≤ D := by
    simpa [DifferenceSpread, R, not_le] using Nat.le_of_lt
      (by simpa [DifferenceSpread, R, not_le] using hspread)
  calc
    xi * M ^ 2 ≤ xi * P ^ 2 := hMR
    _ ≤ (xi * R) * E := hxiP
    _ ≤ D * E := Nat.mul_le_mul_right E hxiR
    _ = scaledSignedEnergy S D := by simp [scaledSignedEnergy, E]

/-! ## Harmonic exceptional mass -/

/-- Real-valued scaled energy, suitable for finite expectations. -/
def scaledSignedEnergyReal (S : Finset ℕ) (D : ℕ) : ℝ :=
  (scaledSignedEnergy S D : ℝ)

lemma scaledSignedEnergyReal_nonneg (S : Finset ℕ) (D : ℕ) :
    0 ≤ scaledSignedEnergyReal S D := by
  exact Nat.cast_nonneg _

/-- Markov bound for the high-energy exceptional set on an arbitrary finite
harmonic probability space. -/
theorem prob_scaledEnergy_ge_le
    (I : Finset ℕ) (hI : ∀ n ∈ I, 1 ≤ n) (D xi M : ℕ)
    (hxi : 0 < xi) (hM : 0 < M) :
    prob I (fun S ↦ ((xi * M ^ 2 : ℕ) : ℝ) ≤
      scaledSignedEnergyReal S D) ≤
      (∑ S ∈ I.powerset, weight I S * scaledSignedEnergyReal S D) /
        (xi * M ^ 2 : ℕ) := by
  have hc : (0 : ℝ) < (xi * M ^ 2 : ℕ) := by
    exact_mod_cast Nat.mul_pos hxi (pow_pos hM 2)
  simpa [scaledSignedEnergyReal] using
    (prob_le_expectation_div I (fun S ↦ scaledSignedEnergyReal S D)
      (xi * M ^ 2 : ℕ) hI
      (fun S _ ↦ scaledSignedEnergyReal_nonneg S D) hc)

/-- The bad event "many proper states but too few represented differences"
is contained in the high-energy event, hence has the same Markov bound. -/
theorem prob_stateRich_and_not_spread_le
    (I : Finset ℕ) (hI : ∀ n ∈ I, 1 ≤ n) (D xi M : ℕ)
    (hxi : 0 < xi) (hM : 0 < M) :
    prob I (fun S ↦ StateRich S M ∧ ¬ DifferenceSpread S D xi) ≤
      (∑ S ∈ I.powerset, weight I S * scaledSignedEnergyReal S D) /
        (xi * M ^ 2 : ℕ) := by
  calc
    prob I (fun S ↦ StateRich S M ∧ ¬ DifferenceSpread S D xi) ≤
        prob I (fun S ↦ ((xi * M ^ 2 : ℕ) : ℝ) ≤
          scaledSignedEnergyReal S D) := by
      apply prob_mono I _ _ hI
      intro S hS
      unfold scaledSignedEnergyReal
      exact_mod_cast
        energy_large_of_stateRich_of_not_differenceSpread hS.1 hS.2
    _ ≤ (∑ S ∈ I.powerset,
        weight I S * scaledSignedEnergyReal S D) / (xi * M ^ 2 : ℕ) :=
      prob_scaledEnergy_ge_le I hI D xi M hxi hM

/-- Epsilon form of the exceptional-mass estimate.  Thus any family of
parameters for which the displayed mean-energy hypothesis holds with
`epsilon → 0` has vanishing harmonic mass of state-rich, poorly spread
sets. -/
theorem prob_stateRich_and_not_spread_le_epsilon
    (I : Finset ℕ) (hI : ∀ n ∈ I, 1 ≤ n) (D xi M : ℕ)
    (epsilon : ℝ) (hxi : 0 < xi) (hM : 0 < M)
    (hmean :
      (∑ S ∈ I.powerset, weight I S * scaledSignedEnergyReal S D) ≤
        epsilon * (xi * M ^ 2 : ℕ)) :
    prob I (fun S ↦ StateRich S M ∧ ¬ DifferenceSpread S D xi) ≤
      epsilon := by
  have hc : (0 : ℝ) < (xi * M ^ 2 : ℕ) := by
    exact_mod_cast Nat.mul_pos hxi (pow_pos hM 2)
  calc
    prob I (fun S ↦ StateRich S M ∧ ¬ DifferenceSpread S D xi) ≤
        (∑ S ∈ I.powerset,
          weight I S * scaledSignedEnergyReal S D) / (xi * M ^ 2 : ℕ) :=
      prob_stateRich_and_not_spread_le I hI D xi M hxi hM
    _ ≤ (epsilon * (xi * M ^ 2 : ℕ)) / (xi * M ^ 2 : ℕ) := by
      exact div_le_div_of_nonneg_right hmean hc.le
    _ = epsilon := by field_simp

/-- Interval-specialized form.  Membership in `(C,D]` automatically gives
the positivity required by the harmonic Bernoulli bookkeeping. -/
theorem prob_Ioc_stateRich_and_not_spread_le_epsilon
    (C D xi M : ℕ) (epsilon : ℝ) (hxi : 0 < xi) (hM : 0 < M)
    (hmean :
      (∑ S ∈ (Finset.Ioc C D).powerset,
        weight (Finset.Ioc C D) S * scaledSignedEnergyReal S D) ≤
        epsilon * (xi * M ^ 2 : ℕ)) :
    prob (Finset.Ioc C D)
        (fun S ↦ StateRich S M ∧ ¬ DifferenceSpread S D xi) ≤
      epsilon := by
  apply prob_stateRich_and_not_spread_le_epsilon
    (Finset.Ioc C D) (fun n hn ↦ ?_) D xi M epsilon hxi hM hmean
  have hnpos := (Finset.mem_Ioc.mp hn).1
  omega

/-- Sequence form of the finite exceptional-mass estimate.  Once the mean
normalized-energy bound tends to zero, the harmonic mass of the bad event
tends to zero as well. -/
theorem exceptionalMass_tendsto_zero
    (I : ℕ → Finset ℕ) (D xi M : ℕ → ℕ) (epsilon : ℕ → ℝ)
    (hI : ∀ t n, n ∈ I t → 1 ≤ n)
    (hxi : ∀ t, 0 < xi t) (hM : ∀ t, 0 < M t)
    (hmean : ∀ t,
      (∑ S ∈ (I t).powerset,
        weight (I t) S * scaledSignedEnergyReal S (D t)) ≤
        epsilon t * (xi t * M t ^ 2 : ℕ))
    (hepsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun t ↦ prob (I t)
        (fun S ↦ StateRich S (M t) ∧
          ¬ DifferenceSpread S (D t) (xi t)))
      Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ))
      Filter.atTop (nhds 0)) hepsilon
  · exact Filter.Eventually.of_forall fun t ↦
      prob_nonneg (I t) _ (hI t)
  · exact Filter.Eventually.of_forall fun t ↦
      prob_stateRich_and_not_spread_le_epsilon
        (I t) (hI t) (D t) (xi t) (M t) (epsilon t)
        (hxi t) (hM t) (hmean t)

end

end Erdos144.HarmonicEnergy
