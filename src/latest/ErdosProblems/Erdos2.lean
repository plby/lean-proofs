/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 2.
https://www.erdosproblems.com/forum/thread/2

Informal authors:
- Paul Balister
- Béla Bollobás
- Robert Morris
- Julian Sahasrabudhe
- Marius Tiba

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos2.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import ErdosProblems.Erdos448.MertensEulerProduct448
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Erdős Problem 2

Erdős asked whether covering systems with distinct moduli can have arbitrarily
large least modulus.  Hough proved that they cannot.  Balister, Bollobás,
Morris, Sahasrabudhe and Tiba gave a distortion-sieve proof and the explicit
bound `616000`.

The mathematical reconstruction and the lemma-by-lemma formalization plan are
in `tex/2.tex`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Erdos2

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The exact covering-system statement -/

/-- A covering system with one residue attached to each member of the finite
set `D` of moduli.  Since `D` is a `Finset`, the moduli are distinct by
construction.  The lower bound `2 ≤ d` excludes the trivial modulus `1`. -/
def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧ ∀ z : ℤ, ∃ d ∈ D, z ≡ a d [ZMOD d]

/-- The positive answer to Erdős's original question.  The theorem below
proves the negation of this proposition. -/
def HasArbitrarilyLargeMinimum : Prop :=
  ∀ N : ℕ, ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
    IsDistinctCoveringSystem D a ∧ ∀ d ∈ D, N ≤ d

/-- The uniform-bound formulation of the negative answer. -/
def HasUniformMinimumBound : Prop :=
  ∃ M : ℕ, ∀ (D : Finset ℕ) (a : ℕ → ℤ),
    IsDistinctCoveringSystem D a → ∃ d ∈ D, d < M

lemma uniformBound_iff_not_arbitrarilyLarge :
    HasUniformMinimumBound ↔ ¬HasArbitrarilyLargeMinimum := by
  constructor
  · rintro ⟨M, hM⟩ hlarge
    obtain ⟨D, a, hcover, hmin⟩ := hlarge M
    obtain ⟨d, hdD, hdM⟩ := hM D a hcover
    exact (not_lt_of_ge (hmin d hdD)) hdM
  · intro hnot
    by_contra huniform
    apply hnot
    change ∀ N : ℕ, ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
      IsDistinctCoveringSystem D a ∧ ∀ d ∈ D, N ≤ d
    intro N
    by_contra hN
    push Not at hN
    apply huniform
    refine ⟨N, ?_⟩
    exact hN

/-! ## Finite probability distributions -/

/-- A probability distribution represented by its weights on a finite type. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  sum_weight : ∑ x, weight x = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

/-- The mass of a finite event. -/
def mass (P : FinProb Ω) (S : Finset Ω) : ℝ :=
  ∑ x ∈ S, P.weight x

@[simp]
lemma mass_empty (P : FinProb Ω) : P.mass ∅ = 0 := by
  simp [mass]

@[simp]
lemma mass_univ (P : FinProb Ω) : P.mass Finset.univ = 1 := by
  simpa [mass] using P.sum_weight

lemma mass_nonneg (P : FinProb Ω) (S : Finset Ω) : 0 ≤ P.mass S := by
  exact Finset.sum_nonneg fun x _ => P.weight_nonneg x

lemma mass_mono (P : FinProb Ω) {S T : Finset Ω} (hST : S ⊆ T) :
    P.mass S ≤ P.mass T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro x hxT hxS
  exact P.weight_nonneg x

lemma mass_union_le [DecidableEq Ω] (P : FinProb Ω) (S T : Finset Ω) :
    P.mass (S ∪ T) ≤ P.mass S + P.mass T := by
  rw [mass, mass, mass]
  calc
    ∑ x ∈ S ∪ T, P.weight x =
        (∑ x ∈ S, P.weight x) + ∑ x ∈ T \ S, P.weight x := by
          rw [show S ∪ T = S ∪ (T \ S) by ext x; simp]
          rw [Finset.sum_union]
          exact Finset.disjoint_sdiff
    _ ≤ (∑ x ∈ S, P.weight x) + ∑ x ∈ T, P.weight x := by
      exact add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset : T \ S ⊆ T)
          fun x hxT hxTS => P.weight_nonneg x) _

lemma mass_biUnion_le_sum {ι : Type*} (P : FinProb Ω) (I : Finset ι) (E : ι → Finset Ω) :
    P.mass (I.biUnion E) ≤ ∑ i ∈ I, P.mass (E i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (P.mass_union_le (E i) (I.biUnion E)).trans
        (add_le_add_right ih _)

lemma exists_outside_of_sum_mass_lt_one
    {ι : Type*} (P : FinProb Ω) (I : Finset ι)
    (E : ι → Finset Ω) (hsmall : (∑ i ∈ I, P.mass (E i)) < 1) :
    ∃ x : Ω, ∀ i ∈ I, x ∉ E i := by
  classical
  have hproper : I.biUnion E ≠ (Finset.univ : Finset Ω) := by
    intro hall
    have hunion : P.mass (I.biUnion E) = 1 := by rw [hall, P.mass_univ]
    have hle := P.mass_biUnion_le_sum I E
    linarith
  by_contra hnone
  push Not at hnone
  apply hproper
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact hnone x

lemma mass_le_of_pointwise (P Q : FinProb Ω)
    (S : Finset Ω) {c : ℝ}
    (hpoint : ∀ x, P.weight x ≤ c * Q.weight x) :
    P.mass S ≤ c * Q.mass S := by
  classical
  rw [mass, mass, Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => hpoint x

lemma mass_sdiff_ge [DecidableEq Ω] (P : FinProb Ω) (S T : Finset Ω) :
    P.mass S - P.mass T ≤ P.mass (S \ T) := by
  have hsub : S ⊆ (S \ T) ∪ T := by
    intro x hx
    by_cases hxt : x ∈ T
    · simp [hxt]
    · simp [hx, hxt]
  have hle := (P.mass_mono hsub).trans (P.mass_union_le (S \ T) T)
  linarith

end FinProb

/-! ## One distortion step on a finite fibre -/

namespace Distortion

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]

/-- The uniform proportion of the fibre `B x`. -/
def fibreDensity (B : X → Finset Y) (x : X) : ℝ :=
  ((B x).card : ℝ) / (Fintype.card Y : ℝ)

lemma card_pos_real : (0 : ℝ) < Fintype.card Y := by
  exact_mod_cast Fintype.card_pos

omit [Fintype X] in
lemma fibreDensity_nonneg (B : X → Finset Y) (x : X) :
    0 ≤ fibreDensity B x := by
  exact div_nonneg (by positivity) (card_pos_real.le)

omit [Fintype X] in
lemma fibreDensity_le_one (B : X → Finset Y) (x : X) :
    fibreDensity B x ≤ 1 := by
  rw [fibreDensity, div_le_one (card_pos_real)]
  exact_mod_cast Finset.card_le_univ (B x)

/-- BBMST's fibre multiplier.  The first branch deletes the bad part when
its fibre density is at most `δ`; the second branch removes exactly `δ` of
the original fibre mass. -/
def multiplier (B : X → Finset Y) (δ : ℝ) (x : X) (y : Y) : ℝ :=
  let α := fibreDensity B x
  if α ≤ δ then
    if y ∈ B x then 0 else (1 - α)⁻¹
  else if y ∈ B x then
    (α - δ) / (α * (1 - δ))
  else
    (1 - δ)⁻¹

/-- Extend `P` uniformly across `Y`, then apply the distortion multiplier. -/
def stepWeight (P : FinProb X) (B : X → Finset Y) (δ : ℝ) : X × Y → ℝ :=
  fun z => P.weight z.1 / (Fintype.card Y : ℝ) * multiplier B δ z.1 z.2

lemma sum_ite_mem (S : Finset Y) (a b : ℝ) :
    ∑ y : Y, (if y ∈ S then a else b) =
      (S.card : ℝ) * a + ((Fintype.card Y - S.card : ℕ) : ℝ) * b := by
  classical
  have hcard : ((Finset.univ.filter fun y : Y => y ∉ S).card) =
      Fintype.card Y - S.card := by
    rw [show (Finset.univ.filter fun y : Y => y ∉ S) = Finset.univ \ S by ext y; simp]
    rw [Finset.card_sdiff]
    simp
  rw [Finset.sum_ite]
  simp [hcard]

omit [Fintype X] in
lemma one_sub_fibreDensity_pos_of_le
    (B : X → Finset Y) (x : X) {δ : ℝ} (hδ : δ < 1)
    (hα : fibreDensity B x ≤ δ) : 0 < 1 - fibreDensity B x := by
  linarith

omit [Fintype X] in
lemma fibreDensity_pos_of_not_le
    (B : X → Finset Y) (x : X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hα : ¬fibreDensity B x ≤ δ) : 0 < fibreDensity B x := by
  exact lt_of_le_of_lt hδ (lt_of_not_ge hα)

lemma cast_card_sub (S : Finset Y) :
    ((Fintype.card Y - S.card : ℕ) : ℝ) =
      (Fintype.card Y : ℝ) - (S.card : ℝ) := by
  exact_mod_cast Nat.cast_sub (Finset.card_le_univ S)

omit [Fintype X] in
/-- The multiplier has average one on every fibre. -/
lemma sum_multiplier (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) :
    ∑ y : Y, multiplier B δ x y = (Fintype.card Y : ℝ) := by
  classical
  let α := fibreDensity B x
  let N : ℝ := Fintype.card Y
  have hN : N ≠ 0 := ne_of_gt card_pos_real
  have hcard : ((B x).card : ℝ) = α * N := by
    dsimp only [α, N, fibreDensity]
    field_simp
  by_cases hα : α ≤ δ
  · simp only [multiplier, α, hα, if_pos]
    rw [sum_ite_mem]
    change ((B x).card : ℝ) * 0 +
        ((Fintype.card Y - (B x).card : ℕ) : ℝ) * (1 - α)⁻¹ = N
    rw [mul_zero, zero_add, cast_card_sub]
    have hne : 1 - α ≠ 0 :=
      ne_of_gt (one_sub_fibreDensity_pos_of_le B x hδ1 hα)
    calc
      ((Fintype.card Y : ℝ) - (B x).card) * (1 - α)⁻¹ =
          (N * (1 - α)) * (1 - α)⁻¹ := by
            rw [hcard]
            change (N - α * N) * (1 - α)⁻¹ = (N * (1 - α)) * (1 - α)⁻¹
            ring
      _ = N := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hδne : 1 - δ ≠ 0 := by linarith
    simp only [multiplier, α, hα, if_false]
    rw [sum_ite_mem]
    change ((B x).card : ℝ) * ((α - δ) / (α * (1 - δ))) +
        ((Fintype.card Y - (B x).card : ℕ) : ℝ) * (1 - δ)⁻¹ = N
    rw [cast_card_sub, hcard]
    change α * N * ((α - δ) / (α * (1 - δ))) +
        (N - α * N) * (1 - δ)⁻¹ = N
    field_simp [hαne, hδne]
    ring

omit [Fintype X] in
lemma multiplier_nonneg (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) (y : Y) :
    0 ≤ multiplier B δ x y := by
  let α := fibreDensity B x
  have hαnonneg : 0 ≤ α := fibreDensity_nonneg B x
  by_cases hα : α ≤ δ
  · simp only [multiplier, α, hα, if_pos]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (by linarith [fibreDensity_le_one B x])
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    have hδpos : 0 < 1 - δ := by linarith
    simp only [multiplier, α, hα, if_false]
    split_ifs
    · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge hα))
        (mul_nonneg hαpos.le hδpos.le)
    · exact inv_nonneg.mpr hδpos.le

omit [Fintype X] in
lemma multiplier_le (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) (y : Y) :
    multiplier B δ x y ≤ (1 - δ)⁻¹ := by
  let α := fibreDensity B x
  have hδpos : 0 < 1 - δ := by linarith
  by_cases hα : α ≤ δ
  · simp only [multiplier, α, hα, if_pos]
    split_ifs
    · exact inv_nonneg.mpr hδpos.le
    · apply (inv_le_inv₀ (by linarith) hδpos).2
      linarith
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    simp only [multiplier, α, hα, if_false]
    split_ifs
    · rw [div_eq_mul_inv, mul_inv]
      calc
        (α - δ) * (α⁻¹ * (1 - δ)⁻¹) =
            ((α - δ) * α⁻¹) * (1 - δ)⁻¹ := by ring
        _ ≤ 1 * (1 - δ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hδpos.le)
          exact mul_inv_le_one_of_le₀ (by linarith) hαpos.le
        _ = (1 - δ)⁻¹ := one_mul _
    · exact le_rfl

/-- One normalized distortion step. -/
def step (P : FinProb X) (B : X → Finset Y) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : FinProb (X × Y) where
  weight := stepWeight P B δ
  weight_nonneg z := mul_nonneg
    (div_nonneg (P.weight_nonneg z.1) card_pos_real.le)
    (multiplier_nonneg B hδ0 hδ1 z.1 z.2)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : X, ∑ y : Y, stepWeight P B δ (x, y) = ∑ x : X, P.weight x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [stepWeight]
        rw [← Finset.mul_sum, sum_multiplier B hδ0 hδ1 x]
        field_simp [ne_of_gt (card_pos_real (Y := Y))]
      _ = 1 := P.sum_weight

/-- Expectation with respect to a finite probability distribution. -/
def expectation (P : FinProb X) (f : X → ℝ) : ℝ :=
  ∑ x : X, P.weight x * f x

lemma expectation_indicator (P : FinProb X) (A : Finset X) (c : ℝ) :
    expectation P (fun x => if x ∈ A then c else 0) = c * P.mass A := by
  rw [expectation, FinProb.mass]
  calc
    ∑ x : X, P.weight x * (if x ∈ A then c else 0) =
        ∑ x ∈ A, P.weight x * c := by
          simp_rw [mul_ite, mul_zero]
          rw [← Finset.sum_filter]
          simp
    _ = (∑ x ∈ A, P.weight x) * c := by rw [Finset.sum_mul]
    _ = c * (∑ x ∈ A, P.weight x) := by ring

lemma expectation_mul_indicators (P : FinProb X) (A B C : Finset X)
    (c d : ℝ) (hC : ∀ x, x ∈ C ↔ x ∈ A ∧ x ∈ B) :
    expectation P (fun x =>
      (if x ∈ A then c else 0) * (if x ∈ B then d else 0)) =
        (c * d) * P.mass C := by
  rw [show (fun x =>
      (if x ∈ A then c else 0) * (if x ∈ B then d else 0)) =
      (fun x => if x ∈ C then c * d else 0) by
    funext x
    by_cases hxC : x ∈ C
    · have hx := (hC x).mp hxC
      simp [hxC, hx.1, hx.2]
    · have hx := mt (hC x).mpr hxC
      simp only [not_and_or] at hx
      rcases hx with hxA | hxB
      · simp [hxC, hxA]
      · simp [hxC, hxB]]
  exact expectation_indicator P C (c * d)

/-- Fraction of the original fibre mass left on its bad part after
distortion. -/
def removedFraction (δ α : ℝ) : ℝ :=
  if α ≤ δ then 0 else (α - δ) / (1 - δ)

omit [Fintype X] in
lemma cast_card_eq_density_mul (B : X → Finset Y) (x : X) :
    ((B x).card : ℝ) = fibreDensity B x * (Fintype.card Y : ℝ) := by
  rw [fibreDensity]
  field_simp [ne_of_gt (card_pos_real (Y := Y))]

lemma sum_stepWeight_bad (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) :
    ∑ y ∈ B x, stepWeight P B δ (x, y) =
      P.weight x * removedFraction δ (fibreDensity B x) := by
  classical
  let α := fibreDensity B x
  let N : ℝ := Fintype.card Y
  have hN : N ≠ 0 := ne_of_gt card_pos_real
  have hcard : ((B x).card : ℝ) = α * N := cast_card_eq_density_mul B x
  have hδne : 1 - δ ≠ 0 := by linarith
  by_cases hα : α ≤ δ
  · rw [removedFraction, if_pos hα, mul_zero]
    apply Finset.sum_eq_zero
    intro y hy
    simp [stepWeight, multiplier, α, hα, hy]
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    have hαne : α ≠ 0 := ne_of_gt hαpos
    simp only [stepWeight, multiplier, removedFraction, α, hα, if_false]
    apply Eq.trans (Finset.sum_congr rfl (fun y hy => by rw [if_pos hy]))
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    change α * N *
        (P.weight x / N * ((α - δ) / (α * (1 - δ)))) =
      P.weight x * ((α - δ) / (1 - δ))
    field_simp [hN, hαne, hδne]

/-- The bad subset of the extended space. -/
def badPairs (B : X → Finset Y) : Finset (X × Y) :=
  Finset.univ.filter fun z => z.2 ∈ B z.1

lemma step_mass_bad (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (step P B δ hδ0 hδ1).mass (badPairs B) =
      expectation P (fun x => removedFraction δ (fibreDensity B x)) := by
  classical
  rw [FinProb.mass]
  change ∑ z ∈ Finset.univ.filter (fun z : X × Y => z.2 ∈ B z.1),
      stepWeight P B δ z = _
  rw [Finset.sum_filter]
  change ∑ z : X × Y, (if z.2 ∈ B z.1 then stepWeight P B δ z else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter]
  change ∑ y ∈ (Finset.univ.filter fun y : Y => y ∈ B x),
      stepWeight P B δ (x, y) = _
  rw [show (Finset.univ.filter fun y : Y => y ∈ B x) = B x by ext y; simp]
  exact sum_stepWeight_bad P B hδ0 hδ1 x

lemma expectation_mono (P : FinProb X) {f g : X → ℝ}
    (hfg : ∀ x, f x ≤ g x) : expectation P f ≤ expectation P g := by
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left (hfg x) (P.weight_nonneg x)

/-- Linearity of finite expectation over a finite family. -/
lemma expectation_finset_sum {ι : Type*} (P : FinProb X) (I : Finset ι)
    (f : ι → X → ℝ) :
    expectation P (fun x => ∑ i ∈ I, f i x) =
      ∑ i ∈ I, expectation P (f i) := by
  classical
  rw [expectation]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The square of a finite sum expands into the double sum of the pairwise
expectations. -/
lemma expectation_sq_finset_sum {ι : Type*} (P : FinProb X) (I : Finset ι)
    (f : ι → X → ℝ) :
    expectation P (fun x => (∑ i ∈ I, f i x) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, expectation P (fun x => f i x * f j x) := by
  classical
  rw [expectation]
  calc
    (∑ x : X, P.weight x * (∑ i ∈ I, f i x) ^ 2) =
        ∑ x : X, ∑ i ∈ I, ∑ j ∈ I,
          P.weight x * (f i x * f j x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x : X,
          P.weight x * (f i x * f j x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ I, expectation P (fun x => f i x * f j x) := by
      rfl

lemma removedFraction_nonneg {δ α : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα0 : 0 ≤ α) : 0 ≤ removedFraction δ α := by
  rw [removedFraction]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (by linarith)

lemma removedFraction_le_first {δ α : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    removedFraction δ α ≤ α := by
  rw [removedFraction]
  split_ifs with h
  · exact hα0
  · rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hα1)]

lemma sub_le_sq_div_four {δ α : ℝ} (hδ : 0 < δ) :
    α - δ ≤ α ^ 2 / (4 * δ) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (α - 2 * δ)]

lemma removedFraction_le_second {δ α : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hα0 : 0 ≤ α) :
    removedFraction δ α ≤ α ^ 2 / (4 * δ * (1 - δ)) := by
  rw [removedFraction]
  split_ifs with h
  · exact div_nonneg (sq_nonneg α) (mul_nonneg (by positivity) (by linarith))
  · rw [div_le_iff₀ (by linarith)]
    calc
      α - δ ≤ α ^ 2 / (4 * δ) := sub_le_sq_div_four hδ0
      _ = α ^ 2 / (4 * δ * (1 - δ)) * (1 - δ) := by
        field_simp [ne_of_gt hδ0, ne_of_gt (show 0 < 1 - δ by linarith)]

/-- First moment of the removed fibre proportions. -/
def firstMoment (P : FinProb X) (B : X → Finset Y) : ℝ :=
  expectation P (fibreDensity B)

/-- Second moment of the removed fibre proportions. -/
def secondMoment (P : FinProb X) (B : X → Finset Y) : ℝ :=
  expectation P (fun x => (fibreDensity B x) ^ 2)

lemma step_mass_bad_le_first (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (step P B δ hδ0 hδ1).mass (badPairs B) ≤ firstMoment P B := by
  rw [step_mass_bad P B hδ0 hδ1]
  exact expectation_mono P fun x =>
    removedFraction_le_first hδ0 hδ1 (fibreDensity_nonneg B x) (fibreDensity_le_one B x)

lemma step_mass_bad_le_second (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (step P B δ hδ0.le hδ1).mass (badPairs B) ≤
      secondMoment P B / (4 * δ * (1 - δ)) := by
  rw [step_mass_bad P B hδ0.le hδ1, secondMoment, expectation]
  calc
    expectation P (fun x => removedFraction δ (fibreDensity B x)) ≤
        expectation P (fun x => (fibreDensity B x) ^ 2 / (4 * δ * (1 - δ))) :=
      expectation_mono P fun x => removedFraction_le_second hδ0 hδ1
        (fibreDensity_nonneg B x)
    _ = (∑ x : X, P.weight x * (fibreDensity B x) ^ 2) /
        (4 * δ * (1 - δ)) := by
      rw [expectation]
      simp_rw [div_eq_mul_inv, mul_assoc]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- Uniform extension of a distribution to one new coordinate. -/
def uniformExtension (P : FinProb X) : FinProb (X × Y) :=
  step P (fun _ => ∅) 0 le_rfl zero_lt_one

@[simp]
lemma uniformExtension_weight (P : FinProb X) (z : X × Y) :
    (uniformExtension P : FinProb (X × Y)).weight z =
      P.weight z.1 / (Fintype.card Y : ℝ) := by
  simp [uniformExtension, step, stepWeight, multiplier, fibreDensity]

lemma step_weight_le_uniform (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (z : X × Y) :
    (step P B δ hδ0 hδ1).weight z ≤
      (1 - δ)⁻¹ * (uniformExtension P).weight z := by
  rw [uniformExtension_weight]
  change P.weight z.1 / (Fintype.card Y : ℝ) * multiplier B δ z.1 z.2 ≤
    (1 - δ)⁻¹ * (P.weight z.1 / (Fintype.card Y : ℝ))
  rw [mul_comm (1 - δ)⁻¹]
  exact mul_le_mul_of_nonneg_left (multiplier_le B hδ0 hδ1 z.1 z.2)
    (div_nonneg (P.weight_nonneg z.1) card_pos_real.le)

lemma step_mass_le_uniform (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S : Finset (X × Y)) :
    (step P B δ hδ0 hδ1).mass S ≤
      (1 - δ)⁻¹ * (uniformExtension P).mass S := by
  exact FinProb.mass_le_of_pointwise _ _ S (step_weight_le_uniform P B hδ0 hδ1)

/-- Pull an event on the old coordinates back to the extended product. -/
def oldPairs (S : Finset X) : Finset (X × Y) :=
  S.product Finset.univ

lemma step_mass_oldPairs (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S : Finset X) :
    (step P B δ hδ0 hδ1).mass (oldPairs S) = P.mass S := by
  classical
  rw [FinProb.mass, FinProb.mass]
  change ∑ z ∈ S.product (Finset.univ : Finset Y), stepWeight P B δ z =
    ∑ x ∈ S, P.weight x
  calc
    ∑ z ∈ S.product (Finset.univ : Finset Y), stepWeight P B δ z =
        ∑ x ∈ S, ∑ y ∈ (Finset.univ : Finset Y), stepWeight P B δ (x, y) := by
      exact Finset.sum_product S Finset.univ (stepWeight P B δ)
    _ = ∑ x ∈ S, P.weight x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [stepWeight]
      rw [← Finset.mul_sum, sum_multiplier B hδ0 hδ1 x]
      field_simp [ne_of_gt (card_pos_real (Y := Y))]

/-! ## Iterating the distortion -/

/-- A positive coordinate size. -/
abbrev PosNat := {n : ℕ // 0 < n}

/-- A finite coordinate of the specified positive size. -/
abbrev Coordinate (q : PosNat) := Fin (q : ℕ)

instance coordinateNonempty (q : PosNat) : Nonempty (Coordinate q) :=
  ⟨⟨0, q.property⟩⟩

/-- The first `n` coordinates, associated to the left.  This orientation
makes adjoining coordinate `n` definitionally a product. -/
@[reducible] def Prefix (q : ℕ → PosNat) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Prefix q n × Coordinate (q n)

instance prefixFintype (q : ℕ → PosNat) : (n : ℕ) → Fintype (Prefix q n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd (Prefix q n) (Coordinate (q n))
      (prefixFintype q n) inferInstance

/-- The data needed at each stage of a finite distortion sieve. -/
structure Schedule (q : ℕ → PosNat) where
  bad : (n : ℕ) → Prefix q n → Finset (Coordinate (q n))
  delta : ℕ → ℝ
  delta_nonneg : ∀ n, 0 ≤ delta n
  delta_lt_one : ∀ n, delta n < 1

/-- Unit mass on the empty prefix. -/
def unitProb : FinProb PUnit where
  weight _ := 1
  weight_nonneg _ := zero_le_one
  sum_weight := by simp

/-- The probability distribution after `n` distortion steps. -/
def prefixProb {q : ℕ → PosNat} (S : Schedule q) :
    (n : ℕ) → FinProb (Prefix q n)
  | 0 => unitProb
  | n + 1 => step (prefixProb S n) (S.bad n) (S.delta n)
      (S.delta_nonneg n) (S.delta_lt_one n)

/-- Residues not removed in the first `n` stages. -/
def residual {q : ℕ → PosNat} (S : Schedule q) :
    (n : ℕ) → Finset (Prefix q n)
  | 0 => Finset.univ
  | n + 1 => oldPairs (residual S n) \ badPairs (S.bad n)

/-- Actual distorted mass of the bad set at stage `n`. -/
def stageCost {q : ℕ → PosNat} (S : Schedule q) (n : ℕ) : ℝ :=
  (prefixProb S (n + 1)).mass (badPairs (S.bad n))

@[simp]
lemma prefixProb_succ {q : ℕ → PosNat} (S : Schedule q) (n : ℕ) :
    prefixProb S (n + 1) = step (prefixProb S n) (S.bad n) (S.delta n)
      (S.delta_nonneg n) (S.delta_lt_one n) := rfl

@[simp]
lemma residual_zero {q : ℕ → PosNat} (S : Schedule q) :
    residual S 0 = Finset.univ := rfl

lemma residual_mass_lower {q : ℕ → PosNat} (S : Schedule q) (n : ℕ) :
    1 - ∑ i ∈ Finset.range n, stageCost S i ≤
      (prefixProb S n).mass (residual S n) := by
  induction n with
  | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, residual_zero]
        using (prefixProb S 0).mass_univ.ge
  | succ n ih =>
      rw [Finset.sum_range_succ]
      let R : Finset (Prefix q (n + 1)) :=
        oldPairs (residual S n) \ badPairs (S.bad n)
      have hres : residual S (n + 1) = R := by
        rw [residual]
      rw [hres, prefixProb_succ]
      have hdiff := (prefixProb S (n + 1)).mass_sdiff_ge
        (oldPairs (residual S n)) (badPairs (S.bad n))
      have hold : (prefixProb S (n + 1)).mass (oldPairs (residual S n)) =
          (prefixProb S n).mass (residual S n) :=
        step_mass_oldPairs (prefixProb S n) (S.bad n)
          (S.delta_nonneg n) (S.delta_lt_one n) (residual S n)
      rw [hold] at hdiff
      rw [sub_add_eq_sub_sub]
      calc
        1 - ∑ i ∈ Finset.range n, stageCost S i - stageCost S n ≤
            (prefixProb S n).mass (residual S n) - stageCost S n :=
          sub_le_sub_right ih _
        _ ≤ (prefixProb S (n + 1)).mass R := by
          simpa only [stageCost, R] using hdiff

lemma residual_nonempty_of_sum_cost_lt_one {q : ℕ → PosNat}
    (S : Schedule q) (n : ℕ)
    (hsmall : (∑ i ∈ Finset.range n, stageCost S i) < 1) :
    (residual S n).Nonempty := by
  have hpos : 0 < (prefixProb S n).mass (residual S n) :=
    lt_of_lt_of_le (sub_pos.mpr hsmall) (residual_mass_lower S n)
  by_contra hempty
  have hz : residual S n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [hz, FinProb.mass_empty] at hpos
  exact lt_irrefl 0 hpos

lemma residual_nonempty_of_stage_bounds {q : ℕ → PosNat}
    (S : Schedule q) (n : ℕ) (c : ℕ → ℝ)
    (hcost : ∀ i < n, stageCost S i ≤ c i)
    (hsmall : (∑ i ∈ Finset.range n, c i) < 1) :
    (residual S n).Nonempty := by
  apply residual_nonempty_of_sum_cost_lt_one S n
  exact (Finset.sum_le_sum fun i hi => hcost i (Finset.mem_range.mp hi)).trans_lt hsmall

/-! ## Product boxes under the iterated distortion -/

/-- A coordinatewise box in a finite prefix. -/
def box {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i))) :
    (n : ℕ) → Finset (Prefix q n)
  | 0 => Finset.univ
  | n + 1 => (box A n).product (A n)

@[simp]
lemma box_zero {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i))) :
    box A 0 = Finset.univ := rfl

@[simp]
lemma box_succ {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i))) (n : ℕ) :
    box A (n + 1) = (box A n).product (A n) := rfl

lemma mem_box_pair {q : ℕ → PosNat}
    (A B : (i : ℕ) → Finset (Coordinate (q i))) :
    ∀ (n : ℕ) (x : Prefix q n),
      x ∈ box (fun i => A i ∩ B i) n ↔ x ∈ box A n ∧ x ∈ box B n := by
  intro n
  induction n with
  | zero => intro x; simp [box]
  | succ n ih =>
      intro z
      rcases z with ⟨x, y⟩
      constructor
      · intro h
        have hp := Finset.mem_product.mp h
        have hx := (ih x).mp hp.1
        have hy := Finset.mem_inter.mp hp.2
        exact ⟨Finset.mem_product.mpr ⟨hx.1, hy.1⟩,
          Finset.mem_product.mpr ⟨hx.2, hy.2⟩⟩
      · rintro ⟨hA, hB⟩
        have hpA := Finset.mem_product.mp hA
        have hpB := Finset.mem_product.mp hB
        exact Finset.mem_product.mpr ⟨(ih x).mpr ⟨hpA.1, hpB.1⟩,
          Finset.mem_inter.mpr ⟨hpA.2, hpB.2⟩⟩

lemma uniformExtension_mass_product
    (P : FinProb X) (S : Finset X) (T : Finset Y) :
    (uniformExtension P : FinProb (X × Y)).mass (S.product T) =
      P.mass S * ((T.card : ℝ) / (Fintype.card Y : ℝ)) := by
  classical
  rw [FinProb.mass, FinProb.mass]
  calc
    ∑ z ∈ S.product T, (uniformExtension P).weight z =
        ∑ x ∈ S, ∑ y ∈ T, (uniformExtension P).weight (x, y) := by
      exact Finset.sum_product S T (uniformExtension P).weight
    _ = ∑ x ∈ S, P.weight x * ((T.card : ℝ) / (Fintype.card Y : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [uniformExtension_weight]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = (∑ x ∈ S, P.weight x) * ((T.card : ℝ) / (Fintype.card Y : ℝ)) := by
      rw [Finset.sum_mul]

/-- The factor paid by a box at one declared active coordinate.  Inactive
coordinates are required to be unrestricted and cost exactly one. -/
def boxFactor {q : ℕ → PosNat} (S : Schedule q)
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (active : ℕ → Prop) [DecidablePred active] (i : ℕ) : ℝ :=
  if active i then
    (1 - S.delta i)⁻¹ *
      (((A i).card : ℝ) / (Fintype.card (Coordinate (q i)) : ℝ))
  else 1

lemma boxFactor_nonneg {q : ℕ → PosNat} (S : Schedule q)
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (active : ℕ → Prop) [DecidablePred active] (i : ℕ) :
    0 ≤ boxFactor S A active i := by
  rw [boxFactor]
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one i]))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact zero_le_one

/-- A coordinate box has the uniform box mass, multiplied only by the
distortion factors at coordinates on which it is nontrivial. -/
lemma prefixProb_mass_box_le {q : ℕ → PosNat} (S : Schedule q)
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (active : ℕ → Prop) [DecidablePred active]
    (hinactive : ∀ i, ¬active i → A i = Finset.univ) (n : ℕ) :
    (prefixProb S n).mass (box A n) ≤
      ∏ i ∈ Finset.range n, boxFactor S A active i := by
  induction n with
  | zero =>
      rw [box_zero, FinProb.mass_univ]
      simp
  | succ n ih =>
      rw [Finset.prod_range_succ, box_succ]
      by_cases hactive : active n
      · have hstep :
            (prefixProb S (n + 1)).mass ((box A n).product (A n)) ≤
              (1 - S.delta n)⁻¹ *
                (uniformExtension (prefixProb S n)).mass
                  ((box A n).product (A n)) :=
          step_mass_le_uniform (prefixProb S n) (S.bad n)
            (S.delta_nonneg n) (S.delta_lt_one n) ((box A n).product (A n))
        rw [uniformExtension_mass_product] at hstep
        rw [boxFactor, if_pos hactive]
        calc
          (prefixProb S (n + 1)).mass ((box A n).product (A n)) ≤
              (1 - S.delta n)⁻¹ *
                ((prefixProb S n).mass (box A n) *
                  (((A n).card : ℝ) /
                    (Fintype.card (Coordinate (q n)) : ℝ))) := hstep
          _ = (prefixProb S n).mass (box A n) *
                ((1 - S.delta n)⁻¹ *
                  (((A n).card : ℝ) /
                    (Fintype.card (Coordinate (q n)) : ℝ))) := by ring
          _ ≤ (∏ i ∈ Finset.range n, boxFactor S A active i) *
                ((1 - S.delta n)⁻¹ *
                  (((A n).card : ℝ) /
                    (Fintype.card (Coordinate (q n)) : ℝ))) := by
              exact mul_le_mul_of_nonneg_right ih
                (mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one n]))
                  (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · have hfull := hinactive n hactive
        have hold :
            (prefixProb S (n + 1)).mass (oldPairs (box A n)) =
              (prefixProb S n).mass (box A n) :=
          step_mass_oldPairs (prefixProb S n) (S.bad n)
            (S.delta_nonneg n) (S.delta_lt_one n) (box A n)
        rw [hfull, show (box A n).product Finset.univ = oldPairs (box A n) from rfl,
          hold, boxFactor, if_neg hactive, mul_one]
        exact ih

/-- The recursively associated prefix is canonically the dependent product
of its coordinates. -/
def prefixEquivPi (q : ℕ → PosNat) :
    (n : ℕ) → Prefix q n ≃ ((i : Fin n) → Coordinate (q i))
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => PUnit.unit
        left_inv := by intro x; cases x; rfl
        right_inv := by intro f; funext i; exact Fin.elim0 i }
  | n + 1 =>
      ((prefixEquivPi q n).prodCongr (Equiv.refl (Coordinate (q n)))).trans
      ((Equiv.prodComm _ _).trans
          (Fin.snocEquiv (fun i : Fin (n + 1) => Coordinate (q i))))

/-- Membership in a recursively associated product box is equivalent to
coordinatewise membership after applying the canonical prefix equivalence. -/
lemma mem_box_iff_mem_coordinate {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (n : ℕ) (x : Prefix q n) :
    x ∈ box A n ↔ ∀ i : Fin n, (prefixEquivPi q n x) i ∈ A i.1 := by
  induction n with
  | zero =>
      simp only [box_zero, Finset.mem_univ, true_iff]
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      rcases x with ⟨x, y⟩
      rw [box_succ]
      refine Finset.mem_product.trans ?_
      rw [ih]
      constructor
      · rintro ⟨hx, hy⟩ i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [prefixEquivPi] using hy
        · simpa [prefixEquivPi] using hx j
      · intro h
        constructor
        · intro j
          simpa [prefixEquivPi] using h j.castSucc
        · simpa [prefixEquivPi] using h (Fin.last n)

@[simp]
lemma mem_badPairs_iff {X Y : Type*} [Fintype X] [Fintype Y]
    (B : X → Finset Y) (x : X) (y : Y) :
    (x, y) ∈ badPairs B ↔ y ∈ B x := by
  simp [badPairs]

end Distortion

/-! ## Finite congruence fibres -/

namespace Arithmetic

/-- The fibre of reduction from `ZMod n` to `ZMod m`. -/
def zmodFiber {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (a : ZMod m) : Finset (ZMod n) :=
  Finset.univ.filter fun x => ZMod.castHom h (ZMod m) x = a

@[simp]
lemma mem_zmodFiber {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (a : ZMod m) (x : ZMod n) :
    x ∈ zmodFiber h a ↔ ZMod.castHom h (ZMod m) x = a := by
  simp only [zmodFiber, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every fibre of a surjective reduction map between finite residue rings
has the expected normalized cardinality. -/
lemma zmodFiber_card_div_card {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod m) :
    (((zmodFiber h a).card : ℝ) / (Fintype.card (ZMod n) : ℝ)) =
      1 / (m : ℝ) := by
  classical
  let f : ZMod n →+ ZMod m := (ZMod.castHom h (ZMod m)).toAddMonoidHom
  have hsurj : Function.Surjective f := ZMod.castHom_surjective h
  have hfiber (b : ZMod m) :
      ((Finset.univ.filter fun x : ZMod n => f x = b).card) =
        (zmodFiber h a).card := by
    rw [zmodFiber]
    change ((Finset.univ.filter fun x : ZMod n => f x = b).card) =
      (Finset.univ.filter fun x : ZMod n => f x = a).card
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj b) (hsurj a)
  have hmaps :
      ((Finset.univ : Finset (ZMod n)) : Set (ZMod n)).MapsTo f
        ((Finset.univ : Finset (ZMod m)) : Set (ZMod m)) := by
    intro x hx
    exact Finset.mem_univ _
  have hcount :
      Fintype.card (ZMod n) =
        ∑ b : ZMod m, (Finset.univ.filter fun x : ZMod n => f x = b).card := by
    rw [Fintype.card, Finset.card_eq_sum_card_fiberwise hmaps]
  rw [show (∑ b : ZMod m,
      (Finset.univ.filter fun x : ZMod n => f x = b).card) =
        Fintype.card (ZMod m) * (zmodFiber h a).card by
      simp_rw [hfiber]
      simp] at hcount
  simp only [ZMod.card] at hcount ⊢
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hcountR : (n : ℝ) = (m : ℝ) * ((zmodFiber h a).card : ℝ) := by
    exact_mod_cast hcount
  field_simp [hm, hn]
  nlinarith [hcountR]

/-- The same reduction fibre, transported to the canonical `Fin n`
coordinate used by the distortion recursion. -/
def finZmodFiber {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (a : ZMod m) : Finset (Fin n) :=
  (zmodFiber h a).map (ZMod.finEquiv n).symm.toEmbedding

lemma finZmodFiber_card_div_card {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod m) :
    (((finZmodFiber h a).card : ℝ) / (Fintype.card (Fin n) : ℝ)) =
      1 / (m : ℝ) := by
  rw [finZmodFiber, Finset.card_map, Fintype.card_fin]
  simpa only [ZMod.card] using zmodFiber_card_div_card h a

@[simp]
lemma mem_finZmodFiber {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod m) (x : Fin n) :
    x ∈ finZmodFiber h a ↔
      ZMod.castHom h (ZMod m) (ZMod.finEquiv n x) = a := by
  simp [finZmodFiber, mem_zmodFiber]

/-! ### Enumerating the prime-power coordinates of a period -/

abbrev PrimeIndex (Q : ℕ) := {p : ℕ // p ∈ Q.primeFactors}

def primeCount (Q : ℕ) : ℕ := Q.primeFactors.card

/-- The increasing enumeration of the distinct prime divisors of `Q`. -/
def primeEnum (Q : ℕ) : Fin (primeCount Q) ≃o PrimeIndex Q :=
  monoEquivOfFin (PrimeIndex Q) (by simp [primeCount])

def primeAt (Q : ℕ) (i : Fin (primeCount Q)) : ℕ :=
  primeEnum Q i

lemma primeAt_mem (Q : ℕ) (i : Fin (primeCount Q)) :
    primeAt Q i ∈ Q.primeFactors :=
  (primeEnum Q i).property

lemma primeAt_prime (Q : ℕ) (i : Fin (primeCount Q)) :
    (primeAt Q i).Prime :=
  Nat.prime_of_mem_primeFactors (primeAt_mem Q i)

lemma primeAt_strictMono (Q : ℕ) : StrictMono (primeAt Q) := by
  intro i j hij
  exact_mod_cast (primeEnum Q).lt_iff_lt.mpr hij

/-- Coordinate `i` is the full prime power of the `i`th prime in `Q`.
Outside the finite range it is the harmless one-point coordinate. -/
def primePowerSize (Q i : ℕ) : Distortion.PosNat :=
  if h : i < primeCount Q then
    let p := primeAt Q ⟨i, h⟩
    ⟨p ^ Q.factorization p, pow_pos (primeAt_prime Q ⟨i, h⟩).pos _⟩
  else
    ⟨1, zero_lt_one⟩

@[simp]
lemma primePowerSize_of_lt (Q : ℕ) {i : ℕ} (hi : i < primeCount Q) :
    ((primePowerSize Q i : Distortion.PosNat) : ℕ) =
      (primeAt Q ⟨i, hi⟩) ^ Q.factorization (primeAt Q ⟨i, hi⟩) := by
  simp [primePowerSize, hi]

/-- Product of the first `n` enumerated prime-power coordinates. -/
def partialModulus (Q n : ℕ) : ℕ :=
  ∏ i : Fin n, ((primePowerSize Q i : Distortion.PosNat) : ℕ)

lemma partialModulus_full {Q : ℕ} (hQ : Q ≠ 0) :
    partialModulus Q (primeCount Q) = Q := by
  rw [partialModulus]
  calc
    ∏ i : Fin (primeCount Q),
        ((primePowerSize Q i : Distortion.PosNat) : ℕ) =
      ∏ p : PrimeIndex Q, p.1 ^ Q.factorization p.1 := by
        apply Fintype.prod_equiv (primeEnum Q).toEquiv
        intro i
        simp [primePowerSize, primeAt]
    _ = Q := (Nat.prod_primeFactors_coe_pow_factorization hQ).symm

/-- One enumerated `Fin` coordinate, identified with its residue ring. -/
def finPrimePowerEquiv (Q : ℕ) (i : Fin (primeCount Q)) :
    Distortion.Coordinate (primePowerSize Q i) ≃
      ZMod ((primeAt Q i) ^ Q.factorization (primeAt Q i)) :=
  letI : NeZero ((primeAt Q i) ^ Q.factorization (primeAt Q i)) :=
    ⟨pow_ne_zero _ (primeAt_prime Q i).ne_zero⟩
  (Equiv.cast (congrArg Fin (primePowerSize_of_lt Q i.isLt))).trans
    (ZMod.finEquiv ((primeAt Q i) ^ Q.factorization (primeAt Q i))).toEquiv

/-- The full recursively associated product is the usual CRT residue ring. -/
def prefixCRTEq (Q : ℕ) (hQ : Q ≠ 0) :
    Distortion.Prefix (primePowerSize Q) (primeCount Q) ≃ ZMod Q :=
  (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q)).trans <|
    (Equiv.piCongrRight fun i : Fin (primeCount Q) => finPrimePowerEquiv Q i).trans <|
      (Equiv.piCongrLeft
        (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
        (primeEnum Q).toEquiv).trans
          (ZMod.equivPi (n := Q) hQ).symm.toEquiv

/-! ### One-coordinate congruence restrictions -/

/-- In a `p^γ` coordinate, impose one residue modulo `p^e`; exponent zero
is represented by the full coordinate. -/
def primeRestriction (p γ e : ℕ) (hp : p.Prime) (he : e ≤ γ)
    (b : ℤ) : Finset (Fin (p ^ γ)) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ γ) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact if hzero : e = 0 then Finset.univ else
    finZmodFiber (pow_dvd_pow p he) (b : ZMod (p ^ e))

lemma primeRestriction_zero (p γ : ℕ) (hp : p.Prime) (b : ℤ) :
    primeRestriction p γ 0 hp (Nat.zero_le γ) b = Finset.univ := by
  simp [primeRestriction]

lemma primeRestriction_card_div (p γ e : ℕ) (hp : p.Prime) (he : e ≤ γ)
    (b : ℤ) :
    (((primeRestriction p γ e hp he b).card : ℝ) /
        (Fintype.card (Fin (p ^ γ)) : ℝ)) =
      1 / ((p ^ e : ℕ) : ℝ) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ γ) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_cases hzero : e = 0
  · subst e
    rw [primeRestriction_zero]
    simp only [Finset.card_univ, Fintype.card_fin, pow_zero, Nat.cast_one, div_one]
    exact div_self (by exact_mod_cast pow_ne_zero γ hp.ne_zero)
  · simp only [primeRestriction, hzero, ↓reduceDIte]
    exact finZmodFiber_card_div_card (pow_dvd_pow p he) (b : ZMod (p ^ e))

/-- Coordinate restrictions for the congruence `z ≡ b (mod d)`, expressed
inside the prime-power coordinates of a multiple `Q` of `d`. -/
def classCoordinates (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (i : ℕ) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) := by
  by_cases hi : i < primeCount Q
  · let j : Fin (primeCount Q) := ⟨i, hi⟩
    let p := primeAt Q j
    let γ := Q.factorization p
    let e := d.factorization p
    have hp : p.Prime := primeAt_prime Q j
    have he : e ≤ γ := (Nat.factorization_le_iff_dvd hd hQ).mpr hdQ p
    let R : Finset (Fin (p ^ γ)) := primeRestriction p γ e hp he b
    let castE : Fin (p ^ γ) ≃ Distortion.Coordinate (primePowerSize Q i) :=
      Equiv.cast (congrArg Fin (primePowerSize_of_lt Q hi).symm)
    exact R.map castE.toEmbedding
  · exact Finset.univ

/-- A coordinate is active precisely when `d` contains its prime. -/
def classActive (Q d i : ℕ) : Prop :=
  if hi : i < primeCount Q then
    d.factorization (primeAt Q ⟨i, hi⟩) ≠ 0
  else False

lemma classCoordinates_of_not_active (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0)
    (hdQ : d ∣ Q) (b : ℤ) (i : ℕ) (hi : ¬classActive Q d i) :
    classCoordinates Q d hQ hd hdQ b i = Finset.univ := by
  rw [classActive] at hi
  by_cases hir : i < primeCount Q
  · simp only [hir, ↓reduceDIte, not_not] at hi
    rw [classCoordinates]
    simp only [hir, ↓reduceDIte]
    simp only [primeRestriction, hi, ↓reduceDIte]
    exact Finset.map_univ_equiv _
  · simp [classCoordinates, hir]

lemma classCoordinates_card_div (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0)
    (hdQ : d ∣ Q) (b : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((classCoordinates Q d hQ hd hdQ b i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) =
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  rw [classCoordinates]
  simp only [hi, ↓reduceDIte]
  rw [Finset.card_map, Fintype.card_fin, primePowerSize_of_lt Q hi]
  simpa only [Fintype.card_fin] using
    (primeRestriction_card_div
      (primeAt Q ⟨i, hi⟩)
      (Q.factorization (primeAt Q ⟨i, hi⟩))
      (d.factorization (primeAt Q ⟨i, hi⟩))
      (primeAt_prime Q ⟨i, hi⟩)
      ((Nat.factorization_le_iff_dvd hd hQ).mpr hdQ _)
      b)

/-- The prefix event determined by one congruence class. -/
def classBox (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (n : ℕ) : Finset (Distortion.Prefix (primePowerSize Q) n) :=
  Distortion.box (classCoordinates Q d hQ hd hdQ b) n

/-- A congruence class is a coordinate box, so its distorted mass is bounded
by the product of its active coordinate factors. -/
lemma prefixProb_mass_classBox_le
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) (b : ℤ) (n : ℕ) :
    (Distortion.prefixProb S n).mass (classBox Q d hQ hd hdQ b n) ≤
      ∏ i ∈ Finset.range n,
        Distortion.boxFactor S (classCoordinates Q d hQ hd hdQ b)
          (classActive Q d) i := by
  exact Distortion.prefixProb_mass_box_le S
    (classCoordinates Q d hQ hd hdQ b) (classActive Q d)
    (classCoordinates_of_not_active Q d hQ hd hdQ b) n

/-- The explicit factor contributed by a congruence class at one coordinate. -/
def classFactor (S : Distortion.Schedule (primePowerSize Q))
    (d i : ℕ) : ℝ :=
  if hi : i < primeCount Q then
    if d.factorization (primeAt Q ⟨i, hi⟩) = 0 then 1 else
      (1 - S.delta i)⁻¹ /
        (((primeAt Q ⟨i, hi⟩) ^
          d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
  else 1

lemma boxFactor_classCoordinates
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) (b : ℤ) (i : ℕ) :
    Distortion.boxFactor S (classCoordinates Q d hQ hd hdQ b)
        (classActive Q d) i = classFactor S d i := by
  rw [Distortion.boxFactor, classActive, classFactor]
  by_cases hi : i < primeCount Q
  · simp only [hi, ↓reduceDIte]
    by_cases he : d.factorization (primeAt Q ⟨i, hi⟩) = 0
    · simp [he]
    · simp only [he, if_false]
      rw [classCoordinates_card_div Q d hQ hd hdQ b hi]
      split
      · ring
      · rename_i hzero
        have hz : d.factorization (primeAt Q ⟨i, hi⟩) = 0 := by
          simpa only using not_ne_iff.mp hzero
        exact (he hz).elim
  · simp [hi]

lemma prefixProb_mass_classBox_le_explicit
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) (b : ℤ) (n : ℕ) :
    (Distortion.prefixProb S n).mass (classBox Q d hQ hd hdQ b n) ≤
      ∏ i ∈ Finset.range n, classFactor S d i := by
  simpa only [boxFactor_classCoordinates S hQ hd hdQ b] using
    prefixProb_mass_classBox_le S hQ hd hdQ b n

/-! ### Intersections of two congruence-class boxes -/

def pairCoordinates (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) (i : ℕ) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) :=
  classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i ∩
    classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i

def pairActive (Q d₁ d₂ i : ℕ) : Prop :=
  classActive Q d₁ i ∨ classActive Q d₂ i

lemma pairCoordinates_of_not_active (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) (i : ℕ) (hi : ¬pairActive Q d₁ d₂ i) :
    pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i =
      Finset.univ := by
  rw [pairActive, not_or] at hi
  rw [pairCoordinates,
    classCoordinates_of_not_active Q d₁ hQ hd₁ hd₁Q b₁ i hi.1,
    classCoordinates_of_not_active Q d₂ hQ hd₂ hd₂Q b₂ i hi.2]
  exact Finset.inter_self _

lemma pairCoordinates_card_div_le_left (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d₁.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  calc
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      (((classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_left :
            classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i ∩
                classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i ⊆
              classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i)
    _ = _ := classCoordinates_card_div Q d₁ hQ hd₁ hd₁Q b₁ hi

lemma pairCoordinates_card_div_le_right (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d₂.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  calc
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      (((classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_right :
            classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i ∩
                classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i ⊆
              classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i)
    _ = _ := classCoordinates_card_div Q d₂ hQ hd₂ hd₂Q b₂ hi

lemma pairCoordinates_card_div_le_max (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      1 / (((primeAt Q ⟨i, hi⟩) ^
        max (d₁.factorization (primeAt Q ⟨i, hi⟩))
          (d₂.factorization (primeAt Q ⟨i, hi⟩)) : ℕ) : ℝ) := by
  by_cases he : d₁.factorization (primeAt Q ⟨i, hi⟩) ≤
      d₂.factorization (primeAt Q ⟨i, hi⟩)
  · rw [max_eq_right he]
    exact pairCoordinates_card_div_le_right Q d₁ d₂ hQ hd₁ hd₂
      hd₁Q hd₂Q b₁ b₂ hi
  · rw [max_eq_left (le_of_not_ge he)]
    exact pairCoordinates_card_div_le_left Q d₁ d₂ hQ hd₁ hd₂
      hd₁Q hd₂Q b₁ b₂ hi

/-- Membership in both congruence-class boxes is coordinatewise membership in
their intersection box. -/
lemma mem_pairBox_iff (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) (n : ℕ) (x : Distortion.Prefix (primePowerSize Q) n) :
    x ∈ Distortion.box
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂) n ↔
      x ∈ classBox Q d₁ hQ hd₁ hd₁Q b₁ n ∧
        x ∈ classBox Q d₂ hQ hd₂ hd₂Q b₂ n := by
  exact Distortion.mem_box_pair
    (classCoordinates Q d₁ hQ hd₁ hd₁Q b₁)
    (classCoordinates Q d₂ hQ hd₂ hd₂Q b₂) n x

/-- The explicit coordinate factor for an intersection of two congruence
classes; the larger of the two prime exponents controls its density. -/
def pairFactor (S : Distortion.Schedule (primePowerSize Q))
    (d₁ d₂ i : ℕ) : ℝ :=
  if hi : i < primeCount Q then
    let e := max (d₁.factorization (primeAt Q ⟨i, hi⟩))
      (d₂.factorization (primeAt Q ⟨i, hi⟩))
    if e = 0 then 1 else
      (1 - S.delta i)⁻¹ * (1 /
        (((primeAt Q ⟨i, hi⟩) ^ e : ℕ) : ℝ)
      )
  else 1

lemma boxFactor_pairCoordinates_le
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q) (b₁ b₂ : ℤ) (i : ℕ) :
    Distortion.boxFactor S
        (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂)
        (pairActive Q d₁ d₂) i ≤ pairFactor S d₁ d₂ i := by
  rw [Distortion.boxFactor, pairFactor]
  by_cases hi : i < primeCount Q
  · simp only [hi, ↓reduceDIte]
    let e₁ := d₁.factorization (primeAt Q ⟨i, hi⟩)
    let e₂ := d₂.factorization (primeAt Q ⟨i, hi⟩)
    change
      (if pairActive Q d₁ d₂ i then
          (1 - S.delta i)⁻¹ *
            (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
              (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ))
        else 1) ≤
        if max e₁ e₂ = 0 then 1 else
          (1 - S.delta i)⁻¹ *
            (1 / (((primeAt Q ⟨i, hi⟩) ^ max e₁ e₂ : ℕ) : ℝ))
    by_cases he : max e₁ e₂ = 0
    · have hz₁ : e₁ = 0 := by omega
      have hz₂ : e₂ = 0 := by omega
      have hnot : ¬pairActive Q d₁ d₂ i := by
        rw [pairActive, classActive, classActive]
        simp only [hi, ↓reduceDIte, not_or, not_not]
        exact ⟨by simpa only [e₁] using hz₁, by simpa only [e₂] using hz₂⟩
      rw [if_neg hnot, if_pos he]
    · have hactive : pairActive Q d₁ d₂ i := by
        rw [pairActive, classActive, classActive]
        simp only [hi, ↓reduceDIte]
        by_contra hz
        rw [not_or] at hz
        apply he
        have hz₁ : e₁ = 0 := by
          simpa only [e₁] using not_ne_iff.mp hz.1
        have hz₂ : e₂ = 0 := by
          simpa only [e₂] using not_ne_iff.mp hz.2
        simp [hz₁, hz₂]
      rw [if_pos hactive, if_neg he]
      have hinv : 0 ≤ (1 - S.delta i)⁻¹ :=
        inv_nonneg.mpr (by linarith [S.delta_lt_one i])
      calc
        (1 - S.delta i)⁻¹ *
              (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
                (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
            (1 - S.delta i)⁻¹ *
              (1 / (((primeAt Q ⟨i, hi⟩) ^ max e₁ e₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (pairCoordinates_card_div_le_max Q d₁ d₂ hQ hd₁ hd₂
              hd₁Q hd₂Q b₁ b₂ hi) hinv
        _ = (1 - S.delta i)⁻¹ *
              (1 / (((primeAt Q ⟨i, hi⟩) ^ max e₁ e₂ : ℕ) : ℝ)) := rfl
  · have hnot : ¬pairActive Q d₁ d₂ i := by
      simp [pairActive, classActive, hi]
    simp [hi, hnot]

lemma prefixProb_mass_pairBox_le
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q) (b₁ b₂ : ℤ) (n : ℕ) :
    (Distortion.prefixProb S n).mass
        (Distortion.box
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂) n) ≤
      ∏ i ∈ Finset.range n, pairFactor S d₁ d₂ i := by
  calc
    (Distortion.prefixProb S n).mass
        (Distortion.box
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂) n) ≤
      ∏ i ∈ Finset.range n,
        Distortion.boxFactor S
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂)
          (pairActive Q d₁ d₂) i :=
        Distortion.prefixProb_mass_box_le S _ _
          (pairCoordinates_of_not_active Q d₁ d₂ hQ hd₁ hd₂
            hd₁Q hd₂Q b₁ b₂) n
    _ ≤ ∏ i ∈ Finset.range n, pairFactor S d₁ d₂ i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Distortion.boxFactor_nonneg S _ _ i
      · intro i hi
        exact boxFactor_pairCoordinates_le S hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i

/-! ### The arithmetic distortion schedule -/

/-- The modulus `d` is assigned to coordinate `i` when `i` is the largest
prime-power coordinate occurring in `d`. -/
def assignedAt (Q d i : ℕ) : Prop :=
  if hi : i < primeCount Q then
    d.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
    ∀ j, i < j → (hj : j < primeCount Q) →
      d.factorization (primeAt Q ⟨j, hj⟩) = 0
  else False

abbrev ModulusIndex (D : Finset ℕ) := {d : ℕ // d ∈ D}

def stageIndices (Q : ℕ) (D : Finset ℕ) (i : ℕ) :
    Finset (ModulusIndex D) :=
  Finset.univ.filter fun d => assignedAt Q d i

/-- The section of one congruence class in the new coordinate over an old
prefix. -/
def classSection (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (i : ℕ) (x : Distortion.Prefix (primePowerSize Q) i)
    (d : ModulusIndex D) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) :=
  if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
    classCoordinates Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i
  else ∅

/-- At a prime-power stage, remove the union of the sections of precisely the
classes assigned to that stage. -/
def stageBad (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (i : ℕ) (x : Distortion.Prefix (primePowerSize Q) i) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) :=
  (stageIndices Q D i).biUnion (classSection Q D a hQ hd hdQ i x)

def arithmeticSchedule (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) :
    Distortion.Schedule (primePowerSize Q) where
  bad := stageBad Q D a hQ hd hdQ
  delta := delta
  delta_nonneg := hdelta0
  delta_lt_one := hdelta1

lemma classSection_card_div (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (x : Distortion.Prefix (primePowerSize Q) i) (d : ModulusIndex D) :
    (((classSection Q D a hQ hd hdQ i x d).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) =
      if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
        1 / (((primeAt Q ⟨i, hi⟩) ^
          d.1.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
      else 0 := by
  rw [classSection]
  split
  · rename_i hx
    rw [classCoordinates_card_div Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) hi]
  · rename_i hx
    simp

lemma fibreDensity_stageBad_le (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (x : Distortion.Prefix (primePowerSize Q) i) :
    Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i) x ≤
      ∑ d ∈ stageIndices Q D i,
        if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
          1 / (((primeAt Q ⟨i, hi⟩) ^
            d.1.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
        else 0 := by
  rw [Distortion.fibreDensity, stageBad]
  have hcard : ((stageIndices Q D i).biUnion
      (classSection Q D a hQ hd hdQ i x)).card ≤
      ∑ d ∈ stageIndices Q D i, (classSection Q D a hQ hd hdQ i x d).card :=
    Finset.card_biUnion_le
  calc
    (((stageIndices Q D i).biUnion
        (classSection Q D a hQ hd hdQ i x)).card : ℝ) /
          (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ) ≤
      ((↑(∑ d ∈ stageIndices Q D i,
          (classSection Q D a hQ hd hdQ i x d).card) : ℝ) /
          (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast hcard
    _ = ∑ d ∈ stageIndices Q D i,
        (((classSection Q D a hQ hd hdQ i x d).card : ℝ) /
          (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
        push_cast
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
    _ = ∑ d ∈ stageIndices Q D i,
        if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
          1 / (((primeAt Q ⟨i, hi⟩) ^
            d.1.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro d hdstage
          exact classSection_card_div Q D a hQ hd hdQ hi x d

/-- The proportion of the `i`-th prime-power coordinate fixed by modulus
`d`.  Outside the actual coordinate range it is set to zero. -/
def stageCoefficient (Q d i : ℕ) : ℝ :=
  if hi : i < primeCount Q then
    1 / (((primeAt Q ⟨i, hi⟩) ^
      d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
  else 0

lemma stageCoefficient_of_lt (Q d : ℕ) {i : ℕ} (hi : i < primeCount Q) :
    stageCoefficient Q d i =
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  simp [stageCoefficient, hi]

lemma stageCoefficient_nonneg (Q d i : ℕ) : 0 ≤ stageCoefficient Q d i := by
  rw [stageCoefficient]
  split
  · positivity
  · exact le_rfl

lemma fibreDensity_stageBad_le' (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (x : Distortion.Prefix (primePowerSize Q) i) :
    Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i) x ≤
      ∑ d ∈ stageIndices Q D i,
        if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
          stageCoefficient Q d.1 i
        else 0 := by
  simpa only [stageCoefficient_of_lt Q _ hi] using
    fibreDensity_stageBad_le Q D a hQ hd hdQ hi x

lemma firstMoment_stageBad_le (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          (Distortion.prefixProb S i).mass
            (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  let P := Distortion.prefixProb S i
  let I := stageIndices Q D i
  let f := fun d : ModulusIndex D => fun x : Distortion.Prefix (primePowerSize Q) i =>
    if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
      stageCoefficient Q d.1 i
    else 0
  change Distortion.firstMoment P (stageBad Q D a hQ hd hdQ i) ≤
    ∑ d ∈ I, stageCoefficient Q d.1 i *
      P.mass (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i)
  rw [Distortion.firstMoment]
  calc
    Distortion.expectation P
        (Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i)) ≤
      Distortion.expectation P (fun x => ∑ d ∈ I, f d x) :=
        Distortion.expectation_mono P fun x =>
          fibreDensity_stageBad_le' Q D a hQ hd hdQ hi x
    _ = ∑ d ∈ I, Distortion.expectation P (f d) :=
      Distortion.expectation_finset_sum P I f
    _ = ∑ d ∈ I, stageCoefficient Q d.1 i *
        P.mass (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i) := by
      apply Finset.sum_congr rfl
      intro d hdI
      exact Distortion.expectation_indicator P
        (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i)
        (stageCoefficient Q d.1 i)

lemma secondMoment_stageBad_le (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          (Distortion.prefixProb S i).mass
            (Distortion.box
              (pairCoordinates Q d₁.1 d₂.1 hQ
                (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
                (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
                (a d₁.1) (a d₂.1)) i) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  let P := Distortion.prefixProb S i
  let I := stageIndices Q D i
  let A := fun d : ModulusIndex D =>
    classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i
  let f := fun d : ModulusIndex D => fun x : Distortion.Prefix (primePowerSize Q) i =>
    if x ∈ A d then stageCoefficient Q d.1 i else 0
  change Distortion.secondMoment P (stageBad Q D a hQ hd hdQ i) ≤
    ∑ d₁ ∈ I, ∑ d₂ ∈ I,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        P.mass (Distortion.box
          (pairCoordinates Q d₁.1 d₂.1 hQ
            (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
            (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
            (a d₁.1) (a d₂.1)) i)
  rw [Distortion.secondMoment]
  calc
    Distortion.expectation P
        (fun x => Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i) x ^ 2) ≤
      Distortion.expectation P (fun x => (∑ d ∈ I, f d x) ^ 2) := by
        apply Distortion.expectation_mono P
        intro x
        have hle := fibreDensity_stageBad_le' Q D a hQ hd hdQ hi x
        have hleft := Distortion.fibreDensity_nonneg
          (stageBad Q D a hQ hd hdQ i) x
        have hright : 0 ≤ ∑ d ∈ I, f d x := by
          apply Finset.sum_nonneg
          intro d hdI
          dsimp only [f]
          split
          · exact stageCoefficient_nonneg Q d.1 i
          · exact le_rfl
        nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hright hleft)]
    _ = ∑ d₁ ∈ I, ∑ d₂ ∈ I,
        Distortion.expectation P (fun x => f d₁ x * f d₂ x) :=
      Distortion.expectation_sq_finset_sum P I f
    _ = ∑ d₁ ∈ I, ∑ d₂ ∈ I,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          P.mass (Distortion.box
            (pairCoordinates Q d₁.1 d₂.1 hQ
              (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
              (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
              (a d₁.1) (a d₂.1)) i) := by
      apply Finset.sum_congr rfl
      intro d₁ hd₁I
      apply Finset.sum_congr rfl
      intro d₂ hd₂I
      exact Distortion.expectation_mul_indicators P (A d₁) (A d₂)
        (Distortion.box
          (pairCoordinates Q d₁.1 d₂.1 hQ
            (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
            (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
            (a d₁.1) (a d₂.1)) i)
        (stageCoefficient Q d₁.1 i) (stageCoefficient Q d₂.1 i)
        (mem_pairBox_iff Q d₁.1 d₂.1 hQ
          (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
          (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
          (a d₁.1) (a d₂.1) i)

lemma firstMoment_stageBad_le_products (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          ∏ j ∈ Finset.range i, classFactor S d.1 j := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          (Distortion.prefixProb S i).mass
            (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i) :=
        firstMoment_stageBad_le Q D a hQ hd hdQ delta hdelta0 hdelta1 hi
    _ ≤ ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          ∏ j ∈ Finset.range i, classFactor S d.1 j := by
      apply Finset.sum_le_sum
      intro d hdI
      exact mul_le_mul_of_nonneg_left
        (prefixProb_mass_classBox_le_explicit S hQ (hd d.1 d.2)
          (hdQ d.1 d.2) (a d.1) i)
        (stageCoefficient_nonneg Q d.1 i)

lemma secondMoment_stageBad_le_products (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          (Distortion.prefixProb S i).mass
            (Distortion.box
              (pairCoordinates Q d₁.1 d₂.1 hQ
                (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
                (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
                (a d₁.1) (a d₂.1)) i) :=
        secondMoment_stageBad_le Q D a hQ hd hdQ delta hdelta0 hdelta1 hi
    _ ≤ ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j := by
      apply Finset.sum_le_sum
      intro d₁ hd₁I
      apply Finset.sum_le_sum
      intro d₂ hd₂I
      apply mul_le_mul_of_nonneg_left
      · exact prefixProb_mass_pairBox_le S hQ
          (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
          (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
          (a d₁.1) (a d₂.1) i
      · exact mul_nonneg (stageCoefficient_nonneg Q d₁.1 i)
          (stageCoefficient_nonneg Q d₂.1 i)

/-! ### Encoding stage moduli by their exponent vectors -/

def stageCoordinate (Q : ℕ) {i : ℕ} (hi : i < primeCount Q)
    (j : Fin (i + 1)) : Fin (primeCount Q) :=
  ⟨j.1, j.2.trans_le (Nat.succ_le_of_lt hi)⟩

abbrev StageExponentVector (Q : ℕ) {i : ℕ} (hi : i < primeCount Q) :=
  (j : Fin (i + 1)) →
    Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)

def stageExponentVector (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0)
    (hdQ : d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    StageExponentVector Q hi :=
  fun j =>
    ⟨d.factorization (primeAt Q (stageCoordinate Q hi j)),
      Nat.lt_succ_of_le ((Nat.factorization_le_iff_dvd hd hQ).mpr hdQ _)⟩

lemma primeAt_primeEnum_symm (Q : ℕ) (p : PrimeIndex Q) :
    primeAt Q ((primeEnum Q).symm p) = p.1 := by
  exact congrArg Subtype.val ((primeEnum Q).apply_symm_apply p)

lemma stageExponentVector_injective (Q : ℕ) (D : Finset ℕ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) :
    Set.InjOn
      (fun d : ModulusIndex D =>
        stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi)
      (stageIndices Q D i) := by
  intro d₁ hd₁I d₂ hd₂I hvec
  apply Subtype.ext
  apply Nat.eq_of_factorization_eq (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
  intro p
  by_cases hpQ : p ∈ Q.primeFactors
  · let k : Fin (primeCount Q) := (primeEnum Q).symm ⟨p, hpQ⟩
    have hpk : primeAt Q k = p := primeAt_primeEnum_symm Q ⟨p, hpQ⟩
    by_cases hki : k.1 ≤ i
    · let j : Fin (i + 1) := ⟨k.1, Nat.lt_succ_iff.mpr hki⟩
      have hjk : stageCoordinate Q hi j = k := by
        apply Fin.ext
        rfl
      have hv := congrArg Fin.val (congrFun hvec j)
      change d₁.1.factorization (primeAt Q (stageCoordinate Q hi j)) =
        d₂.1.factorization (primeAt Q (stageCoordinate Q hi j)) at hv
      simpa only [hjk, hpk] using hv
    · have hik : i < k.1 := lt_of_not_ge hki
      have ha₁ : assignedAt Q d₁.1 i := (Finset.mem_filter.mp hd₁I).2
      have ha₂ : assignedAt Q d₂.1 i := (Finset.mem_filter.mp hd₂I).2
      have ha₁' : d₁.1.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
          ∀ j, i < j → (hj : j < primeCount Q) →
            d₁.1.factorization (primeAt Q ⟨j, hj⟩) = 0 := by
        simpa only [assignedAt, hi, ↓reduceDIte] using ha₁
      have ha₂' : d₂.1.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
          ∀ j, i < j → (hj : j < primeCount Q) →
            d₂.1.factorization (primeAt Q ⟨j, hj⟩) = 0 := by
        simpa only [assignedAt, hi, ↓reduceDIte] using ha₂
      have hz₁ := ha₁'.2 k.1 hik k.2
      have hz₂ := ha₂'.2 k.1 hik k.2
      simpa only [hpk] using hz₁.trans hz₂.symm
  · by_cases hp : p.Prime
    · have hpndQ : ¬p ∣ Q := by
        intro hpQdvd
        exact hpQ ((Nat.mem_primeFactors).mpr ⟨hp, hpQdvd, hQ⟩)
      have hpnd₁ : ¬p ∣ d₁.1 := fun hpd => hpndQ (hpd.trans (hdQ d₁.1 d₁.2))
      have hpnd₂ : ¬p ∣ d₂.1 := fun hpd => hpndQ (hpd.trans (hdQ d₂.1 d₂.2))
      rw [Nat.factorization_eq_zero_of_not_dvd hpnd₁,
        Nat.factorization_eq_zero_of_not_dvd hpnd₂]
    · rw [Nat.factorization_eq_zero_of_not_prime d₁.1 hp,
        Nat.factorization_eq_zero_of_not_prime d₂.1 hp]

lemma assignedAt_iff_of_lt (Q d : ℕ) {i : ℕ} (hi : i < primeCount Q) :
    assignedAt Q d i ↔
      d.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
        ∀ j, i < j → (hj : j < primeCount Q) →
          d.factorization (primeAt Q ⟨j, hj⟩) = 0 := by
  simp [assignedAt, hi]

/-- Local first-moment weight of one exponent.  At the last coordinate zero
is excluded; at earlier coordinates exponent zero contributes one. -/
def firstLocalFactor (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1))
    (e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) : ℝ :=
  let p := primeAt Q (stageCoordinate Q hi j)
  if j.1 = i then
    if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ))
  else if e.1 = 0 then 1 else
    (1 - S.delta j.1)⁻¹ / (((p ^ e.1 : ℕ) : ℝ))

/-- Local second-moment weight of a pair of exponents. -/
def secondLocalFactor (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1))
    (e₁ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) : ℝ :=
  let p := primeAt Q (stageCoordinate Q hi j)
  if j.1 = i then
    if e₁.1 = 0 ∨ e₂.1 = 0 then 0 else
      1 / (((p ^ (e₁.1 + e₂.1) : ℕ) : ℝ))
  else
    let e := max e₁.1 e₂.1
    if e = 0 then 1 else
      (1 - S.delta j.1)⁻¹ / (((p ^ e : ℕ) : ℝ))

lemma firstLocalFactor_nonneg
    (S : Distortion.Schedule (primePowerSize Q)) {i : ℕ}
    (hi : i < primeCount Q) (j : Fin (i + 1))
    (e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) :
    0 ≤ firstLocalFactor S hi j e := by
  rw [firstLocalFactor]
  split <;> split
  · exact le_rfl
  · positivity
  · exact zero_le_one
  · exact mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])) (by positivity)

lemma secondLocalFactor_nonneg
    (S : Distortion.Schedule (primePowerSize Q)) {i : ℕ}
    (hi : i < primeCount Q) (j : Fin (i + 1))
    (e₁ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) :
    0 ≤ secondLocalFactor S hi j e₁ e₂ := by
  rw [secondLocalFactor]
  split
  · split
    · exact le_rfl
    · positivity
  · dsimp only
    split
    · exact zero_le_one
    · exact mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])) (by positivity)

lemma prod_firstLocal_stageExponent
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) (ha : assignedAt Q d i) :
    (∏ j : Fin (i + 1),
      firstLocalFactor S hi j (stageExponentVector Q d hQ hd hdQ hi j)) =
      stageCoefficient Q d i *
        ∏ j ∈ Finset.range i, classFactor S d j := by
  rw [Fin.prod_univ_castSucc, Finset.prod_range]
  have hlast : (Fin.last i : Fin (i + 1)).1 = i := rfl
  have hapos := (assignedAt_iff_of_lt Q d hi).mp ha
  have hcurrent :
      (stageExponentVector Q d hQ hd hdQ hi (Fin.last i)).1 =
        d.factorization (primeAt Q ⟨i, hi⟩) := by
    rfl
  have hlastFactor :
      firstLocalFactor S hi (Fin.last i)
          (stageExponentVector Q d hQ hd hdQ hi (Fin.last i)) =
        stageCoefficient Q d i := by
    rw [firstLocalFactor, stageCoefficient_of_lt Q d hi]
    simp only [hlast, if_true, hcurrent, if_neg hapos.1]
    rfl
  rw [hlastFactor, mul_comm]
  congr 1
  apply Fintype.prod_congr
  intro j
  have hj : j.1 < primeCount Q := j.2.trans hi
  have hjne : (j.castSucc : Fin (i + 1)).1 ≠ i := Nat.ne_of_lt j.2
  rw [firstLocalFactor, classFactor]
  simp only [hj, ↓reduceDIte, hjne, if_false, stageExponentVector,
    stageCoordinate]
  by_cases he : d.factorization (primeAt Q ⟨j.1, hj⟩) = 0
  · simp [he]
  · simp [he]

lemma prod_secondLocal_stageExponent
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (ha₁ : assignedAt Q d₁ i) (ha₂ : assignedAt Q d₂ i) :
    (∏ j : Fin (i + 1),
      secondLocalFactor S hi j
        (stageExponentVector Q d₁ hQ hd₁ hd₁Q hi j)
        (stageExponentVector Q d₂ hQ hd₂ hd₂Q hi j)) =
      (stageCoefficient Q d₁ i * stageCoefficient Q d₂ i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁ d₂ j := by
  rw [Fin.prod_univ_castSucc, Finset.prod_range]
  have hapos₁ := (assignedAt_iff_of_lt Q d₁ hi).mp ha₁
  have hapos₂ := (assignedAt_iff_of_lt Q d₂ hi).mp ha₂
  have hlastFactor :
      secondLocalFactor S hi (Fin.last i)
          (stageExponentVector Q d₁ hQ hd₁ hd₁Q hi (Fin.last i))
          (stageExponentVector Q d₂ hQ hd₂ hd₂Q hi (Fin.last i)) =
        stageCoefficient Q d₁ i * stageCoefficient Q d₂ i := by
    rw [secondLocalFactor, stageCoefficient_of_lt Q d₁ hi,
      stageCoefficient_of_lt Q d₂ hi]
    simp only [Fin.val_last, if_true, stageExponentVector, stageCoordinate,
      hapos₁.1, hapos₂.1, or_false, if_false]
    have hp : primeAt Q ⟨i, hi⟩ ≠ 0 := (primeAt_prime Q ⟨i, hi⟩).ne_zero
    push_cast
    rw [pow_add]
    field_simp
  rw [hlastFactor, mul_comm]
  congr 1
  apply Fintype.prod_congr
  intro j
  have hj : j.1 < primeCount Q := j.2.trans hi
  have hjne : (j.castSucc : Fin (i + 1)).1 ≠ i := Nat.ne_of_lt j.2
  rw [secondLocalFactor, pairFactor]
  simp only [hj, ↓reduceDIte, hjne, if_false, stageExponentVector,
    stageCoordinate]
  let e₁ := d₁.factorization (primeAt Q ⟨j.1, hj⟩)
  let e₂ := d₂.factorization (primeAt Q ⟨j.1, hj⟩)
  by_cases he : max e₁ e₂ = 0
  · simp [e₁, e₂, he]
  · simp [e₁, e₂, he, div_eq_mul_inv]

def firstVectorWeight (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (v : StageExponentVector Q hi) : ℝ :=
  ∏ j : Fin (i + 1), firstLocalFactor S hi j (v j)

lemma firstVectorWeight_nonneg (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (v : StageExponentVector Q hi) :
    0 ≤ firstVectorWeight S hi v := by
  exact Finset.prod_nonneg fun j hj => firstLocalFactor_nonneg S hi j (v j)

lemma sum_stage_first_products_le_euler
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d ∈ stageIndices Q D i,
      stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          firstLocalFactor S hi j e := by
  let I := stageIndices Q D i
  let g := fun d : ModulusIndex D =>
    stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi
  let w := firstVectorWeight S hi
  have hinj : Set.InjOn g I := stageExponentVector_injective Q D hQ hd hdQ hi
  calc
    (∑ d ∈ I, stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) =
      ∑ d ∈ I, w (g d) := by
        apply Finset.sum_congr rfl
        intro d hdI
        dsimp only [w, g, firstVectorWeight]
        rw [prod_firstLocal_stageExponent S hQ (hd d.1 d.2) (hdQ d.1 d.2) hi
          ((Finset.mem_filter.mp hdI).2)]
    _ = ∑ v ∈ I.image g, w v := by
      rw [Finset.sum_image]
      intro d₁ hd₁I d₂ hd₂I heq
      exact hinj hd₁I hd₂I heq
    _ ≤ ∑ v : StageExponentVector Q hi, w v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v hvuniv hvimage
      exact firstVectorWeight_nonneg S hi v
    _ = ∏ j : Fin (i + 1),
        ∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          firstLocalFactor S hi j e := by
      dsimp only [w, firstVectorWeight]
      exact (Fintype.prod_sum (fun j e => firstLocalFactor S hi j e)).symm

def piPairEquiv {I : Type*} (E : I → Type*) :
    ((∀ i, E i) × (∀ i, E i)) ≃ (∀ i, E i × E i) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv z := rfl
  right_inv z := rfl

lemma sum_pair_pi_prod {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, Fintype (E i)]
    (f : ∀ i, E i → E i → ℝ) :
    (∑ x : ∀ i, E i, ∑ y : ∀ i, E i, ∏ i, f i (x i) (y i)) =
      ∏ i, ∑ a : E i, ∑ b : E i, f i a b := by
  calc
    (∑ x : ∀ i, E i, ∑ y : ∀ i, E i, ∏ i, f i (x i) (y i)) =
        ∑ z : (∀ i, E i) × (∀ i, E i), ∏ i, f i (z.1 i) (z.2 i) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ z : ∀ i, E i × E i, ∏ i, f i (z i).1 (z i).2 := by
      exact Fintype.sum_equiv (piPairEquiv E)
        (fun z => ∏ i, f i (z.1 i) (z.2 i))
        (fun z => ∏ i, f i (z i).1 (z i).2) (fun z => rfl)
    _ = ∏ i, ∑ z : E i × E i, f i z.1 z.2 := by
      exact (Fintype.prod_sum (fun (i : I) (z : E i × E i) => f i z.1 z.2)).symm
    _ = ∏ i, ∑ a : E i, ∑ b : E i, f i a b := by
      apply Fintype.prod_congr
      intro i
      rw [Fintype.sum_prod_type]

abbrev StageExponentPair (Q : ℕ) {i : ℕ} (hi : i < primeCount Q) :=
  (j : Fin (i + 1)) →
    (Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1) ×
      Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1))

lemma sum_stage_second_products_le_euler
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
            secondLocalFactor S hi j e₁ e₂ := by
  let I := stageIndices Q D i
  let g := fun d : ModulusIndex D =>
    stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi
  let gp : ModulusIndex D × ModulusIndex D → StageExponentPair Q hi :=
    fun z j => (g z.1 j, g z.2 j)
  let w : StageExponentPair Q hi → ℝ := fun v =>
    ∏ j : Fin (i + 1), secondLocalFactor S hi j (v j).1 (v j).2
  have hinj : Set.InjOn g I := stageExponentVector_injective Q D hQ hd hdQ hi
  have hinjp : Set.InjOn gp (I.product I) := by
    intro z₁ hz₁ z₂ hz₂ hgp
    have hz₁' := Finset.mem_product.mp hz₁
    have hz₂' := Finset.mem_product.mp hz₂
    apply Prod.ext
    · apply hinj hz₁'.1 hz₂'.1
      funext j
      exact congrArg Prod.fst (congrFun hgp j)
    · apply hinj hz₁'.2 hz₂'.2
      funext j
      exact congrArg Prod.snd (congrFun hgp j)
  have hw (v : StageExponentPair Q hi) : 0 ≤ w v := by
    exact Finset.prod_nonneg fun j hj =>
      secondLocalFactor_nonneg S hi j (v j).1 (v j).2
  calc
    (∑ d₁ ∈ I, ∑ d₂ ∈ I,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) =
      ∑ d₁ ∈ I, ∑ d₂ ∈ I, w (gp (d₁, d₂)) := by
        apply Finset.sum_congr rfl
        intro d₁ hd₁I
        apply Finset.sum_congr rfl
        intro d₂ hd₂I
        dsimp only [w, gp, g]
        exact (prod_secondLocal_stageExponent S hQ
          (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
          (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2) hi
          ((Finset.mem_filter.mp hd₁I).2)
          ((Finset.mem_filter.mp hd₂I).2)).symm
    _ = ∑ z ∈ I.product I, w (gp z) := by
      exact (Finset.sum_product I I (fun z => w (gp z))).symm
    _ = ∑ v ∈ (I.product I).image gp, w v := by
      rw [Finset.sum_image]
      intro z₁ hz₁ z₂ hz₂ heq
      exact hinjp hz₁ hz₂ heq
    _ ≤ ∑ v : StageExponentPair Q hi, w v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v hvuniv hvimage
      exact hw v
    _ = ∏ j : Fin (i + 1),
        ∑ e : (Fin (Q.factorization
            (primeAt Q (stageCoordinate Q hi j)) + 1) ×
          Fin (Q.factorization
            (primeAt Q (stageCoordinate Q hi j)) + 1)),
          secondLocalFactor S hi j e.1 e.2 := by
      dsimp only [w]
      exact (Fintype.prod_sum (fun j (e :
          Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1) ×
            Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) =>
        secondLocalFactor S hi j e.1 e.2)).symm
    _ = ∏ j : Fin (i + 1),
        ∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
            secondLocalFactor S hi j e₁ e₂ := by
      apply Fintype.prod_congr
      intro j
      rw [Fintype.sum_prod_type]

/-! ### Elementary finite geometric estimates -/

lemma fin_inv_pow_sum_eq (p γ : ℕ) (hp : p ≠ 0) (hp1 : p ≠ 1) :
    (∑ e : Fin (γ + 1),
      if e.1 = 0 then (0 : ℝ) else 1 / (((p ^ e.1 : ℕ) : ℝ))) =
      (1 - ((p : ℝ)⁻¹) ^ γ) / ((p : ℝ) - 1) := by
  induction γ with
  | zero => simp
  | succ γ ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, ih, Fin.val_last, Nat.succ_ne_zero, if_false]
      push_cast
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
      have hp1R : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp1)
      have hcancel : (p : ℝ) ^ γ * (1 / (p : ℝ)) ^ γ = 1 := by
        rw [← mul_pow]
        field_simp
        simp
      have hbase : (p : ℝ) * (1 / (p : ℝ)) = 1 := by
        field_simp
      have hboth : ((p : ℝ) ^ γ * (1 / (p : ℝ)) ^ γ) *
          ((p : ℝ) * (1 / (p : ℝ))) = 1 := by
        rw [hcancel, hbase, one_mul]
      field_simp [hpR, hp1R]
      rw [pow_succ, pow_succ]
      nlinarith [hcancel, hboth]

lemma fin_inv_pow_sum_le (p γ : ℕ) (hp2 : 2 ≤ p) :
    (∑ e : Fin (γ + 1),
      if e.1 = 0 then (0 : ℝ) else 1 / (((p ^ e.1 : ℕ) : ℝ))) ≤
      1 / ((p : ℝ) - 1) := by
  rw [fin_inv_pow_sum_eq p γ (by omega) (by omega)]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hden : 0 < (p : ℝ) - 1 := by linarith
  rw [div_le_div_iff_of_pos_right hden]
  have hpow : 0 ≤ ((p : ℝ)⁻¹) ^ γ := by positivity
  linarith

/-- Group a finite double geometric sum according to the maximum exponent.
There are exactly `2 * t + 1` ordered pairs with maximum `t`. -/
lemma fin_double_max_sum_eq_shell (r : ℝ) (γ : ℕ) :
    (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
      if max e₁.1 e₂.1 = 0 then 0 else r ^ max e₁.1 e₂.1) =
      ∑ e : Fin (γ + 1),
        if e.1 = 0 then 0 else ((2 * e.1 + 1 : ℕ) : ℝ) * r ^ e.1 := by
  let splitTerm : Fin (γ + 1) → Fin (γ + 1) → ℝ := fun e₁ e₂ =>
    (if e₁.1 ≠ 0 ∧ e₂ ≤ e₁ then r ^ e₁.1 else 0) +
      (if e₁ < e₂ then r ^ e₂.1 else 0)
  calc
    (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
      if max e₁.1 e₂.1 = 0 then 0 else r ^ max e₁.1 e₂.1) =
        ∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1), splitTerm e₁ e₂ := by
      apply Finset.sum_congr rfl
      intro e₁ he₁
      apply Finset.sum_congr rfl
      intro e₂ he₂
      dsimp only [splitTerm]
      by_cases hle : e₂ ≤ e₁
      · rw [max_eq_left (by exact_mod_cast hle)]
        by_cases hz : e₁.1 = 0
        · have hz₂ : e₂.1 = 0 := by omega
          have heq : e₂ = e₁ := Fin.ext (hz₂.trans hz.symm)
          subst e₂
          simp [hz]
        · simp [hz, hle, not_lt_of_ge hle]
      · have hlt : e₁ < e₂ := lt_of_not_ge hle
        rw [max_eq_right (by exact_mod_cast hlt.le)]
        have hz : e₂.1 ≠ 0 := by omega
        simp [hz, hle, hlt]
    _ = (∑ e₁ : Fin (γ + 1),
          if e₁.1 = 0 then 0 else ((e₁.1 + 1 : ℕ) : ℝ) * r ^ e₁.1) +
        ∑ e₂ : Fin (γ + 1),
          if e₂.1 = 0 then 0 else (e₂.1 : ℝ) * r ^ e₂.1 := by
      simp_rw [splitTerm]
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro e₁ he₁
        by_cases hz : e₁.1 = 0
        · simp [hz]
        · rw [if_neg hz]
          rw [← Finset.sum_filter]
          rw [show (Finset.univ.filter fun e₂ : Fin (γ + 1) =>
              e₁.1 ≠ 0 ∧ e₂ ≤ e₁) = Finset.Iic e₁ by
            ext e₂
            simp [hz]]
          simp [Fin.card_Iic]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e₂ he₂
        by_cases hz : e₂.1 = 0
        · have hleast : ∀ x : Fin (γ + 1), e₂ ≤ x := by
            intro x
            exact_mod_cast (show e₂.1 ≤ x.1 by omega)
          simp [hz, hleast]
        · rw [if_neg hz, ← Finset.sum_filter]
          rw [show (Finset.univ.filter fun e₁ : Fin (γ + 1) => e₁ < e₂) =
              Finset.Iio e₂ by ext e₁; simp]
          simp [Fin.card_Iio]
    _ = ∑ e : Fin (γ + 1),
        if e.1 = 0 then 0 else ((2 * e.1 + 1 : ℕ) : ℝ) * r ^ e.1 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hz : e.1 = 0
      · simp [hz]
      · simp only [hz, if_false]
        push_cast
        ring

/-- The finite double maximum sum is bounded by its infinite geometric
value.  This is the local `(3p-1)/(p-1)^2` term in BBMST. -/
lemma fin_double_max_sum_le (p γ : ℕ) (hp2 : 2 ≤ p) :
    (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
      if max e₁.1 e₂.1 = 0 then 0 else
        1 / ((((p ^ max e₁.1 e₂.1 : ℕ) : ℝ)))) ≤
      (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by positivity
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp2
  have hr0 : 0 ≤ r := inv_nonneg.mpr hpR.le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hp1R
  have hrewrite (n : ℕ) : 1 / ((((p ^ n : ℕ) : ℝ))) = r ^ n := by
    simp only [r, one_div, Nat.cast_pow, inv_pow]
  simp_rw [hrewrite]
  rw [fin_double_max_sum_eq_shell]
  rw [Fin.sum_univ_eq_sum_range (fun e : ℕ =>
    if e = 0 then 0 else ((2 * e + 1 : ℕ) : ℝ) * r ^ e)]
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hw := hasSum_coe_mul_geometric_of_norm_lt_one (r := r) hrnorm
  have hweighted :
      (∑ e ∈ Finset.range (γ + 1), (e : ℝ) * r ^ e) ≤ r / (1 - r) ^ 2 := by
    simpa only [hw.tsum_eq] using
      (hw.summable.sum_le_tsum (Finset.range (γ + 1))
        (fun e he => mul_nonneg (by positivity) (pow_nonneg hr0 e)))
  have htail :
      (∑ e ∈ Finset.range (γ + 1), if e = 0 then 0 else r ^ e) ≤ r / (1 - r) := by
    rw [← Fin.sum_univ_eq_sum_range]
    have hgeom := fin_inv_pow_sum_le p γ hp2
    have hleft :
        (∑ e : Fin (γ + 1), if e.1 = 0 then 0 else r ^ e.1) =
          ∑ e : Fin (γ + 1),
            if e.1 = 0 then 0 else 1 / ((((p ^ e.1 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [hrewrite]
    rw [hleft]
    calc
      _ ≤ 1 / ((p : ℝ) - 1) := hgeom
      _ = r / (1 - r) := by
        dsimp only [r]
        field_simp [ne_of_gt hpR, ne_of_gt (sub_pos.mpr hp1R)]
  calc
    (∑ e ∈ Finset.range (γ + 1),
        if e = 0 then 0 else ((2 * e + 1 : ℕ) : ℝ) * r ^ e) =
      2 * (∑ e ∈ Finset.range (γ + 1), (e : ℝ) * r ^ e) +
        (∑ e ∈ Finset.range (γ + 1), if e = 0 then 0 else r ^ e) := by
          rw [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro e he
          by_cases hz : e = 0
          · simp [hz]
          · simp only [hz, if_false]
            push_cast
            ring
    _ ≤ 2 * (r / (1 - r) ^ 2) + r / (1 - r) :=
      add_le_add (mul_le_mul_of_nonneg_left hweighted (by norm_num)) htail
    _ = (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
      dsimp only [r]
      field_simp [ne_of_gt hpR, ne_of_gt (sub_pos.mpr hp1R)]
      ring

lemma sum_firstLocalFactor_le
    (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1)) :
    (∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
      firstLocalFactor S hi j e) ≤
      if j.1 = i then
        1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)
      else
        1 + (1 - S.delta j.1)⁻¹ *
          (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) := by
  let p := primeAt Q (stageCoordinate Q hi j)
  let γ := Q.factorization p
  have hp2 : 2 ≤ p := (primeAt_prime Q (stageCoordinate Q hi j)).two_le
  have hgeom := fin_inv_pow_sum_le p γ hp2
  by_cases hjlast : j.1 = i
  · simp only [firstLocalFactor, hjlast, if_true]
    exact hgeom
  · rw [if_neg hjlast]
    simp only [firstLocalFactor, hjlast, if_false]
    have hinv : 0 ≤ (1 - S.delta j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])
    calc
      (∑ e : Fin (γ + 1),
        if e.1 = 0 then 1 else
          (1 - S.delta j.1)⁻¹ / (((p ^ e.1 : ℕ) : ℝ))) =
        ∑ e : Fin (γ + 1), ((if e.1 = 0 then 1 else 0) +
            (1 - S.delta j.1)⁻¹ *
              (if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ)))) := by
                apply Finset.sum_congr rfl
                intro e he
                by_cases he0 : e.1 = 0
                · simp [he0]
                · simp [he0, div_eq_mul_inv]
      _ = 1 + (1 - S.delta j.1)⁻¹ *
          (∑ e : Fin (γ + 1),
            if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ))) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              simp
      _ ≤ 1 + (1 - S.delta j.1)⁻¹ *
          (1 / ((p : ℝ) - 1)) := by
            exact add_le_add_right (mul_le_mul_of_nonneg_left hgeom hinv) 1

lemma sum_secondLocalFactor_le
    (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1)) :
    (∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
      ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
        secondLocalFactor S hi j e₁ e₂) ≤
      if j.1 = i then
        (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) ^ 2
      else
        1 + (1 - S.delta j.1)⁻¹ *
          ((3 * (primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) /
            ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) ^ 2) := by
  let p := primeAt Q (stageCoordinate Q hi j)
  let γ := Q.factorization p
  have hp2 : 2 ≤ p := (primeAt_prime Q (stageCoordinate Q hi j)).two_le
  have hgeom := fin_inv_pow_sum_le p γ hp2
  have hdouble := fin_double_max_sum_le p γ hp2
  by_cases hjlast : j.1 = i
  · simp only [secondLocalFactor, hjlast, if_true]
    let f : Fin (γ + 1) → ℝ := fun e =>
      if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ))
    have hrewrite (e₁ e₂ : Fin (γ + 1)) :
        (if e₁.1 = 0 ∨ e₂.1 = 0 then 0 else
          1 / (((p ^ (e₁.1 + e₂.1) : ℕ) : ℝ))) = f e₁ * f e₂ := by
      dsimp only [f]
      by_cases h₁ : e₁.1 = 0
      · simp [h₁]
      · by_cases h₂ : e₂.1 = 0
        · simp [h₂]
        · simp only [h₁, h₂, false_or, if_false]
          push_cast
          rw [pow_add]
          field_simp
    calc
      (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
          if e₁.1 = 0 ∨ e₂.1 = 0 then 0 else
            1 / (((p ^ (e₁.1 + e₂.1) : ℕ) : ℝ))) =
          ∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1), f e₁ * f e₂ := by
        apply Finset.sum_congr rfl
        intro e₁ he₁
        apply Finset.sum_congr rfl
        intro e₂ he₂
        exact hrewrite e₁ e₂
      _ = (∑ e : Fin (γ + 1), f e) * (∑ e : Fin (γ + 1), f e) := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_mul]
      _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 := by
        rw [pow_two]
        exact mul_self_le_mul_self (Finset.sum_nonneg fun e he => by
          dsimp only [f]
          positivity) hgeom
  · rw [if_neg hjlast]
    simp only [secondLocalFactor, hjlast, if_false]
    have hinv : 0 ≤ (1 - S.delta j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])
    let splitTerm : Fin (γ + 1) → Fin (γ + 1) → ℝ := fun e₁ e₂ =>
      (if max e₁.1 e₂.1 = 0 then 1 else 0) +
        (1 - S.delta j.1)⁻¹ *
          (if max e₁.1 e₂.1 = 0 then 0 else
            1 / (((p ^ max e₁.1 e₂.1 : ℕ) : ℝ)))
    have hone :
        (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
          if max e₁.1 e₂.1 = 0 then (1 : ℝ) else 0) = 1 := by
      simp only [max_eq_zero, Fin.val_eq_zero_iff, Finset.sum_boole]
      classical
      rw [Finset.sum_eq_single 0]
      · norm_cast
        rw [Finset.card_eq_one]
        exact ⟨0, by ext e; simp⟩
      · intro e he_mem he_ne
        simp [he_ne]
      · simp
    calc
      (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
        if max e₁.1 e₂.1 = 0 then 1 else
          (1 - S.delta j.1)⁻¹ / (((p ^ max e₁.1 e₂.1 : ℕ) : ℝ))) =
        ∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1), splitTerm e₁ e₂ := by
        apply Finset.sum_congr rfl
        intro e₁ he₁
        apply Finset.sum_congr rfl
        intro e₂ he₂
        dsimp only [splitTerm]
        by_cases hz : max e₁.1 e₂.1 = 0
        · simp [hz]
        · simp [hz, div_eq_mul_inv]
      _ = 1 + (1 - S.delta j.1)⁻¹ *
          (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
            if max e₁.1 e₂.1 = 0 then 0 else
              1 / (((p ^ max e₁.1 e₂.1 : ℕ) : ℝ))) := by
        simp_rw [splitTerm]
        simp_rw [Finset.sum_add_distrib]
        rw [hone]
        simp_rw [← Finset.mul_sum]
      _ ≤ 1 + (1 - S.delta j.1)⁻¹ *
          ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hdouble hinv) 1

lemma sum_stage_first_products_le_standard
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d ∈ stageIndices Q D i,
      stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
  calc
    (∑ d ∈ stageIndices Q D i,
      stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          firstLocalFactor S hi j e :=
        sum_stage_first_products_le_euler S D hQ hd hdQ hi
    _ ≤ ∏ j : Fin (i + 1),
        if j.1 = i then
          1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)
        else
          1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact Finset.sum_nonneg fun e he => firstLocalFactor_nonneg S hi j e
      · intro j hj
        exact sum_firstLocalFactor_le S hi j
    _ = (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_last, if_true, stageCoordinate]
      rw [mul_comm]
      congr 1
      apply Fintype.prod_congr
      intro j
      simp only [Fin.val_castSucc, Nat.ne_of_lt j.2, if_false]

lemma sum_stage_second_products_le_standard
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
  calc
    (∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
            secondLocalFactor S hi j e₁ e₂ :=
      sum_stage_second_products_le_euler S D hQ hd hdQ hi
    _ ≤ ∏ j : Fin (i + 1),
        if j.1 = i then
          (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) ^ 2
        else
          1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) /
              ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) ^ 2) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact Finset.sum_nonneg fun e₁ he₁ =>
          Finset.sum_nonneg fun e₂ he₂ => secondLocalFactor_nonneg S hi j e₁ e₂
      · intro j hj
        exact sum_secondLocalFactor_le S hi j
    _ = (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_last, if_true, stageCoordinate]
      rw [mul_comm]
      congr 1
      apply Fintype.prod_congr
      intro j
      simp only [Fin.val_castSucc, Nat.ne_of_lt j.2, if_false]

lemma firstMoment_stageBad_le_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  exact (firstMoment_stageBad_le_products Q D a hQ hd hdQ delta hdelta0 hdelta1 hi).trans
    (sum_stage_first_products_le_standard S D hQ hd hdQ hi)

lemma secondMoment_stageBad_le_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  exact (secondMoment_stageBad_le_products Q D a hQ hd hdQ delta hdelta0 hdelta1 hi).trans
    (sum_stage_second_products_le_standard S D hQ hd hdQ hi)

lemma stageCost_le_first_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.stageCost S i ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.stageCost S i ≤
        Distortion.firstMoment (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) := by
      simpa only [Distortion.stageCost, Distortion.prefixProb_succ, S,
        arithmeticSchedule] using
        (Distortion.step_mass_bad_le_first (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) (hdelta0 i) (hdelta1 i))
    _ ≤ _ := firstMoment_stageBad_le_standard Q D a hQ hd hdQ delta hdelta0 hdelta1 hi

lemma stageCost_le_second_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q)
    (hdi : 0 < delta i) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.stageCost S i ≤
      ((1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) /
        (4 * delta i * (1 - delta i)) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.stageCost S i ≤
        Distortion.secondMoment (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) / (4 * delta i * (1 - delta i)) := by
      simpa only [Distortion.stageCost, Distortion.prefixProb_succ, S,
        arithmeticSchedule] using
        (Distortion.step_mass_bad_le_second (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) hdi (hdelta1 i))
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right
      · exact secondMoment_stageBad_le_standard Q D a hQ hd hdQ delta hdelta0 hdelta1 hi
      · exact mul_nonneg (mul_nonneg (by norm_num) hdi.le)
          (sub_nonneg.mpr (hdelta1 i).le)

/-- Reconstruct a divisor of `Q` from its exponents on the enumerated prime
coordinates of `Q`. -/
lemma prod_primeAt_pow_factorization_eq
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) :
    (∏ j : Fin (primeCount Q),
      primeAt Q j ^ d.factorization (primeAt Q j)) = d := by
  calc
    (∏ j : Fin (primeCount Q),
      primeAt Q j ^ d.factorization (primeAt Q j)) =
        ∏ p : PrimeIndex Q, p.1 ^ d.factorization p.1 := by
      apply Fintype.prod_equiv (primeEnum Q).toEquiv
      intro j
      rfl
    _ = ∏ p ∈ Q.primeFactors, p ^ d.factorization p := by
      exact
        Finset.prod_attach Q.primeFactors
          (fun p : ℕ => p ^ d.factorization p)
    _ = ∏ p ∈ d.primeFactors, p ^ d.factorization p := by
      symm
      apply Finset.prod_subset (Nat.primeFactors_mono hdQ hQ)
      intro p hpQ hpd
      have hpprime := Nat.prime_of_mem_primeFactors hpQ
      have hpnd : ¬p ∣ d := by
        intro hpdvd
        exact hpd (hpprime.mem_primeFactors hpdvd hd)
      rw [Nat.factorization_eq_zero_of_not_dvd hpnd, pow_zero]
    _ = d := (Nat.prod_primeFactors_pow_factorization hd).symm

/-- If `d` is assigned to stage `i`, its prime factorization is already
contained in the prefix through the `i`-th prime coordinate. -/
lemma prod_stage_prime_powers_eq
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) (ha : assignedAt Q d i) :
    (∏ j : Fin (i + 1),
      primeAt Q (stageCoordinate Q hi j) ^
        d.factorization (primeAt Q (stageCoordinate Q hi j))) = d := by
  let e : Fin (i + 1) ↪ Fin (primeCount Q) :=
    Fin.castLEEmb (Nat.succ_le_of_lt hi)
  let s : Finset (Fin (primeCount Q)) := Finset.univ.map e
  have hprefix :
      (∏ j : Fin (i + 1),
        primeAt Q (stageCoordinate Q hi j) ^
          d.factorization (primeAt Q (stageCoordinate Q hi j))) =
        ∏ j ∈ s, primeAt Q j ^ d.factorization (primeAt Q j) := by
    change (∏ j : Fin (i + 1),
        primeAt Q (stageCoordinate Q hi j) ^
          d.factorization (primeAt Q (stageCoordinate Q hi j))) =
      ∏ j ∈ Finset.univ.map e, primeAt Q j ^ d.factorization (primeAt Q j)
    rw [Finset.prod_map]
    rfl
  rw [hprefix]
  calc
    (∏ j ∈ s, primeAt Q j ^ d.factorization (primeAt Q j)) =
        ∏ j : Fin (primeCount Q),
          primeAt Q j ^ d.factorization (primeAt Q j) := by
      apply Finset.prod_subset (Finset.subset_univ s)
      intro j hjuniv hjnot
      have hjgt : i < j.1 := by
        by_contra hnot
        have hjle : j.1 ≤ i := Nat.le_of_not_gt hnot
        let k : Fin (i + 1) := ⟨j.1, Nat.lt_succ_iff.mpr hjle⟩
        have heq : e k = j := Fin.ext rfl
        apply hjnot
        exact Finset.mem_map.mpr ⟨k, Finset.mem_univ _, heq⟩
      have hz := ((assignedAt_iff_of_lt Q d hi).mp ha).2 j.1 hjgt j.2
      rw [hz, pow_zero]
    _ = d := prod_primeAt_pow_factorization_eq Q d hQ hd hdQ

/-- A modulus assigned at a prime below `K` is `K`-smooth. -/
lemma mem_smoothNumbers_of_assignedAt
    (Q d K : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) (ha : assignedAt Q d i)
    (hpK : primeAt Q ⟨i, hi⟩ < K) :
    d ∈ K.smoothNumbers := by
  rw [Nat.mem_smoothNumbers_iff_primeFactors_subset]
  refine ⟨hd, ?_⟩
  intro p hpd
  have hpQ : p ∈ Q.primeFactors := Nat.primeFactors_mono hdQ hQ hpd
  let k : Fin (primeCount Q) := (primeEnum Q).symm ⟨p, hpQ⟩
  have hpk : primeAt Q k = p := primeAt_primeEnum_symm Q ⟨p, hpQ⟩
  have hki : k.1 ≤ i := by
    by_contra hnot
    have hik : i < k.1 := Nat.lt_of_not_ge hnot
    have hz := ((assignedAt_iff_of_lt Q d hi).mp ha).2 k.1 hik k.2
    have hpos : d.factorization p ≠ 0 :=
      (Nat.prime_of_mem_primeFactors hpd).factorization_pos_of_dvd hd
        (Nat.dvd_of_mem_primeFactors hpd) |>.ne'
    exact hpos (by simpa only [hpk] using hz)
  have hple : p ≤ primeAt Q ⟨i, hi⟩ := by
    rw [← hpk]
    exact (primeAt_strictMono Q).monotone hki
  exact Nat.mem_primesBelow.mpr
    ⟨hple.trans_lt hpK, Nat.prime_of_mem_primeFactors hpd⟩

/-! ### From surviving prefixes back to congruence classes -/

lemma castHom_castHom {k m n : ℕ} (hkm : k ∣ m) (hmn : m ∣ n)
    (x : ZMod n) :
    ZMod.castHom hkm (ZMod k) (ZMod.castHom hmn (ZMod m) x) =
      ZMod.castHom (hkm.trans hmn) (ZMod k) x := by
  exact RingHom.congr_fun (Subsingleton.elim
    ((ZMod.castHom hkm (ZMod k)).comp (ZMod.castHom hmn (ZMod m)))
    (ZMod.castHom (hkm.trans hmn) (ZMod k))) x

/-- Each component of the prime-power CRT equivalence is the canonical
reduction map. -/
lemma equivPi_apply_eq_castHom
    (Q : ℕ) (hQ : Q ≠ 0) (x : ZMod Q) (p : PrimeIndex Q) :
    ZMod.equivPi (n := Q) hQ x p =
      ZMod.castHom
        ((Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hQ |>.2 le_rfl)
        (ZMod (p.1 ^ Q.factorization p.1)) x := by
  exact RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom
      (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1)) p).comp
        (ZMod.equivPi (n := Q) hQ).toRingHom)
    (ZMod.castHom
      ((Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hQ |>.2 le_rfl)
      (ZMod (p.1 ^ Q.factorization p.1)))) x

/-- Applying CRT to a full prefix recovers the corresponding transported
prime-power coordinate. -/
lemma equivPi_prefixCRTEq_apply
    (Q : ℕ) (hQ : Q ≠ 0)
    (x : Distortion.Prefix (primePowerSize Q) (primeCount Q))
    (i : Fin (primeCount Q)) :
    ZMod.equivPi (n := Q) hQ (prefixCRTEq Q hQ x) (primeEnum Q i) =
      finPrimePowerEquiv Q i
        (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q) x i) := by
  let v : (j : Fin (primeCount Q)) →
      ZMod (((primeEnum Q j).1) ^ Q.factorization (primeEnum Q j).1) :=
    fun j => by
      simpa only [primeAt] using finPrimePowerEquiv Q j
        (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q) x j)
  let w : (p : PrimeIndex Q) → ZMod (p.1 ^ Q.factorization p.1) :=
    Equiv.piCongrLeft
      (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
      (primeEnum Q).toEquiv v
  have hx : prefixCRTEq Q hQ x =
      (ZMod.equivPi (n := Q) hQ).symm w := rfl
  rw [hx, (ZMod.equivPi (n := Q) hQ).apply_symm_apply]
  dsimp only [w]
  change (Equiv.piCongrLeft
      (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
      (primeEnum Q).toEquiv v) (primeEnum Q i) = v i
  exact Equiv.piCongrLeft_apply_apply
    (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
    (primeEnum Q).toEquiv v i

/-- One coordinate restriction means precisely reduction to `b` modulo the
corresponding prime power of `d`. -/
lemma mem_classCoordinates_iff_cast
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (i : Fin (primeCount Q))
    (x : Distortion.Coordinate (primePowerSize Q i.1)) :
    x ∈ classCoordinates Q d hQ hd hdQ b i.1 ↔
      ZMod.castHom
        (pow_dvd_pow (primeAt Q i)
          ((Nat.factorization_le_iff_dvd hd hQ).mpr hdQ (primeAt Q i)))
        (ZMod ((primeAt Q i) ^ d.factorization (primeAt Q i)))
        (finPrimePowerEquiv Q i x) =
      (b : ZMod ((primeAt Q i) ^ d.factorization (primeAt Q i))) := by
  by_cases he : d.factorization (primeAt Q i) = 0
  · constructor
    · intro _
      haveI : Subsingleton (ZMod ((primeAt Q i) ^ d.factorization (primeAt Q i))) := by
        rw [he, pow_zero]
        infer_instance
      exact Subsingleton.elim _ _
    · intro _
      simp [classCoordinates, primeRestriction, i.isLt, he]
  · have hcast :
        (Equiv.cast (congrArg Fin (primePowerSize_of_lt Q i.isLt).symm)).symm x =
          Equiv.cast (congrArg Fin (primePowerSize_of_lt Q i.isLt)) x := by
      rfl
    simp [classCoordinates, primeRestriction, finPrimePowerEquiv, i.isLt, he, hcast]

/-- A full prefix belongs to a congruence-class box whenever its CRT residue
reduces to that class modulo `d`. -/
lemma mem_classBox_of_cast_eq
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (x : Distortion.Prefix (primePowerSize Q) (primeCount Q))
    (hx : ZMod.castHom hdQ (ZMod d) (prefixCRTEq Q hQ x) = (b : ZMod d)) :
    x ∈ classBox Q d hQ hd hdQ b (primeCount Q) := by
  rw [classBox, Distortion.mem_box_iff_mem_coordinate]
  intro i
  rw [mem_classCoordinates_iff_cast Q d hQ hd hdQ b i]
  let p := primeAt Q i
  let γ := Q.factorization p
  let e := d.factorization p
  have hp : p.Prime := primeAt_prime Q i
  have heγ : e ≤ γ := (Nat.factorization_le_iff_dvd hd hQ).mpr hdQ p
  have hpeD : p ^ e ∣ d := (hp.pow_dvd_iff_le_factorization hd).2 le_rfl
  have hpγQ : p ^ γ ∣ Q := (hp.pow_dvd_iff_le_factorization hQ).2 le_rfl
  have hpeQ : p ^ e ∣ Q := hpeD.trans hdQ
  have hcoord := equivPi_prefixCRTEq_apply Q hQ x i
  have hproj := equivPi_apply_eq_castHom Q hQ (prefixCRTEq Q hQ x) (primeEnum Q i)
  have hfrom := congrArg (fun y : ZMod d => ZMod.castHom hpeD (ZMod (p ^ e)) y) hx
  have hleft :
      ZMod.castHom (pow_dvd_pow p heγ) (ZMod (p ^ e))
          (finPrimePowerEquiv Q i
            (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q) x i)) =
        ZMod.castHom hpeQ (ZMod (p ^ e)) (prefixCRTEq Q hQ x) := by
    rw [← hcoord, hproj]
    exact castHom_castHom (pow_dvd_pow p heγ) hpγQ _
  rw [hleft]
  rw [← castHom_castHom hpeD hdQ (prefixCRTEq Q hQ x)]
  simpa using hfrom

/-- Every divisor `d > 1` of `Q` is assigned to the coordinate of its
largest prime factor. -/
lemma exists_assignedAt
    (Q d : ℕ) (hQ : Q ≠ 0) (hdQ : d ∣ Q) (hd2 : 2 ≤ d) :
    ∃ i < primeCount Q, assignedAt Q d i := by
  have hd0 : d ≠ 0 := by omega
  have hpf : d.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let p := d.primeFactors.max' hpf
  have hpD : p ∈ d.primeFactors := Finset.max'_mem d.primeFactors hpf
  have hpQ : p ∈ Q.primeFactors := Nat.primeFactors_mono hdQ hQ hpD
  let k : Fin (primeCount Q) := (primeEnum Q).symm ⟨p, hpQ⟩
  refine ⟨k.1, k.2, (assignedAt_iff_of_lt Q d k.2).mpr ?_⟩
  have hpk : primeAt Q k = p := primeAt_primeEnum_symm Q ⟨p, hpQ⟩
  constructor
  · rw [hpk]
    exact (Nat.prime_of_mem_primeFactors hpD).factorization_pos_of_dvd hd0
      (Nat.dvd_of_mem_primeFactors hpD) |>.ne'
  · intro j hkj hj
    by_contra hfac
    have hpj : (primeAt Q ⟨j, hj⟩).Prime := primeAt_prime Q ⟨j, hj⟩
    have hpjd : primeAt Q ⟨j, hj⟩ ∣ d := by
      exact (hpj.dvd_iff_one_le_factorization hd0).2
        (Nat.one_le_iff_ne_zero.mpr hfac)
    have hpjD : primeAt Q ⟨j, hj⟩ ∈ d.primeFactors :=
      hpj.mem_primeFactors hpjd hd0
    have hjle : primeAt Q ⟨j, hj⟩ ≤ p := Finset.le_max' d.primeFactors _ hpjD
    have hp_lt : p < primeAt Q ⟨j, hj⟩ := by
      rw [← hpk]
      exact primeAt_strictMono Q hkj
    omega

/-- A residue surviving through stage `n` lies outside every congruence box
assigned before that stage. -/
lemma residual_not_mem_assigned_classBox
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    ∀ (n : ℕ) (x : Distortion.Prefix (primePowerSize Q) n),
      x ∈ Distortion.residual S n →
      ∀ (d : ModulusIndex D) (i : ℕ), i < n → assignedAt Q d.1 i →
        x ∉ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) n := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  intro n
  induction n with
  | zero =>
      intro x hx d i hi
      omega
  | succ n ih =>
      intro z hz d i hi ha hclass
      rcases z with ⟨x, y⟩
      have hzparts :
          x ∈ Distortion.residual S n ∧ y ∉ S.bad n x := by
        change (x, y) ∈ Distortion.oldPairs (Distortion.residual S n) \
          Distortion.badPairs (S.bad n) at hz
        have hraw := Finset.mem_sdiff.mp hz
        have hold := Finset.mem_product.mp hraw.1
        refine ⟨hold.1, ?_⟩
        intro hy
        apply hraw.2
        exact (Distortion.mem_badPairs_iff (S.bad n) x y).mpr hy
      rw [classBox, Distortion.box_succ] at hclass
      have hclassparts := Finset.mem_product.mp hclass
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hin | heq
      · exact ih x hzparts.1 d i hin ha hclassparts.1
      · subst i
        apply hzparts.2
        change y ∈ stageBad Q D a hQ hd hdQ n x
        rw [stageBad]
        apply Finset.mem_biUnion.mpr
        refine ⟨d, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ d, ha⟩
        · have hxclass :
              x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) n :=
            hclassparts.1
          rw [classSection, if_pos hxclass]
          exact hclassparts.2

end Arithmetic

/-! ## Analytic bounds for the large-prime tail -/

namespace Analytic

open Filter Asymptotics

/-- The local second-moment Euler factor is bounded by a coarse exponential
majorant.  The constant `20` is chosen so that the estimate also covers the
small prime `2`. -/
lemma second_factor_le_exp (p : ℕ) (hp : 2 ≤ p) :
    1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) ≤
      Real.exp (20 / (p : ℝ)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hrat :
      2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) ≤
        20 / (p : ℝ) := by
    rw [show 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) =
      (2 * (3 * (p : ℝ) - 1)) / ((p : ℝ) - 1) ^ 2 by ring]
    rw [div_le_div_iff₀ (sq_pos_of_pos hp1) hp0]
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  calc
    1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) ≤
        1 + 20 / (p : ℝ) := by linarith
    _ ≤ Real.exp (20 / (p : ℝ)) := by
      simpa [add_comm] using Real.add_one_le_exp (20 / (p : ℝ))

/-- The full prime Euler product which majorizes the earlier-coordinate
second-moment factors. -/
def secondEulerProduct (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y,
    (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2))

/-- The earlier prime divisors of `Q` form a subset of all primes up to the
current prime, so their local factors are bounded by the full Euler product. -/
lemma prior_second_factors_le_euler
    (Q : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q) :
    (∏ j : Fin i,
      (1 + 2 *
        ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) ≤
      secondEulerProduct (Arithmetic.primeAt Q ⟨i, hi⟩) := by
  let e : Fin i ↪ ℕ :=
    ⟨fun j => Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩,
      fun j k hjk => by
        have heq : (⟨j.1, j.2.trans hi⟩ : Fin (Arithmetic.primeCount Q)) =
            ⟨k.1, k.2.trans hi⟩ :=
          (Arithmetic.primeAt_strictMono Q).injective hjk
        have hval : j.1 = k.1 :=
          congrArg (fun x : Fin (Arithmetic.primeCount Q) => x.1) heq
        exact Fin.ext hval⟩
  let s : Finset ℕ := Finset.univ.map e
  have hprod :
      (∏ j : Fin i,
        (1 + 2 *
          ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
            ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) =
        ∏ p ∈ s, (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) := by
    change (∏ j : Fin i,
        (1 + 2 *
          ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
            ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) =
      ∏ p ∈ Finset.univ.map e,
        (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2))
    rw [Finset.prod_map]
    rfl
  rw [hprod]
  unfold secondEulerProduct
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hp' := Finset.mem_map.mp hp
    obtain ⟨j, hj, rfl⟩ := hp'
    exact Nat.mem_primesLE.mpr ⟨by
      have hlt : (⟨j.1, j.2.trans hi⟩ : Fin (Arithmetic.primeCount Q)) < ⟨i, hi⟩ :=
        j.2
      exact ((Arithmetic.primeAt_strictMono Q) hlt).le,
      Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hp
    have hp2 : (2 : ℝ) ≤ e j := by
      exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
    have hrat : 0 ≤ (3 * (e j : ℝ) - 1) / ((e j : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    linarith
  · intro p hp hpnot
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    have hrat : 0 ≤ (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    linarith

lemma secondEulerProduct_le_exp_primeSum (y : ℕ) :
    secondEulerProduct y ≤
      Real.exp (20 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
  unfold secondEulerProduct
  calc
    ∏ p ∈ Nat.primesLE y,
        (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) ≤
      ∏ p ∈ Nat.primesLE y, Real.exp (20 / (p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by
            exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
          have hrat : 0 ≤ (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 :=
            div_nonneg (by linarith) (sq_nonneg _)
          linarith
        · intro p hp
          exact second_factor_le_exp p (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    _ = Real.exp (∑ p ∈ Nat.primesLE y, 20 / (p : ℝ)) := by
      rw [Real.exp_sum]
    _ = Real.exp (20 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Mertens' estimate turns the local-factor product into a fixed power of
`log y`. -/
theorem exists_secondEulerProduct_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20 := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 Erdos448.eventually_prime_reciprocal_sum_le_loglog_add_one
  let S : ℝ := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  let C₀ : ℝ := |meissel_mertens| + 1 + S + |Real.log (Real.log 3)|
  refine ⟨Real.exp (20 * C₀), Real.exp_pos _, ?_⟩
  intro y hy
  have hsumUpper :
      (∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.log (Real.log (y : ℝ)) + C₀ := by
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun p _ ↦ div_nonneg zero_le_one (Nat.cast_nonneg p)
    by_cases hNy : N ≤ y
    · have h := hN y hNy
      have hsumId :
          (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (p : ℝ)⁻¹) =
            ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p := by
        apply Finset.sum_congr
        · ext p
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
          constructor
          · rintro ⟨⟨_, hpy⟩, hp⟩
            exact ⟨hpy, hp⟩
          · rintro ⟨hpy, hp⟩
            exact ⟨⟨hp.pos, hpy⟩, hp⟩
        · intro p _
          exact (one_div (p : ℝ)).symm
      rw [hsumId] at h
      dsimp [C₀]
      linarith [le_abs_self meissel_mertens, abs_nonneg (Real.log (Real.log 3))]
    · have hyN : y ≤ N := (Nat.lt_of_not_ge hNy).le
      have hmono : (∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤ S := by
        dsimp [S]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.mpr
            ⟨(Nat.mem_primesLE.mp hp).1.trans hyN, (Nat.mem_primesLE.mp hp).2⟩
        · intro p _ _
          exact div_nonneg zero_le_one (Nat.cast_nonneg p)
      have hlog : Real.log (Real.log (3 : ℝ)) ≤ Real.log (Real.log (y : ℝ)) := by
        apply Real.log_le_log
        · exact Real.log_pos (by norm_num)
        · apply Real.log_le_log (by norm_num)
          exact_mod_cast hy
      dsimp [C₀]
      linarith [abs_nonneg meissel_mertens,
        neg_le_of_abs_le (le_rfl : |Real.log (Real.log 3)| ≤ |Real.log (Real.log 3)|)]
  apply (secondEulerProduct_le_exp_primeSum y).trans
  calc
    Real.exp (20 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.exp (20 * (Real.log (Real.log (y : ℝ)) + C₀)) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsumUpper (by norm_num))
    _ = Real.exp (20 * C₀) * Real.log (y : ℝ) ^ 20 := by
      have hlog : 0 < Real.log (y : ℝ) := by
        exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      rw [show 20 * (Real.log (Real.log (y : ℝ)) + C₀) =
          20 * C₀ + Real.log (Real.log (y : ℝ)) * 20 by ring,
        Real.exp_add]
      congr 1
      calc
        Real.exp (Real.log (Real.log (y : ℝ)) * 20) =
            Real.exp ((20 : ℕ) * Real.log (Real.log (y : ℝ))) := by
          congr 1
          norm_num
          ring
        _ = Real.exp (Real.log (Real.log (y : ℝ))) ^ 20 :=
          Real.exp_nat_mul _ _
        _ = Real.log (y : ℝ) ^ 20 := by rw [Real.exp_log hlog]

/-- The integer majorant for the large-prime stage costs is summable. -/
lemma summable_log_pow_twenty_div_sq :
    Summable (fun n : ℕ => Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2) := by
  have hlo :
      (fun x : ℝ => Real.log x ^ (20 : ℝ)) =o[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    exact isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) (20 : ℝ) (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2 ≤
        1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    have hbound := (hlo.comp_tendsto tendsto_natCast_atTop_atTop).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hbound, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn hn2
    have hn' : Real.log (n : ℝ) ^ (20 : ℝ) ≤
        (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        Real.log (n : ℝ) ^ (20 : ℝ) ≤
            |Real.log (n : ℝ) ^ (20 : ℝ)| := le_abs_self _
        _ ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := by
          simpa only [Function.comp_apply, one_mul, Real.norm_eq_abs] using hn
        _ = (n : ℝ) ^ (1 / 2 : ℝ) :=
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hnNat : Real.log (n : ℝ) ^ (20 : ℕ) ≤
        (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact hn'
    have hnpos : (0 : ℝ) < n := by positivity
    calc
      Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2 ≤
          (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnNat (sq_nonneg _)
      _ = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
        rw [show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by
          norm_num [Real.rpow_two]]
        rw [← Real.rpow_sub hnpos]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have hO :
      (fun n : ℕ => Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2) =O[atTop]
        (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hevent, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn hn2
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hn
  exact summable_of_isBigO_nat
    (Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 3 / 2))
    hO

/-! ### A two-level distortion schedule and its large-stage bound -/

/-- The small-prime coordinates are left uniform, while all later coordinates
use distortion parameter `1/2`. -/
def tailDelta (k i : ℕ) : ℝ := if i < k then 0 else 1 / 2

lemma tailDelta_nonneg (k i : ℕ) : 0 ≤ tailDelta k i := by
  unfold tailDelta
  split_ifs <;> norm_num

lemma tailDelta_lt_one (k i : ℕ) : tailDelta k i < 1 := by
  unfold tailDelta
  split_ifs <;> norm_num

lemma tailDelta_eq_half {k i : ℕ} (hki : k ≤ i) :
    tailDelta k i = 1 / 2 := by
  simp [tailDelta, Nat.not_lt.mpr hki]

lemma prior_schedule_factors_le_euler
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (k : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (tailDelta k)
      (tailDelta_nonneg k) (tailDelta_lt_one k)
    (∏ j : Fin i,
      (1 + (1 - S.delta j.1)⁻¹ *
        ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) ≤
      secondEulerProduct (Arithmetic.primeAt Q ⟨i, hi⟩) := by
  dsimp only [Arithmetic.arithmeticSchedule]
  apply (Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)).trans
    (prior_second_factors_le_euler Q hi)
  · have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
      exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
    have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    have hinv : 0 ≤ (1 - tailDelta k j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [tailDelta_lt_one k j.1])
    positivity
  · have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
      exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
    have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    have hinv : (1 - tailDelta k j.1)⁻¹ ≤ 2 := by
      rw [tailDelta]
      split_ifs <;> norm_num
    have hmul := mul_le_mul_of_nonneg_right hinv hrat
    linarith

lemma reciprocal_sub_one_sq_le_four_div_sq (p : ℕ) (hp : 2 ≤ p) :
    (1 / ((p : ℝ) - 1)) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_pow, one_pow, div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hp0)]
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

/-- Every stage at or above the cutoff is bounded by the common summable
majorant supplied by the Mertens Euler-product estimate. -/
lemma large_stage_cost_le
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {k i : ℕ} (hk : 1 ≤ k) (hki : k ≤ i) (hi : i < Arithmetic.primeCount Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (tailDelta k)
      (tailDelta_nonneg k) (tailDelta_lt_one k)
    Distortion.stageCost S i ≤
      4 * C * Real.log (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 20 /
        (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 2 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (tailDelta k)
      (tailDelta_nonneg k) (tailDelta_lt_one k)
  let p := Arithmetic.primeAt Q ⟨i, hi⟩
  have hdi : 0 < tailDelta k i := by rw [tailDelta_eq_half hki]; norm_num
  have hpprime := Arithmetic.primeAt_prime Q ⟨i, hi⟩
  have hp3 : 3 ≤ p := by
    have hpc : 0 < Arithmetic.primeCount Q := by omega
    let z : Fin (Arithmetic.primeCount Q) := ⟨0, hpc⟩
    have hzero : z < ⟨i, hi⟩ := by
      exact (show 0 < i by omega)
    have hpgt := Arithmetic.primeAt_strictMono Q hzero
    have hp0 := (Arithmetic.primeAt_prime Q z).two_le
    omega
  calc
    Distortion.stageCost S i ≤
      ((1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) /
        (4 * tailDelta k i * (1 - tailDelta k i)) := by
      exact Arithmetic.stageCost_le_second_standard Q D a hQ hd hdQ
        (tailDelta k) (tailDelta_nonneg k) (tailDelta_lt_one k) hi hdi
    _ = (1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
      rw [tailDelta_eq_half hki]
      norm_num
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 * secondEulerProduct p := by
      apply mul_le_mul_of_nonneg_left
      · exact prior_schedule_factors_le_euler Q D a hQ hd hdQ k hi
      · positivity
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 *
        (C * Real.log (p : ℝ) ^ 20) := by
      apply mul_le_mul_of_nonneg_left (hC p hp3)
      positivity
    _ ≤ (4 / (p : ℝ) ^ 2) * (C * Real.log (p : ℝ) ^ 20) := by
      apply mul_le_mul_of_nonneg_right
      · exact reciprocal_sub_one_sq_le_four_div_sq p hpprime.two_le
      · exact mul_nonneg hC0 (by positivity)
    _ = 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := by ring

/-! A prime-value cutoff is more convenient for summing the large-prime tail
and identifying the complementary smooth moduli. -/

def primeTailDelta (Q K i : ℕ) : ℝ :=
  if hi : i < Arithmetic.primeCount Q then
    if Arithmetic.primeAt Q ⟨i, hi⟩ < K then 0 else 1 / 2
  else 0

lemma primeTailDelta_nonneg (Q K i : ℕ) : 0 ≤ primeTailDelta Q K i := by
  unfold primeTailDelta
  split_ifs <;> norm_num

lemma primeTailDelta_lt_one (Q K i : ℕ) : primeTailDelta Q K i < 1 := by
  unfold primeTailDelta
  split_ifs <;> norm_num

lemma primeTailDelta_eq_half (Q K : ℕ) {i : ℕ}
    (hi : i < Arithmetic.primeCount Q)
    (hK : K ≤ Arithmetic.primeAt Q ⟨i, hi⟩) :
    primeTailDelta Q K i = 1 / 2 := by
  simp [primeTailDelta, hi, Nat.not_lt.mpr hK]

lemma primeTailDelta_inv_le_two (Q K i : ℕ) :
    (1 - primeTailDelta Q K i)⁻¹ ≤ (2 : ℝ) := by
  unfold primeTailDelta
  split_ifs <;> norm_num

lemma prior_prime_schedule_factors_le_euler
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∏ j : Fin i,
      (1 + (1 - S.delta j.1)⁻¹ *
        ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) ≤
      secondEulerProduct (Arithmetic.primeAt Q ⟨i, hi⟩) := by
  dsimp only [Arithmetic.arithmeticSchedule]
  apply (Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)).trans
    (prior_second_factors_le_euler Q hi)
  · have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 := by
      have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
        exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
      exact div_nonneg (by linarith) (sq_nonneg _)
    have hinv : 0 ≤ (1 - primeTailDelta Q K j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [primeTailDelta_lt_one Q K j.1])
    positivity
  · have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 := by
      have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
        exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
      exact div_nonneg (by linarith) (sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right
      (primeTailDelta_inv_le_two Q K j.1) hrat
    linarith

/-- A stage whose current prime is at least the prime-value cutoff has a cost
bounded by the common summable integer majorant. -/
lemma large_prime_stage_cost_le
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {K i : ℕ} (hK3 : 3 ≤ K) (hi : i < Arithmetic.primeCount Q)
    (hKp : K ≤ Arithmetic.primeAt Q ⟨i, hi⟩) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Distortion.stageCost S i ≤
      4 * C * Real.log (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 20 /
        (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 2 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  let p := Arithmetic.primeAt Q ⟨i, hi⟩
  have hdi : 0 < primeTailDelta Q K i := by
    rw [primeTailDelta_eq_half Q K hi hKp]
    norm_num
  have hpprime := Arithmetic.primeAt_prime Q ⟨i, hi⟩
  have hp3 : 3 ≤ p := hK3.trans hKp
  calc
    Distortion.stageCost S i ≤
      ((1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) /
        (4 * primeTailDelta Q K i * (1 - primeTailDelta Q K i)) := by
      exact Arithmetic.stageCost_le_second_standard Q D a hQ hd hdQ
        (primeTailDelta Q K) (primeTailDelta_nonneg Q K)
        (primeTailDelta_lt_one Q K) hi hdi
    _ = (1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
      rw [primeTailDelta_eq_half Q K hi hKp]
      norm_num
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 * secondEulerProduct p := by
      exact mul_le_mul_of_nonneg_left
        (prior_prime_schedule_factors_le_euler Q D a hQ hd hdQ K hi) (by positivity)
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 *
        (C * Real.log (p : ℝ) ^ 20) := by
      exact mul_le_mul_of_nonneg_left (hC p hp3) (by positivity)
    _ ≤ (4 / (p : ℝ) ^ 2) * (C * Real.log (p : ℝ) ^ 20) := by
      exact mul_le_mul_of_nonneg_right
        (reciprocal_sub_one_sq_le_four_div_sq p hpprime.two_le)
        (mul_nonneg hC0 (by positivity))
    _ = 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := by ring

lemma summable_large_majorant (C : ℝ) :
    Summable (fun n : ℕ =>
      4 * C * Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2) := by
  simpa only [mul_div_assoc] using
    summable_log_pow_twenty_div_sq.mul_left (4 * C)

/-- There is a numerical prime cutoff above which the total majorant of any
finite collection of stages is less than `1/2`. -/
lemma exists_large_prime_cutoff (C : ℝ) (hC0 : 0 ≤ C) :
    ∃ K : ℕ, 3 ≤ K ∧ ∀ P : Finset ℕ,
      (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2 := by
  let f : ℕ → ℝ := fun n =>
    4 * C * Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2
  have hf : Summable f := summable_large_majorant C
  obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp hf) (1 / 2) (by norm_num)
  let K := max 3 (s.sup id + 1)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro P hP
  have hdisj : Disjoint P s := Finset.disjoint_left.mpr (by
    intro p hpP hps
    have hple : p ≤ s.sup id := Finset.le_sup (f := id) hps
    have hKle : s.sup id + 1 ≤ K := le_max_right _ _
    have hKp := hP p hpP
    omega)
  have hnorm := hs P hdisj
  have hnonneg : 0 ≤ ∑ p ∈ P, f p := by
    apply Finset.sum_nonneg
    intro p hp
    dsimp only [f]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) (by positivity))
      (sq_nonneg _)
  change (∑ p ∈ P, f p) < 1 / 2
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm

/-! ## Summing the small-prime and large-prime stages -/

/-- The completely multiplicative reciprocal map used in the Euler product
for smooth numbers. -/
def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by
    change (((a * b : ℕ) : ℝ))⁻¹ = (a : ℝ)⁻¹ * (b : ℝ)⁻¹
    rw [Nat.cast_mul, mul_inv]

/-- The reciprocals of the positive integers all of whose prime factors are
below a fixed cutoff form a summable family. -/
lemma summable_reciprocal_smoothNumbers (K : ℕ) :
    Summable (fun d : K.smoothNumbers => (d.1 : ℝ)⁻¹) := by
  have hprime {p : ℕ} (hp : p.Prime) : ‖reciprocalHom p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (inv_nonneg.mpr (by exact_mod_cast hp.pos.le))]
    change (p : ℝ)⁻¹ < 1
    rw [inv_lt_one₀ (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := reciprocalHom) hprime K
  change Summable (fun d : K.smoothNumbers => reciprocalHom d.1)
  exact Summable.of_norm heuler.1

/-- A uniform finite-tail formulation of smooth reciprocal summability. -/
lemma exists_smooth_reciprocal_cutoff (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < ε := by
  let f : K.smoothNumbers → ℝ := fun d => (d.1 : ℝ)⁻¹
  have hf : Summable f := summable_reciprocal_smoothNumbers K
  obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp hf) ε hε
  let M := s.sup (fun d => d.1) + 1
  refine ⟨M, ?_⟩
  intro T hT
  have hdisj : Disjoint T s := Finset.disjoint_left.mpr (by
    intro d hdT hds
    have hdle : d.1 ≤ s.sup (fun e => e.1) := Finset.le_sup hds
    have hMd := hT d hdT
    dsimp only [M] at hMd
    omega)
  have hnorm := hs T hdisj
  have hnonneg : 0 ≤ ∑ d ∈ T, f d :=
    Finset.sum_nonneg fun d hd => inv_nonneg.mpr (Nat.cast_nonneg d.1)
  change (∑ d ∈ T, f d) < ε
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm

lemma firstLocalFactor_primeTailDelta
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (d : Arithmetic.ModulusIndex D)
    (ha : Arithmetic.assignedAt Q d.1 i)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K)
    (j : Fin (i + 1)) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Arithmetic.firstLocalFactor S hi j
      (Arithmetic.stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi j) =
      (1 : ℝ) / ((Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j) ^
        d.1.factorization (Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j)) : ℕ) : ℝ) := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  have hapos := (Arithmetic.assignedAt_iff_of_lt Q d.1 hi).mp ha
  by_cases hlast : j.1 = i
  · have hcoord : Arithmetic.stageCoordinate Q hi j = ⟨i, hi⟩ := Fin.ext hlast
    rw [Arithmetic.firstLocalFactor]
    simp only [hlast, if_true, Arithmetic.stageExponentVector]
    have hne : d.1.factorization
        (Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j)) ≠ 0 := by
      simpa only [hcoord] using hapos.1
    simp [hne]
  · have hjlt : j.1 < i := by omega
    have hjpc : j.1 < Arithmetic.primeCount Q := hjlt.trans hi
    have hprimeLt :
        Arithmetic.primeAt Q ⟨j.1, hjpc⟩ < Arithmetic.primeAt Q ⟨i, hi⟩ := by
      exact Arithmetic.primeAt_strictMono Q hjlt
    have hjK : Arithmetic.primeAt Q ⟨j.1, hjpc⟩ < K := hprimeLt.trans hpK
    have hdelta : primeTailDelta Q K j.1 = 0 := by
      simp [primeTailDelta, hjpc, hjK]
    rw [Arithmetic.firstLocalFactor]
    simp only [hlast, if_false, Arithmetic.stageExponentVector,
      Arithmetic.stageCoordinate]
    by_cases he : d.1.factorization (Arithmetic.primeAt Q ⟨j.1, hjpc⟩) = 0
    · simp [he]
    · simp [Arithmetic.arithmeticSchedule, hdelta, he]

/-- At a stage below the prime cutoff, the first-moment weight of an assigned
modulus is exactly its reciprocal. -/
lemma small_stage_weight_eq_inv
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (d : Arithmetic.ModulusIndex D)
    (ha : Arithmetic.assignedAt Q d.1 i)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Arithmetic.stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, Arithmetic.classFactor S d.1 j =
      1 / (d.1 : ℝ) := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  calc
    Arithmetic.stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, Arithmetic.classFactor S d.1 j =
      ∏ j : Fin (i + 1),
        Arithmetic.firstLocalFactor S hi j
          (Arithmetic.stageExponentVector Q d.1 hQ
            (hd d.1 d.2) (hdQ d.1 d.2) hi j) := by
      symm
      exact Arithmetic.prod_firstLocal_stageExponent S hQ
        (hd d.1 d.2) (hdQ d.1 d.2) hi ha
    _ = ∏ j : Fin (i + 1),
        (1 : ℝ) /
          ((Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j) ^
            d.1.factorization
              (Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j)) : ℕ) : ℝ) := by
      apply Fintype.prod_congr
      intro j
      exact firstLocalFactor_primeTailDelta Q D a hQ hd hdQ K hi d ha hpK j
    _ = 1 / (d.1 : ℝ) := by
      simp_rw [div_eq_mul_inv, one_mul]
      rw [Finset.prod_inv_distrib]
      congr 1
      rw [← Nat.cast_prod]
      exact_mod_cast Arithmetic.prod_stage_prime_powers_eq Q d.1 hQ
        (hd d.1 d.2) (hdQ d.1 d.2) hi ha

lemma small_prime_stage_cost_le_sum
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Distortion.stageCost S i ≤
      ∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹ := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  calc
    Distortion.stageCost S i ≤
        Distortion.firstMoment (Distortion.prefixProb S i)
          (Arithmetic.stageBad Q D a hQ hd hdQ i) := by
      simpa only [Distortion.stageCost, Distortion.prefixProb_succ, S,
        Arithmetic.arithmeticSchedule] using
        (Distortion.step_mass_bad_le_first (Distortion.prefixProb S i)
          (Arithmetic.stageBad Q D a hQ hd hdQ i)
          (primeTailDelta_nonneg Q K i) (primeTailDelta_lt_one Q K i))
    _ ≤ ∑ d ∈ Arithmetic.stageIndices Q D i,
        Arithmetic.stageCoefficient Q d.1 i *
          ∏ j ∈ Finset.range i, Arithmetic.classFactor S d.1 j :=
      Arithmetic.firstMoment_stageBad_le_products Q D a hQ hd hdQ
        (primeTailDelta Q K) (primeTailDelta_nonneg Q K)
        (primeTailDelta_lt_one Q K) hi
    _ = ∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hdI
      rw [← one_div]
      exact small_stage_weight_eq_inv Q D a hQ hd hdQ K hi d
        ((Finset.mem_filter.mp hdI).2) hpK

lemma small_prime_stage_cost_lt
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K M : ℕ) {ε : ℝ}
    (htail : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) → (∑ d ∈ T, (d.1 : ℝ)⁻¹) < ε)
    (hmin : ∀ d ∈ D, M ≤ d)
    {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Distortion.stageCost S i < ε := by
  dsimp only
  let I := Arithmetic.stageIndices Q D i
  let e : {d // d ∈ I} ↪ K.smoothNumbers :=
    ⟨fun d => ⟨d.1.1, Arithmetic.mem_smoothNumbers_of_assignedAt Q d.1.1 K hQ
        (hd d.1.1 d.1.2) (hdQ d.1.1 d.1.2) hi
        ((Finset.mem_filter.mp d.2).2) hpK⟩,
      fun d₁ d₂ h => by
        have hval : d₁.1.1 = d₂.1.1 :=
          congrArg (fun z : K.smoothNumbers => z.1) h
        exact Subtype.ext (Subtype.ext hval)⟩
  let T : Finset K.smoothNumbers := I.attach.map e
  have hTmin : ∀ d ∈ T, M ≤ d.1 := by
    intro d hdT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hdT
    exact hmin x.1.1 x.1.2
  have hsum :
      (∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹) =
        ∑ d ∈ T, (d.1 : ℝ)⁻¹ := by
    change (∑ d ∈ I, (d.1 : ℝ)⁻¹) = _
    rw [← Finset.sum_attach, Finset.sum_map]
    rfl
  calc
    Distortion.stageCost
        (Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
          (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)) i ≤
      ∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹ :=
        small_prime_stage_cost_le_sum Q D a hQ hd hdQ K hi hpK
    _ = ∑ d ∈ T, (d.1 : ℝ)⁻¹ := hsum
    _ < ε := htail T hTmin

/-- The distortion stages whose controlling prime is below `K`. -/
def smallStages (Q K : ℕ) : Finset ℕ :=
  (Finset.range (Arithmetic.primeCount Q)).filter fun i =>
    if hi : i < Arithmetic.primeCount Q then
      Arithmetic.primeAt Q ⟨i, hi⟩ < K
    else False

lemma mem_smallStages_iff (Q K : ℕ) {i : ℕ}
    (hi : i < Arithmetic.primeCount Q) :
    i ∈ smallStages Q K ↔ Arithmetic.primeAt Q ⟨i, hi⟩ < K := by
  simp [smallStages, hi]

lemma card_smallStages_le (Q K : ℕ) :
    (smallStages Q K).card ≤ K := by
  let e : {i // i ∈ smallStages Q K} ↪ Fin K :=
    ⟨fun i =>
      let hi : i.1 < Arithmetic.primeCount Q :=
        Finset.mem_range.mp (Finset.mem_filter.mp i.2).1
      ⟨Arithmetic.primeAt Q ⟨i.1, hi⟩,
        (mem_smallStages_iff Q K hi).mp i.2⟩,
      fun i j h => by
        have hp : Arithmetic.primeAt Q
              ⟨i.1, Finset.mem_range.mp (Finset.mem_filter.mp i.2).1⟩ =
            Arithmetic.primeAt Q
              ⟨j.1, Finset.mem_range.mp (Finset.mem_filter.mp j.2).1⟩ :=
          congrArg Fin.val h
        have hij := (Arithmetic.primeAt_strictMono Q).injective hp
        exact Subtype.ext (congrArg Fin.val hij)⟩
  have hcard := Fintype.card_le_of_injective e e.injective
  simpa using hcard

lemma sum_small_stage_cost_lt_half
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K M : ℕ)
    (htail : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < 1 / (2 * ((K : ℝ) + 1)))
    (hmin : ∀ d ∈ D, M ≤ d) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∑ i ∈ smallStages Q K, Distortion.stageCost S i) < 1 / 2 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hε0 : 0 ≤ ε := by dsimp only [ε]; positivity
  calc
    (∑ i ∈ smallStages Q K, Distortion.stageCost S i) ≤
        ∑ _i ∈ smallStages Q K, ε := by
      apply Finset.sum_le_sum
      intro i hiS
      have hi : i < Arithmetic.primeCount Q :=
        Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
      have hpK := (mem_smallStages_iff Q K hi).mp hiS
      exact (small_prime_stage_cost_lt Q D a hQ hd hdQ K M htail hmin hi hpK).le
    _ = ((smallStages Q K).card : ℝ) * ε := by simp
    _ ≤ (K : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_smallStages_le Q K) hε0
    _ < 1 / 2 := by
      dsimp only [ε]
      have hden : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by positivity
      rw [show (K : ℝ) * (1 / (2 * ((K : ℝ) + 1))) =
        (K : ℝ) / (2 * ((K : ℝ) + 1)) by ring]
      rw [div_lt_iff₀ hden]
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

/-- The complementary set of stages whose controlling prime is at least
`K`. -/
def largeStages (Q K : ℕ) : Finset ℕ :=
  Finset.range (Arithmetic.primeCount Q) \ smallStages Q K

lemma mem_largeStages (Q K : ℕ) {i : ℕ} :
    i ∈ largeStages Q K ↔
      ∃ hi : i < Arithmetic.primeCount Q,
        K ≤ Arithmetic.primeAt Q ⟨i, hi⟩ := by
  rw [largeStages, Finset.mem_sdiff]
  constructor
  · rintro ⟨hirange, hismall⟩
    have hi := Finset.mem_range.mp hirange
    refine ⟨hi, ?_⟩
    exact Nat.le_of_not_gt (fun hpK =>
      hismall ((mem_smallStages_iff Q K hi).mpr hpK))
  · rintro ⟨hi, hKp⟩
    refine ⟨Finset.mem_range.mpr hi, ?_⟩
    intro hismall
    exact (Nat.not_lt_of_ge hKp) ((mem_smallStages_iff Q K hi).mp hismall)

lemma sum_large_stage_cost_lt_half
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (K : ℕ) (hK3 : 3 ≤ K)
    (htail : ∀ P : Finset ℕ, (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2)
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∑ i ∈ largeStages Q K, Distortion.stageCost S i) < 1 / 2 := by
  dsimp only
  let I := largeStages Q K
  let e : {i // i ∈ I} ↪ ℕ :=
    ⟨fun i =>
      Arithmetic.primeAt Q
        ⟨i.1, (mem_largeStages Q K).mp i.2 |>.choose⟩,
      fun i j h => by
        have hij := (Arithmetic.primeAt_strictMono Q).injective h
        exact Subtype.ext (congrArg Fin.val hij)⟩
  let P : Finset ℕ := I.attach.map e
  have hP : ∀ p ∈ P, K ≤ p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hp
    exact (mem_largeStages Q K).mp i.2 |>.choose_spec
  have hsum :
      (∑ i ∈ I.attach,
        4 * C * Real.log (e i : ℝ) ^ 20 / (e i : ℝ) ^ 2) =
        ∑ p ∈ P, 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := by
    rw [Finset.sum_map]
  calc
    (∑ i ∈ largeStages Q K,
        Distortion.stageCost
          (Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
            (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)) i) =
      ∑ i ∈ I.attach,
        Distortion.stageCost
          (Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
            (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)) i.1 := by
      change (∑ i ∈ I, _) = _
      rw [← Finset.sum_attach]
    _ ≤ ∑ i ∈ I.attach,
        4 * C * Real.log (e i : ℝ) ^ 20 / (e i : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hiAttach
      let hi : i.1 < Arithmetic.primeCount Q := (mem_largeStages Q K).mp i.2 |>.choose
      have hKp : K ≤ Arithmetic.primeAt Q ⟨i.1, hi⟩ :=
        (mem_largeStages Q K).mp i.2 |>.choose_spec
      have heq : e i = Arithmetic.primeAt Q ⟨i.1, hi⟩ := by
        dsimp only [e]
        congr 1
      rw [heq]
      exact large_prime_stage_cost_le C hC0 hC Q D a hQ hd hdQ hK3 hi hKp
    _ = ∑ p ∈ P, 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := hsum
    _ < 1 / 2 := htail P hP

/-- The complete accumulated distortion cost is strictly below one. -/
lemma sum_all_stage_cost_lt_one
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (K : ℕ) (hK3 : 3 ≤ K)
    (hlarge : ∀ P : Finset ℕ, (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2)
    (M : ℕ)
    (hsmall : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < 1 / (2 * ((K : ℝ) + 1)))
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (hmin : ∀ d ∈ D, M ≤ d) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∑ i ∈ Finset.range (Arithmetic.primeCount Q),
      Distortion.stageCost S i) < 1 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  have hs := sum_small_stage_cost_lt_half Q D a hQ hd hdQ K M hsmall hmin
  have hl := sum_large_stage_cost_lt_half C hC0 hC K hK3 hlarge
    Q D a hQ hd hdQ
  have hsubset :
      smallStages Q K ⊆ Finset.range (Arithmetic.primeCount Q) :=
    Finset.filter_subset _ _
  have hunion :
      smallStages Q K ∪ largeStages Q K =
        Finset.range (Arithmetic.primeCount Q) := by
    rw [largeStages, Finset.union_sdiff_of_subset hsubset]
  have hdisj : Disjoint (smallStages Q K) (largeStages Q K) := by
    rw [largeStages]
    exact Finset.disjoint_sdiff
  calc
    (∑ i ∈ Finset.range (Arithmetic.primeCount Q),
        Distortion.stageCost S i) =
      ∑ i ∈ smallStages Q K ∪ largeStages Q K,
        Distortion.stageCost S i := by rw [hunion]
    _ = (∑ i ∈ smallStages Q K, Distortion.stageCost S i) +
        ∑ i ∈ largeStages Q K, Distortion.stageCost S i := by
      rw [Finset.sum_union hdisj]
    _ < 1 := by linarith

/-- The arithmetic distortion process leaves at least one residue after every
stage whenever all moduli lie beyond the smooth-number cutoff. -/
lemma arithmetic_residual_nonempty
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (K : ℕ) (hK3 : 3 ≤ K)
    (hlarge : ∀ P : Finset ℕ, (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2)
    (M : ℕ)
    (hsmall : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < 1 / (2 * ((K : ℝ) + 1)))
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (hmin : ∀ d ∈ D, M ≤ d) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (Distortion.residual S (Arithmetic.primeCount Q)).Nonempty := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  apply Distortion.residual_nonempty_of_sum_cost_lt_one
  exact sum_all_stage_cost_lt_one C hC0 hC K hK3 hlarge M hsmall
    Q D a hQ hd hdQ hmin

end Analytic

/-! ## The uniform minimum-modulus theorem -/

/-- The distortion sieve supplies a universal upper bound for the least
modulus of every distinct covering system. -/
theorem uniformMinimumBound : HasUniformMinimumBound := by
  obtain ⟨C, hCpos, hC⟩ := Analytic.exists_secondEulerProduct_log_bound
  obtain ⟨K, hK3, hlarge⟩ := Analytic.exists_large_prime_cutoff C hCpos.le
  have hε : (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) := by positivity
  obtain ⟨M, hsmall⟩ := Analytic.exists_smooth_reciprocal_cutoff K hε
  refine ⟨M, ?_⟩
  intro D a hcover
  by_contra hnone
  have hmin : ∀ d ∈ D, M ≤ d := by
    intro d hdD
    exact Nat.le_of_not_gt fun hdM => hnone ⟨d, hdD, hdM⟩
  let Q : ℕ := D.prod id
  have hd : ∀ d ∈ D, d ≠ 0 := by
    intro d hdD
    exact Nat.ne_of_gt (Nat.zero_lt_two.trans_le (hcover.1 d hdD))
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact Finset.prod_ne_zero_iff.mpr hd
  have hdQ : ∀ d ∈ D, d ∣ Q := by
    intro d hdD
    dsimp only [Q]
    exact Finset.dvd_prod_of_mem id hdD
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ
    (Analytic.primeTailDelta Q K)
    (Analytic.primeTailDelta_nonneg Q K)
    (Analytic.primeTailDelta_lt_one Q K)
  have hres :
      (Distortion.residual S (Arithmetic.primeCount Q)).Nonempty := by
    exact Analytic.arithmetic_residual_nonempty C hCpos.le hC K hK3 hlarge
      M hsmall Q D a hQ hd hdQ hmin
  obtain ⟨x, hx⟩ := hres
  letI : NeZero Q := ⟨hQ⟩
  let y : ZMod Q := Arithmetic.prefixCRTEq Q hQ x
  let z : ℤ := y.val
  obtain ⟨d, hdD, hz⟩ := hcover.2 z
  have hcast :
      ZMod.castHom (hdQ d hdD) (ZMod d) (Arithmetic.prefixCRTEq Q hQ x) =
        (a d : ZMod d) := by
    have hy : (z : ZMod Q) = y := by
      dsimp only [z]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val y
    change ZMod.castHom (hdQ d hdD) (ZMod d) y = (a d : ZMod d)
    rw [← hy]
    simpa using (ZMod.intCast_eq_intCast_iff z (a d) d).2 hz
  have hbox := Arithmetic.mem_classBox_of_cast_eq Q d hQ (hd d hdD)
    (hdQ d hdD) (a d) x hcast
  obtain ⟨i, hi, hai⟩ := Arithmetic.exists_assignedAt Q d hQ (hdQ d hdD)
    (hcover.1 d hdD)
  have houtside := Arithmetic.residual_not_mem_assigned_classBox
    Q D a hQ hd hdQ (Analytic.primeTailDelta Q K)
    (Analytic.primeTailDelta_nonneg Q K)
    (Analytic.primeTailDelta_lt_one Q K)
    (Arithmetic.primeCount Q) x hx ⟨d, hdD⟩ i hi hai
  exact houtside hbox

/-- Equivalent negative formulation: least moduli cannot be arbitrarily
large. -/
theorem not_hasArbitrarilyLargeMinimum : ¬HasArbitrarilyLargeMinimum :=
  uniformBound_iff_not_arbitrarilyLarge.mp uniformMinimumBound

/-- Erdős Problem 2: distinct covering systems have a uniform bound on their
least modulus. -/
theorem erdos_2 :
    ∃ M : ℕ, ∀ (D : Finset ℕ) (a : ℕ → ℤ),
      IsDistinctCoveringSystem D a → ∃ d ∈ D, d < M :=
  uniformMinimumBound

#print axioms erdos_2

end

end Erdos2
