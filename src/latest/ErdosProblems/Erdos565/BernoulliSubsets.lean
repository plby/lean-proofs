import ErdosProblems.Erdos565.FiniteBernoulliLocality
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Finite Bernoulli random subsets

This file provides the elementary product-probability identities used in the
container argument for Erdős problem 565.  Everything is an explicit finite
sum over a powerset.  In particular, no measure-theoretic independence is
hidden in the statements below.
-/

open scoped BigOperators

namespace Erdos565
namespace BernoulliSubsets

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The mass of `X` in the homogeneous Bernoulli model on `U`.

Only values with `X ⊆ U` are used by `eventMass`; the product definition is
convenient for splitting disjoint coordinate blocks. -/
def weight (q : ℝ) (U X : Finset V) : ℝ :=
  Erdos76.FiniteNibble.bernoulliMass U (fun _ ↦ q) X

/-- The mass of an event in the `q`-random-subset model on `U`. -/
def eventMass (q : ℝ) (U : Finset V) (event : Finset V → Prop) : ℝ :=
  ∑ X ∈ U.powerset, if event X then weight q U X else 0

/-- Conditional mass, written only in terms of finite sums. -/
def conditionalMass (q : ℝ) (U : Finset V)
    (event condition : Finset V → Prop) : ℝ :=
  eventMass q U (fun X ↦ event X ∧ condition X) / eventMass q U condition

/-- An event is increasing under inclusion. -/
def Increasing (event : Finset V → Prop) : Prop :=
  ∀ ⦃X Y⦄, X ⊆ Y → event X → event Y

/-- An event is decreasing under inclusion. -/
def Decreasing (event : Finset V → Prop) : Prop :=
  ∀ ⦃X Y⦄, X ⊆ Y → event Y → event X

@[simp] theorem weight_eq (q : ℝ) (U X : Finset V) :
    weight q U X = (∏ _x ∈ X, q) * ∏ _x ∈ U \ X, (1 - q) := rfl

/-- Cardinality form of the homogeneous mass. -/
theorem weight_eq_pow (q : ℝ) (U X : Finset V) :
    weight q U X = q ^ X.card * (1 - q) ^ (U \ X).card := by
  simp [weight, Erdos76.FiniteNibble.bernoulliMass]

theorem weight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {U X : Finset V} (hXU : X ⊆ U) :
    0 ≤ weight q U X := by
  exact Erdos76.FiniteNibble.bernoulliMass_nonneg hXU
    (fun _ _ ↦ hq0) (fun _ _ ↦ hq1)

theorem eventMass_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (U : Finset V) (event : Finset V → Prop) :
    0 ≤ eventMass q U event := by
  unfold eventMass
  exact sum_nonneg fun X hX ↦ by
    split
    · exact weight_nonneg hq0 hq1 (mem_powerset.mp hX)
    · exact le_rfl

theorem eventMass_eq_restrictedEventMass (q : ℝ) (U : Finset V)
    (event : Finset V → Prop) :
    eventMass q U event =
      Erdos76.FiniteNibble.restrictedEventMass U (fun _ ↦ q) event := by
  symm
  calc
    Erdos76.FiniteNibble.restrictedEventMass U (fun _ ↦ q) event =
        ∑ X : Erdos76.FiniteNibble.Subsets U,
          if event X.1 then weight q U X.1 else 0 := by
      rfl
    _ = ∑ X : ↥U.powerset, if event X.1 then weight q U X.1 else 0 := by
      apply Fintype.sum_equiv (Erdos76.FiniteNibble.subsetsEquivPowersetAttach U)
      intro X
      rfl
    _ = ∑ X ∈ U.powerset, if event X then weight q U X else 0 := by
      simpa using
        (Finset.sum_attach U.powerset
          (fun X : Finset V ↦ if event X then weight q U X else 0))
    _ = eventMass q U event := rfl

/-- The masses of all subsets add to one. -/
@[simp] theorem eventMass_true (q : ℝ) (U : Finset V) :
    eventMass q U (fun _ ↦ True) = 1 := by
  rw [eventMass_eq_restrictedEventMass]
  exact Erdos76.FiniteNibble.restrictedEventMass_true U (fun _ ↦ q)

@[simp] theorem eventMass_false (q : ℝ) (U : Finset V) :
    eventMass q U (fun _ ↦ False) = 0 := by
  simp [eventMass]

theorem eventMass_mono {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {U : Finset V} {A B : Finset V → Prop}
    (hAB : ∀ X, A X → B X) :
    eventMass q U A ≤ eventMass q U B := by
  unfold eventMass
  apply sum_le_sum
  intro X hX
  by_cases hA : A X
  · simp [hA, hAB X hA]
  · simp only [hA, ↓reduceIte]
    split
    · exact weight_nonneg hq0 hq1 (mem_powerset.mp hX)
    · exact le_rfl

theorem eventMass_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (U : Finset V) (event : Finset V → Prop) :
    eventMass q U event ≤ 1 := by
  rw [← eventMass_true q U]
  exact eventMass_mono hq0 hq1 (fun _ _ ↦ trivial)

/-- Exact factorisation for events on disjoint coordinate blocks. -/
theorem eventMass_and_of_disjoint {q : ℝ} {U W : Finset V}
    {A B : Finset V → Prop} (hUW : Disjoint U W)
    (hA : Erdos76.FiniteNibble.EventDependsOn U A)
    (hB : Erdos76.FiniteNibble.EventDependsOn W B) :
    eventMass q (U ∪ W) (fun X ↦ A X ∧ B X) =
      eventMass q U A * eventMass q W B := by
  rw [eventMass_eq_restrictedEventMass, eventMass_eq_restrictedEventMass,
    eventMass_eq_restrictedEventMass]
  exact Erdos76.FiniteNibble.restrictedEventMass_and_of_disjoint hUW hA hB

/-- A local event has the same mass after irrelevant coordinates are added. -/
theorem eventMass_union_of_dependsOn_left {q : ℝ} {U W : Finset V}
    {A : Finset V → Prop} (hUW : Disjoint U W)
    (hA : Erdos76.FiniteNibble.EventDependsOn U A) :
    eventMass q (U ∪ W) A = eventMass q U A := by
  have h := eventMass_and_of_disjoint (q := q) hUW hA
    (Erdos76.FiniteNibble.eventDependsOn_true W)
  simpa using h

/-- A local event has the same mass after irrelevant coordinates are added. -/
theorem eventMass_union_of_dependsOn_right {q : ℝ} {U W : Finset V}
    {B : Finset V → Prop} (hUW : Disjoint U W)
    (hB : Erdos76.FiniteNibble.EventDependsOn W B) :
    eventMass q (U ∪ W) B = eventMass q W B := by
  have h := eventMass_and_of_disjoint (q := q) hUW
    (Erdos76.FiniteNibble.eventDependsOn_true U) hB
  simpa [mul_comm] using h

/-- Conditioning on an event in a disjoint coordinate block leaves the first
event's mass unchanged. -/
theorem conditionalMass_of_disjoint {q : ℝ} {U W : Finset V}
    {A B : Finset V → Prop} (hUW : Disjoint U W)
    (hA : Erdos76.FiniteNibble.EventDependsOn U A)
    (hB : Erdos76.FiniteNibble.EventDependsOn W B)
    (hBpos : eventMass q W B ≠ 0) :
    conditionalMass q (U ∪ W) A B = eventMass q U A := by
  unfold conditionalMass
  rw [eventMass_and_of_disjoint hUW hA hB,
    eventMass_union_of_dependsOn_right hUW hB]
  exact mul_div_cancel_right₀ _ hBpos

/-- The event that every coordinate of `L` is present depends only on `L`. -/
theorem contains_dependsOn (L : Finset V) :
    Erdos76.FiniteNibble.EventDependsOn L (fun X ↦ L ⊆ X) := by
  intro X Y hXY
  unfold Erdos76.FiniteNibble.AgreesOn at hXY
  constructor
  · intro hLX x hxL
    have hx : x ∈ X ∩ L := mem_inter.mpr ⟨hLX hxL, hxL⟩
    rw [hXY] at hx
    exact (mem_inter.mp hx).1
  · intro hLY x hxL
    have hx : x ∈ Y ∩ L := mem_inter.mpr ⟨hLY hxL, hxL⟩
    rw [← hXY] at hx
    exact (mem_inter.mp hx).1

/-- The cylinder probability `P(L ⊆ X) = q^|L|`. -/
theorem eventMass_contains {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {U L : Finset V} (hLU : L ⊆ U) :
    eventMass q U (fun X ↦ L ⊆ X) = q ^ L.card := by
  -- Split `U` into `L` and its complement.  On the `L` block only the full
  -- subset contributes, while the complementary block has total mass one.
  have hdisj : Disjoint L (U \ L) := disjoint_sdiff
  have hcover : L ∪ (U \ L) = U := union_sdiff_of_subset hLU
  rw [← hcover, eventMass_union_of_dependsOn_left hdisj (contains_dependsOn L)]
  unfold eventMass
  rw [sum_eq_single L]
  · simp [weight_eq_pow]
  · intro X hX hXL
    have hsub : X ⊆ L := mem_powerset.mp hX
    have hnsub : ¬L ⊆ X := by
      intro hLX
      exact hXL (Subset.antisymm hsub hLX)
    simp [hnsub]
  · simp

private def indicator (event : Finset V → Prop) (X : Finset V) : ℝ :=
  if event X then 1 else 0

private theorem indicator_nonneg (event : Finset V → Prop) :
    0 ≤ indicator event := by
  intro X
  by_cases h : event X <;> simp [indicator, h]

private theorem indicator_monotone {event : Finset V → Prop}
    (hevent : Increasing event) : Monotone (indicator event) := by
  intro X Y hXY
  by_cases hX : event X
  · have hY := hevent hXY hX
    simp [indicator, hX, hY]
  · by_cases hY : event Y <;> simp [indicator, hX, hY]

private theorem indicator_antitone {event : Finset V → Prop}
    (hevent : Decreasing event) : Antitone (indicator event) := by
  intro X Y hXY
  by_cases hY : event Y
  · have hX := hevent hXY hY
    simp [indicator, hX, hY]
  · by_cases hX : event X <;> simp [indicator, hX, hY]

private theorem weight_log_modular (q : ℝ) (X Y : Finset V) :
    weight q Finset.univ X * weight q Finset.univ Y =
      weight q Finset.univ (X ∩ Y) * weight q Finset.univ (X ∪ Y) := by
  simp only [weight_eq_pow]
  have hcard : (X ∩ Y).card + (X ∪ Y).card = X.card + Y.card :=
    card_inter_add_card_union X Y
  have hqpow : q ^ X.card * q ^ Y.card =
      q ^ (X ∩ Y).card * q ^ (X ∪ Y).card := by
    rw [← pow_add, ← pow_add, hcard]
  have hcomp :
      (Finset.univ \ X).card + (Finset.univ \ Y).card =
        (Finset.univ \ (X ∩ Y)).card + (Finset.univ \ (X ∪ Y)).card := by
    simp only [card_sdiff, inter_univ]
    have hXle : X.card ≤ (Finset.univ : Finset V).card :=
      card_le_card (subset_univ X)
    have hYle : Y.card ≤ (Finset.univ : Finset V).card :=
      card_le_card (subset_univ Y)
    have hIle : (X ∩ Y).card ≤ (Finset.univ : Finset V).card :=
      card_le_card (subset_univ (X ∩ Y))
    have hUle : (X ∪ Y).card ≤ (Finset.univ : Finset V).card :=
      card_le_card (subset_univ (X ∪ Y))
    omega
  have hcpow :
      (1 - q) ^ (Finset.univ \ X).card *
          (1 - q) ^ (Finset.univ \ Y).card =
        (1 - q) ^ (Finset.univ \ (X ∩ Y)).card *
          (1 - q) ^ (Finset.univ \ (X ∪ Y)).card := by
    rw [← pow_add, ← pow_add, hcomp]
  calc
    (q ^ X.card * (1 - q) ^ (Finset.univ \ X).card) *
          (q ^ Y.card * (1 - q) ^ (Finset.univ \ Y).card) =
        (q ^ X.card * q ^ Y.card) *
          ((1 - q) ^ (Finset.univ \ X).card *
            (1 - q) ^ (Finset.univ \ Y).card) := by ring
    _ = (q ^ (X ∩ Y).card * q ^ (X ∪ Y).card) *
          ((1 - q) ^ (Finset.univ \ (X ∩ Y)).card *
            (1 - q) ^ (Finset.univ \ (X ∪ Y)).card) := by rw [hqpow, hcpow]
    _ = (q ^ (X ∩ Y).card * (1 - q) ^ (Finset.univ \ (X ∩ Y)).card) *
          (q ^ (X ∪ Y).card * (1 - q) ^ (Finset.univ \ (X ∪ Y)).card) := by ring

private theorem eventMass_univ_eq_sum (q : ℝ)
    (event : Finset V → Prop) :
    eventMass q Finset.univ event =
      ∑ X : Finset V, weight q Finset.univ X * indicator event X := by
  unfold eventMass
  simp only [Finset.powerset_univ]
  apply sum_congr rfl
  intro X _
  by_cases h : event X <;> simp [indicator, h]

/-- Harris--FKG for two increasing events in the finite homogeneous
Bernoulli product space. -/
theorem harris_increasing {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {A B : Finset V → Prop} (hA : Increasing A) (hB : Increasing B) :
    eventMass q Finset.univ A * eventMass q Finset.univ B ≤
      eventMass q Finset.univ (fun X ↦ A X ∧ B X) := by
  let μ : Finset V → ℝ := fun X ↦ weight q Finset.univ X
  let f : Finset V → ℝ := indicator A
  let g : Finset V → ℝ := indicator B
  have hμ0 : 0 ≤ μ := fun X ↦ weight_nonneg hq0 hq1 (subset_univ X)
  have hlog : ∀ X Y, μ X * μ Y ≤ μ (X ⊓ Y) * μ (X ⊔ Y) := by
    intro X Y
    exact (weight_log_modular q X Y).le
  have hfkg := fkg (μ := μ) (f := f) (g := g)
    hμ0 (indicator_nonneg A) (indicator_nonneg B)
    (indicator_monotone hA) (indicator_monotone hB) hlog
  have hμsum : (∑ X, μ X) = 1 := by
    calc
      (∑ X, μ X) = eventMass q Finset.univ (fun _ ↦ True) := by
        rw [eventMass_univ_eq_sum (V := V)]
        simp [μ, indicator]
      _ = 1 := eventMass_true q Finset.univ
  rw [hμsum] at hfkg
  rw [one_mul] at hfkg
  calc
    eventMass q Finset.univ A * eventMass q Finset.univ B =
        (∑ X, μ X * f X) * ∑ X, μ X * g X := by
      rw [eventMass_univ_eq_sum (V := V), eventMass_univ_eq_sum (V := V)]
    _ ≤ ∑ X, μ X * (f X * g X) := hfkg
    _ = eventMass q Finset.univ (fun X ↦ A X ∧ B X) := by
      rw [eventMass_univ_eq_sum (V := V)]
      apply sum_congr rfl
      intro X _
      by_cases hAX : A X <;> by_cases hBX : B X <;>
        simp [μ, f, g, indicator, hAX, hBX]

/-- Harris--FKG for two decreasing events. -/
theorem harris_decreasing {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {A B : Finset V → Prop} (hA : Decreasing A) (hB : Decreasing B) :
    eventMass q Finset.univ A * eventMass q Finset.univ B ≤
      eventMass q Finset.univ (fun X ↦ A X ∧ B X) := by
  let Ac : Finset V → Prop := fun X ↦ A Xᶜ
  let Bc : Finset V → Prop := fun X ↦ B Xᶜ
  have hAc : Increasing Ac := by
    intro X Y hXY hAX
    exact hA (Finset.compl_subset_compl.mpr hXY) hAX
  have hBc : Increasing Bc := by
    intro X Y hXY hBX
    exact hB (Finset.compl_subset_compl.mpr hXY) hBX
  have hq'0 : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hq'1 : 1 - q ≤ 1 := by linarith
  have hh := harris_increasing (V := V) hq'0 hq'1 hAc hBc
  have hweight_compl (X : Finset V) :
      weight (1 - q) Finset.univ Xᶜ = weight q Finset.univ X := by
    simp [weight_eq_pow, Finset.card_compl, card_sdiff, inter_univ]
    ring
  let e : Finset V ≃ Finset V := Equiv.ofBijective (fun X ↦ Xᶜ) compl_bijective
  have mass_compl (C : Finset V → Prop) :
      eventMass (1 - q) Finset.univ (fun X ↦ C Xᶜ) =
        eventMass q Finset.univ C := by
    rw [eventMass_univ_eq_sum (V := V), eventMass_univ_eq_sum (V := V)]
    calc
      (∑ X : Finset V,
          weight (1 - q) Finset.univ X * indicator (fun Y ↦ C Yᶜ) X) =
          ∑ X : Finset V,
            weight (1 - q) Finset.univ (e X) *
              indicator (fun Y ↦ C Yᶜ) (e X) := by
        exact (e.sum_comp (fun X ↦
          weight (1 - q) Finset.univ X * indicator (fun Y ↦ C Yᶜ) X)).symm
      _ = ∑ X : Finset V, weight q Finset.univ X * indicator C X := by
        apply sum_congr rfl
        intro X _
        change weight (1 - q) Finset.univ Xᶜ * indicator (fun Y ↦ C Yᶜ) Xᶜ = _
        rw [hweight_compl]
        simp [indicator]
  rw [mass_compl A, mass_compl B] at hh
  have hconj :
      eventMass (1 - q) Finset.univ (fun X ↦ Ac X ∧ Bc X) =
        eventMass q Finset.univ (fun X ↦ A X ∧ B X) := by
    simpa [Ac, Bc] using mass_compl (fun X ↦ A X ∧ B X)
  rw [hconj] at hh
  exact hh

end

end BernoulliSubsets
end Erdos565
