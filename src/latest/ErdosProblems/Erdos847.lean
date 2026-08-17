/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import «_scratch».Erdos847Construction

/-!
# Erdős Problem 847

The negative solution is due to Christian Reiher, Vojtěch Rödl, and Marcelo Sales,
*Colouring versus density in integers and Hales--Jewett cubes* (2024).

The detailed mathematical proof and its Leanization map are in `tex/847.tex`.
-/

namespace Erdos847

open Set

attribute [local instance] Classical.propDecidable

/-- `HasFew3APs A` is the local positive-proportion hypothesis in the upstream statement. -/
def HasFew3APs (A : Set ℕ) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ B : Set ℕ, B ⊆ A → Finite B →
    ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

/-- A nonconstant monochromatic three-term arithmetic progression for a coloring of `A`. -/
def HasMonochromaticThreeAP (A : Set ℕ) {r : ℕ} (color : ℕ → Fin r) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a + c = b + b ∧ a ≠ c ∧ color a = color b ∧ color b = color c

/-- Every coloring of `A` by a nonempty finite palette has a monochromatic three-AP. -/
def RamseyForThreeAP (A : Set ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ color : ℕ → Fin r, HasMonochromaticThreeAP A color

/-- The two properties supplied by the Reiher--Rödl--Sales counterexample. -/
def IsRRSCounterexample (A : Set ℕ) (μ : ℝ) : Prop :=
  RamseyForThreeAP A ∧
    ∀ B : Set ℕ, B ⊆ A → Finite B →
      ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ μ * B.ncard ∧ ThreeAPFree C

lemma hasFew3APs_of_isRRSCounterexample {A : Set ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hA : IsRRSCounterexample A μ) : HasFew3APs A := by
  exact ⟨μ, hμ, hA.2⟩

/-- A finite cover by three-AP-free sets gives a finite coloring with no monochromatic three-AP. -/
lemma not_finite_threeAPFree_cover {A : Set ℕ} [Infinite A]
    (hRamsey : RamseyForThreeAP A) :
    ¬ ∃ n, ∃ S : Fin n → Set ℕ,
      (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i := by
  rintro ⟨n, S, hfree, hcover⟩
  have hn : 0 < n := by
    by_contra hnpos
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnpos
    subst n
    have hAempty : A = ∅ := by simpa using hcover
    have hAfin : A.Finite := by simp [hAempty]
    exact (Set.infinite_coe_iff.mp (inferInstance : Infinite A)) hAfin
  have hindex : ∀ x ∈ A, ∃ i : Fin n, x ∈ S i := by
    intro x hx
    rw [hcover] at hx
    exact Set.mem_iUnion.mp hx
  let color : ℕ → Fin n := fun x =>
    if hx : x ∈ A then Classical.choose (hindex x hx) else ⟨0, hn⟩
  have color_mem : ∀ {x : ℕ}, x ∈ A → x ∈ S (color x) := by
    intro x hx
    simp only [color, dif_pos hx]
    exact Classical.choose_spec (hindex x hx)
  obtain ⟨a, ha, b, hb, c, hc, habc, hac, hab, hbc⟩ := hRamsey n hn color
  have haS : a ∈ S (color a) := color_mem ha
  have hbS : b ∈ S (color a) := by simpa [hab] using color_mem hb
  have hcS : c ∈ S (color a) := by simpa [hab, hbc] using color_mem hc
  have := (threeAPFree_iff_eq_right.mp (hfree (color a))) haS hbS hcS habc
  exact hac this

/-- Once the RRS set has been constructed, it refutes the literal upstream universal statement. -/
lemma negative_answer_of_counterexample {A : Set ℕ} [Infinite A] {μ : ℝ} (hμ : 0 < μ)
    (hA : IsRRSCounterexample A μ) :
    ¬ (∀ X : Set ℕ, Infinite X → HasFew3APs X →
      ∃ n, ∃ S : Fin n → Set ℕ,
        (∀ i, ThreeAPFree (S i)) ∧ X = ⋃ i : Fin n, S i) := by
  intro h
  exact not_finite_threeAPFree_cover hA.1
    (h A (inferInstance : Infinite A) (hasFew3APs_of_isRRSCounterexample hμ hA))

/-- Erdős Problem 847 has a negative answer.  The witness is the separated
union of the finite RRS blocks constructed above the sparse Hales--Jewett
line systems. -/
theorem erdos_847 :
    ¬ ∀ A : Set ℕ, Infinite A → HasFew3APs A →
      ∃ n, ∃ S : Fin n → Set ℕ,
        (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i := by
  intro hcover
  obtain ⟨A, hAinfinite, hA⟩ :=
    Erdos847Construction.exists_counterexample
  letI : Infinite A := Set.infinite_coe_iff.mpr hAinfinite
  have hA' : IsRRSCounterexample A (1 / 3 : ℝ) := by
    exact hA
  exact (negative_answer_of_counterexample (by norm_num) hA') hcover

end Erdos847
