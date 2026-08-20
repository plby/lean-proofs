import ErdosProblems.Erdos746.Model
import ErdosProblems.Erdos543.Model
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A direct finite Bernoulli expansion calculation

This module develops the finite weighted-subset model used in the first
exposure argument.  Keeping the calculation finite has two advantages: no
measurability side conditions are needed, and the relation with the uniform
fixed-size layers is an exact finite identity.
-/

open scoped BigOperators
open Filter

namespace Erdos746

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Bernoulli weight of a subset of a finite universe. -/
def subsetBernoulliWeight {α : Type*} (U A : Finset α) (p : ℝ) : ℝ :=
  p ^ A.card * (1 - p) ^ (U.card - A.card)

/-- Finite Bernoulli probability of an event on subsets of `U`. -/
def subsetBernoulliProbability {α : Type*} [DecidableEq α]
    (U : Finset α) (p : ℝ) (P : Finset α → Prop) : ℝ :=
  ∑ A ∈ U.powerset with P A, subsetBernoulliWeight U A p

theorem subsetBernoulliWeight_nonneg {α : Type*} {U A : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ subsetBernoulliWeight U A p := by
  unfold subsetBernoulliWeight
  positivity

/-- The finite Bernoulli weights on all subsets sum to one. -/
theorem sum_subsetBernoulliWeight {α : Type*} [DecidableEq α]
    (U : Finset α) (p : ℝ) :
    (∑ A ∈ U.powerset, subsetBernoulliWeight U A p) = 1 := by
  calc
    (∑ A ∈ U.powerset, subsetBernoulliWeight U A p) =
        ∑ A ∈ U.powerset,
          (∏ _x ∈ A, p) * ∏ _x ∈ U \ A, (1 - p) := by
            apply Finset.sum_congr rfl
            intro A hA
            have hAU : A ⊆ U := Finset.mem_powerset.mp hA
            simp [subsetBernoulliWeight,
              Finset.card_sdiff_of_subset hAU]
    _ = ∏ _x ∈ U, (p + (1 - p)) :=
      (Finset.prod_add (fun _ : α ↦ p) (fun _ ↦ 1 - p) U).symm
    _ = 1 := by simp

theorem subsetBernoulliProbability_nonneg {α : Type*} [DecidableEq α]
    (U : Finset α) {p : ℝ} (P : Finset α → Prop)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ subsetBernoulliProbability U p P := by
  unfold subsetBernoulliProbability
  exact Finset.sum_nonneg fun A hA ↦
    subsetBernoulliWeight_nonneg hp0 hp1

theorem subsetBernoulliProbability_le_one {α : Type*} [DecidableEq α]
    (U : Finset α) {p : ℝ} (P : Finset α → Prop)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    subsetBernoulliProbability U p P ≤ 1 := by
  rw [← sum_subsetBernoulliWeight U p]
  unfold subsetBernoulliProbability
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro A hA _
    exact subsetBernoulliWeight_nonneg hp0 hp1

/-- Complement rule for the finite Bernoulli model. -/
theorem subsetBernoulliProbability_compl {α : Type*} [DecidableEq α]
    (U : Finset α) {p : ℝ} (P : Finset α → Prop) :
    subsetBernoulliProbability U p (fun A ↦ ¬ P A) =
      1 - subsetBernoulliProbability U p P := by
  classical
  unfold subsetBernoulliProbability
  rw [Finset.sum_filter, Finset.sum_filter,
    ← sum_subsetBernoulliWeight U p, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hP : P A <;> simp [hP]

/-- Density of an event on one fixed cardinality layer. -/
def directLayerProbability {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ) : ℝ :=
  (((U.powersetCard k).filter P).card : ℝ) / U.card.choose k

/-- The usual binomial mass, kept local to the direct finite model. -/
def directBinomialTerm (N k : ℕ) (p : ℝ) : ℝ :=
  (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)

/-- Exact mixture identity: a Bernoulli subset is obtained by first choosing
its cardinality and then choosing a uniform subset on that layer. -/
theorem subsetBernoulliProbability_eq_sum_layers
    {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
    (P : Finset α → Prop) :
    subsetBernoulliProbability U p P =
      ∑ k ∈ Finset.range (U.card + 1),
        directBinomialTerm U.card k p * directLayerProbability U P k := by
  classical
  have hfiltered : subsetBernoulliProbability U p P =
      ∑ A ∈ U.powerset,
        if P A then subsetBernoulliWeight U A p else 0 := by
    unfold subsetBernoulliProbability
    rw [Finset.sum_filter]
  rw [hfiltered, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro k hk
  have hkU : k ≤ U.card := by
    simpa using (Finset.mem_range.mp hk)
  have hchoose : (U.card.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hkU))
  have hcard : ∀ A ∈ U.powersetCard k, A.card = k :=
    fun A hA ↦ (Finset.mem_powersetCard.mp hA).2
  rw [show (∑ A ∈ U.powersetCard k,
      if P A then subsetBernoulliWeight U A p else 0) =
      (((U.powersetCard k).filter P).card : ℝ) *
        (p ^ k * (1 - p) ^ (U.card - k)) by
        calc
          (∑ A ∈ U.powersetCard k,
              if P A then subsetBernoulliWeight U A p else 0) =
              ∑ A ∈ (U.powersetCard k).filter P,
                subsetBernoulliWeight U A p := by
                  rw [Finset.sum_filter]
          _ = ∑ _A ∈ (U.powersetCard k).filter P,
                (p ^ k * (1 - p) ^ (U.card - k)) := by
                  apply Finset.sum_congr rfl
                  intro A hA
                  simp only [Finset.mem_filter] at hA
                  simp [subsetBernoulliWeight, hcard A hA.1]
          _ = (((U.powersetCard k).filter P).card : ℝ) *
                (p ^ k * (1 - p) ^ (U.card - k)) := by simp]
  unfold directBinomialTerm directLayerProbability
  field_simp

theorem directLayerProbability_mono_succ
    {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    (hk : k < U.card) :
    directLayerProbability U P k ≤ directLayerProbability U P (k + 1) := by
  have hcount := Erdos543.Model.extension_count_le_marked_count U P k hP
  have hchoose : U.card.choose (k + 1) * (k + 1) =
      U.card.choose k * (U.card - k) := Nat.choose_succ_right_eq _ _
  have hdenk : 0 < (U.card.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hk)
  have hdenk1 : 0 < (U.card.choose (k + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  rw [directLayerProbability, directLayerProbability,
    div_le_div_iff₀ hdenk hdenk1]
  simp only [Erdos543.Model.goodSets] at hcount
  norm_cast at hcount hchoose ⊢
  nlinarith

theorem directLayerProbability_mono
    {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    {k m : ℕ} (hkm : k ≤ m) (hm : m ≤ U.card) :
    directLayerProbability U P k ≤ directLayerProbability U P m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  clear hkm
  revert hm
  induction d with
  | zero =>
      intro _
      exact le_rfl
  | succ d ih =>
      intro hm
      have hprev : k + d ≤ U.card := by omega
      have hstep : k + d < U.card := by omega
      exact (ih hprev).trans
        (directLayerProbability_mono_succ U P (k + d) hP hstep)

theorem directLayerProbability_compl
    {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) {k : ℕ} (hk : k ≤ U.card) :
    directLayerProbability U (fun A ↦ ¬ P A) k =
      1 - directLayerProbability U P k := by
  classical
  have hchoose : (U.card.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk))
  have hcards := Finset.card_filter_add_card_filter_not
    (s := U.powersetCard k) P
  rw [Finset.card_powersetCard] at hcards
  have hcards' :
      ((U.powersetCard k).filter P).card +
        ((U.powersetCard k).filter (fun A ↦ ¬ P A)).card =
          U.card.choose k := by
    convert hcards using 1
    · ext A
      simp
  have hcardsR :
      (((U.powersetCard k).filter P).card : ℝ) +
        (((U.powersetCard k).filter (fun A ↦ ¬ P A)).card : ℝ) =
          (U.card.choose k : ℝ) := by
    exact_mod_cast hcards'
  unfold directLayerProbability
  field_simp
  linarith

def directBinomialLowerMass (N m : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), directBinomialTerm N k p

theorem directBinomialTerm_nonneg {N k : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ directBinomialTerm N k p := by
  unfold directBinomialTerm
  positivity

/-- Exact transfer inequality from the Bernoulli model to a fixed layer.
For an increasing event `P`, its failure density on layer `m`, multiplied by
the Bernoulli mass of all layers at most `m`, is bounded by its Bernoulli
failure probability. -/
theorem directLayer_failure_mul_lowerMass_le_bernoulli_failure
    {α : Type*} [DecidableEq α] (U : Finset α) {p : ℝ}
    (P : Finset α → Prop)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    {m : ℕ} (hm : m ≤ U.card) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    directLayerProbability U (fun A ↦ ¬ P A) m *
        directBinomialLowerMass U.card m p ≤
      subsetBernoulliProbability U p (fun A ↦ ¬ P A) := by
  rw [subsetBernoulliProbability_eq_sum_layers]
  unfold directBinomialLowerMass
  calc
    directLayerProbability U (fun A ↦ ¬ P A) m *
        (∑ k ∈ Finset.range (m + 1), directBinomialTerm U.card k p) =
        ∑ k ∈ Finset.range (m + 1),
          directBinomialTerm U.card k p *
            directLayerProbability U (fun A ↦ ¬ P A) m := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          directBinomialTerm U.card k p *
            directLayerProbability U (fun A ↦ ¬ P A) k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkU : k ≤ U.card := hkm.trans hm
      have hgood := directLayerProbability_mono U P hP hkm hm
      rw [directLayerProbability_compl U P hkU,
        directLayerProbability_compl U P hm]
      exact mul_le_mul_of_nonneg_left (by linarith)
        (directBinomialTerm_nonneg hp0 hp1)
    _ ≤ ∑ k ∈ Finset.range (U.card + 1),
          directBinomialTerm U.card k p *
            directLayerProbability U (fun A ↦ ¬ P A) k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right hm 1)
      · intro k hk _
        exact mul_nonneg (directBinomialTerm_nonneg hp0 hp1)
          (by
            unfold directLayerProbability
            positivity)

end

end Erdos746
