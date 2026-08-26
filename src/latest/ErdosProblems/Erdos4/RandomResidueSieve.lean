import ErdosProblems.Erdos4.ExposureBounds
import ErdosProblems.Erdos4.Base

/-!
# Exact probabilities for the preliminary random residue sieve

One residue is chosen independently at each sieve prime. This file gives
the exact survival product for an arbitrary finite set, and the exact
conditional product after a distinguished target has survived. No
independence of the different integers is asserted.
-/

open scoped BigOperators

namespace Erdos4.RandomResidueSieve

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def residues (T : Finset ℕ) (l : P) : Finset (ZMod (ell l)) :=
  T.image (fun n : ℕ => (n : ZMod (ell l)))

def Survives (a : ∀ l, ZMod (ell l)) (T : Finset ℕ) : Prop :=
  ∀ l, a l ∉ residues ell T l

theorem survives_union (a : ∀ l, ZMod (ell l)) (T U : Finset ℕ) :
    Survives ell a (T ∪ U) ↔ Survives ell a T ∧ Survives ell a U := by
  simp only [Survives, residues, Finset.image_union, Finset.mem_union, not_or, forall_and]

theorem survives_singleton (a : ∀ l, ZMod (ell l)) (q : ℕ) :
    Survives ell a {q} ↔ ∀ l, a l ≠ (q : ZMod (ell l)) := by
  simp [Survives, residues]

theorem survives_insert (a : ∀ l, ZMod (ell l)) (q : ℕ) (T : Finset ℕ) :
    Survives ell a (insert q T) ↔ Survives ell a {q} ∧ Survives ell a T := by
  rw [← Finset.singleton_union, survives_union]

noncomputable def weight (a : ∀ l, ZMod (ell l)) : ℝ := ∏ l, (ell l : ℝ)⁻¹

theorem weight_nonneg (a : ∀ l, ZMod (ell l)) : 0 ≤ weight ell a := by
  unfold weight
  positivity

theorem local_uniform_sum (l : P) :
    (∑ _a : ZMod (ell l), (ell l : ℝ)⁻¹) = 1 := by
  have hp : (ell l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : (ell l).Prime).ne_zero
  simp [hp]

theorem sum_weight : (∑ a : ∀ l, ZMod (ell l), weight ell a) = 1 :=
  Erdos4.assignmentWeight_sum (fun l (_a : ZMod (ell l)) => (ell l : ℝ)⁻¹)
    (local_uniform_sum ell)

theorem sum_avoid (l : P) (S : Finset (ZMod (ell l))) :
    (∑ a : ZMod (ell l), if a ∉ S then (1 : ℝ) else 0) = ell l - S.card := by
  classical
  have hhit : (∑ a : ZMod (ell l), if a ∈ S then (1 : ℝ) else 0) = S.card := by simp
  have hsum : (∑ a : ZMod (ell l), if a ∉ S then (1 : ℝ) else 0) +
      (∑ a : ZMod (ell l), if a ∈ S then (1 : ℝ) else 0) = ell l := by
    rw [← Finset.sum_add_distrib]
    have hpoint (a : ZMod (ell l)) :
        (if a ∉ S then (1 : ℝ) else 0) + (if a ∈ S then (1 : ℝ) else 0) = 1 := by
      by_cases ha : a ∈ S <;> simp [ha]
    simp only [hpoint, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rw [hhit] at hsum
  linarith

noncomputable def survivalMass (T : Finset ℕ) : ℝ :=
  ∏ l, (1 - (residues ell T l).card / (ell l : ℝ))

open Classical in
theorem survivalMass_eq (T : Finset ℕ) :
    (∑ a : ∀ l, ZMod (ell l), if Survives ell a T then weight ell a else 0) =
      survivalMass ell T := by
  classical
  unfold Survives weight survivalMass
  trans ∏ l, ∑ a : ZMod (ell l), if a ∉ residues ell T l then (ell l : ℝ)⁻¹ else 0
  · convert Erdos4.independent_assignment_miss_mass
      (fun l (_a : ZMod (ell l)) => (ell l : ℝ)⁻¹)
      (fun l a => a ∉ residues ell T l) using 1
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : ∀ l, a l ∉ residues ell T l <;> simp [ha]
  apply Finset.prod_congr rfl
  intro l _hl
  have hp : (ell l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : (ell l).Prime).ne_zero
  calc
    (∑ a : ZMod (ell l), if a ∉ residues ell T l then (ell l : ℝ)⁻¹ else 0) =
        (∑ a : ZMod (ell l), if a ∉ residues ell T l then (1 : ℝ) else 0) * (ell l : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases ha : a ∈ residues ell T l <;> simp [ha]
    _ = (ell l - (residues ell T l).card) * (ell l : ℝ)⁻¹ := by rw [sum_avoid]
    _ = _ := by field_simp

theorem survivalMass_nonneg (T : Finset ℕ) : 0 ≤ survivalMass ell T := by
  classical
  rw [← survivalMass_eq]
  apply Finset.sum_nonneg
  intro a _ha
  split_ifs
  · exact weight_nonneg ell a
  · exact le_rfl

theorem survivalMass_singleton (q : ℕ) : survivalMass ell {q} = UnitFourier.unitDensity ell := by
  rw [UnitFourier.unitDensity_eq_product]
  simp [survivalMass, residues]

noncomputable def conditionalWeight (q : ℕ) (a : ∀ l, ZMod (ell l)) : ℝ := by
  classical
  exact if Survives ell a {q} then weight ell a / UnitFourier.unitDensity ell else 0

theorem conditionalWeight_nonneg (q : ℕ) (a : ∀ l, ZMod (ell l)) :
    0 ≤ conditionalWeight ell q a := by
  unfold conditionalWeight
  split_ifs
  · exact div_nonneg (weight_nonneg ell a) (UnitFourier.unitDensity_pos ell).le
  · exact le_rfl

open Classical in
theorem conditional_survivalMass (q : ℕ) (T : Finset ℕ) :
    (∑ a : ∀ l, ZMod (ell l), if Survives ell a T then conditionalWeight ell q a else 0) =
      survivalMass ell (insert q T) / UnitFourier.unitDensity ell := by
  classical
  rw [← survivalMass_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold conditionalWeight
  simp only [survives_insert]
  by_cases hq : Survives ell a {q} <;> by_cases hT : Survives ell a T <;> simp [hq, hT]

theorem sum_conditionalWeight (q : ℕ) :
    (∑ a : ∀ l, ZMod (ell l), conditionalWeight ell q a) = 1 := by
  have h := conditional_survivalMass ell q ∅
  have hpos := UnitFourier.unitDensity_pos ell
  simpa [Survives, residues, survivalMass_singleton, hpos.ne'] using h

end Erdos4.RandomResidueSieve
