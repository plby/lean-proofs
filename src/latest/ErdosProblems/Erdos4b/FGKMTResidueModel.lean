/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.Base

/-! # The exact finite independent uniform residue sieve -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def integerResidueIndex (p : ℕ) (n : ℤ) : ℕ := (n % (p : ℤ)).toNat

def occupiedResidues (p : ℕ) (N : Finset ℤ) : Finset ℕ := N.image (integerResidueIndex p)

theorem integerResidueIndex_lt {p : ℕ} (hp : 0 < p) (n : ℤ) :
    integerResidueIndex p n < p := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hlo := Int.emod_nonneg n hpZ.ne'
  have hhi := Int.emod_lt_of_pos n hpZ
  unfold integerResidueIndex
  omega

theorem integerResidueIndex_eq_iff {p : ℕ} (hp : 0 < p) (a b : ℤ) :
    integerResidueIndex p a = integerResidueIndex p b ↔ a ≡ b [ZMOD p] := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have ha := Int.emod_nonneg a hpZ.ne'
  have hb := Int.emod_nonneg b hpZ.ne'
  unfold integerResidueIndex Int.ModEq
  omega

theorem occupiedResidues_subset_range {p : ℕ} (hp : 0 < p) (N : Finset ℤ) :
    occupiedResidues p N ⊆ Finset.range p := by
  intro a ha
  obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_range.mpr (integerResidueIndex_lt hp n)

theorem occupiedResidues_card_le (p : ℕ) (N : Finset ℤ) :
    (occupiedResidues p N).card ≤ N.card := Finset.card_image_le

abbrev ResidueAssignment (S : Finset ℕ) := ∀ p : S, Fin p.val

def residueAssignmentMass (S : Finset ℕ) (_a : ResidueAssignment S) : ℝ :=
  ∏ p : S, 1 / (p.val : ℝ)

def residueAssignmentAvoids (S : Finset ℕ) (N : Finset ℤ) (a : ResidueAssignment S) : Prop :=
  ∀ p : S, (a p).val ∉ occupiedResidues p.val N

open scoped Classical in
def residueAvoidanceMass (S : Finset ℕ) (N : Finset ℤ) : ℝ :=
  ∑ a : ResidueAssignment S, if residueAssignmentAvoids S N a then residueAssignmentMass S a else 0

def residueSieveDensity (S : Finset ℕ) : ℝ := ∏ p ∈ S, (1 - 1 / (p : ℝ))

theorem residueAssignmentMass_nonneg (S : Finset ℕ) (a : ResidueAssignment S) :
    0 ≤ residueAssignmentMass S a := by
  exact Finset.prod_nonneg fun p _hp => by positivity

theorem residueAssignmentMass_sum {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) :
    (∑ a : ResidueAssignment S, residueAssignmentMass S a) = 1 := by
  apply assignmentWeight_sum (fun p : S => fun _a : Fin p.val => (1 : ℝ) / p.val)
  intro p
  have hp : (p.val : ℝ) ≠ 0 := by exact_mod_cast (hS p.val p.property).ne'
  simp [hp]

theorem uniform_residue_avoidance {p : ℕ} (hp : 0 < p) (N : Finset ℤ) :
    (∑ a : Fin p, if a.val ∉ occupiedResidues p N then (1 : ℝ) / p else 0) =
      1 - (occupiedResidues p N).card / (p : ℝ) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
    if a ∉ occupiedResidues p N then (1 : ℝ) / p else 0)]
  have hset : (Finset.range p).filter (fun a => a ∉ occupiedResidues p N) =
      Finset.range p \ occupiedResidues p N := by ext a; simp
  rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul,
    Finset.card_sdiff_of_subset (occupiedResidues_subset_range hp N), Finset.card_range]
  have hcard : (occupiedResidues p N).card ≤ p := by
    simpa only [Finset.card_range] using Finset.card_le_card (occupiedResidues_subset_range hp N)
  rw [Nat.cast_sub hcard]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

theorem residueAvoidanceMass_eq_prod {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p)
    (N : Finset ℤ) :
    residueAvoidanceMass S N = ∏ p ∈ S, (1 - (occupiedResidues p N).card / (p : ℝ)) := by
  classical
  unfold residueAvoidanceMass residueAssignmentAvoids residueAssignmentMass
  calc
    _ = ∏ p : S, ∑ a : Fin p.val,
        if a.val ∉ occupiedResidues p.val N then (1 : ℝ) / p.val else 0 := by
      convert independent_assignment_miss_mass
        (fun p : S => fun _a : Fin p.val => (1 : ℝ) / p.val)
        (fun p a => a.val ∉ occupiedResidues p.val N) using 1
      apply Finset.sum_congr rfl
      intro a _ha
      split_ifs <;> rfl
    _ = ∏ p : S, (1 - (occupiedResidues p.val N).card / (p.val : ℝ)) := by
      apply Finset.prod_congr rfl
      intro p _hp
      exact uniform_residue_avoidance (hS p.val p.property) N
    _ = _ := Finset.prod_coe_sort S (fun p : ℕ =>
      1 - (occupiedResidues p N).card / (p : ℝ))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.residueAssignmentMass_sum
#print axioms Erdos4b.FGKMT.residueAvoidanceMass_eq_prod
