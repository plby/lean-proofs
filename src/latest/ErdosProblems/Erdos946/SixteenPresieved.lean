/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffine
import ErdosProblems.Erdos946.EightAffineCardinality

/-! # The fixed pre-sieved sixteen-form family -/

open scoped BigOperators

namespace Erdos946.SixteenPresieved

open SixteenAffine AffineSieve

noncomputable section

private theorem exists_large_bound (a : Fin 16 → ℕ) (c : ℕ) :
    ∃ z : ℕ, 272 ≤ z ∧ c ≤ z ∧ ∀ i, a i ≤ z := by
  refine ⟨272 + c + ∑ i, a i, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i
    have hi := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a j)) (Finset.mem_univ i)
    omega

private theorem exists_smallPrimeBound :
    ∃ z : ℕ, 272 ≤ z ∧ keyCommonMultiplier16 * affinePower16Product ≤ z ∧
      ∀ i, affineSlope16 i ≤ z :=
  exists_large_bound affineSlope16 (keyCommonMultiplier16 * affinePower16Product)

/-- A fixed finite bound, selected from a proved existence statement so
elaboration never needs to evaluate the very large CRT integers. -/
def smallPrimeBound : ℕ := Classical.choose exists_smallPrimeBound

private theorem smallPrimeBound_spec :
    272 ≤ smallPrimeBound ∧ keyCommonMultiplier16 * affinePower16Product ≤ smallPrimeBound ∧
      ∀ i, affineSlope16 i ≤ smallPrimeBound := Classical.choose_spec exists_smallPrimeBound

theorem smallPrimeBound_ge : 272 ≤ smallPrimeBound := smallPrimeBound_spec.1

theorem affineSlope_le_bound (i : Fin 16) : affineSlope16 i ≤ smallPrimeBound :=
  smallPrimeBound_spec.2.2 i

theorem not_dvd_core_of_bound_lt {p : ℕ} (_hp : p.Prime) (hpB : smallPrimeBound < p) :
    ¬p ∣ keyCommonMultiplier16 * affinePower16Product := by
  intro hdiv
  have hle := Nat.le_of_dvd (mul_pos keyCommonMultiplier16_pos affinePower16Product_pos) hdiv
  exact (not_lt_of_ge (hle.trans smallPrimeBound_spec.2.1)) hpB

def familySlope : Fin 16 → ℕ := preSievedSlope affineSlope16 smallPrimeBound

def familyConstant : Fin 16 → ℕ :=
  preSievedConstant affineSlope16 affineConstant16 affineForm16s_admissible smallPrimeBound

def originalParameter (n : ℕ) : ℕ :=
  smallPrimeBound.factorial * n + preSieveResidue affineForm16s_admissible smallPrimeBound

theorem family_form_identity (i : Fin 16) (n : ℕ) :
    familySlope i * n + familyConstant i = affineForm16 i (originalParameter n) := by
  exact preSieved_form_identity affineForm16s_admissible smallPrimeBound i n

theorem originalParameter_ge (n : ℕ) : n ≤ originalParameter n := by
  exact (Nat.le_mul_of_pos_left n (Nat.factorial_pos _)).trans (Nat.le_add_right _ _)

theorem familyConstant_pos (i : Fin 16) : 0 < familyConstant i :=
  Nat.add_pos_right _ (affineConstant16_pos i)

theorem familySlope_coprime {p : ℕ} (hp : p.Prime) (hpB : smallPrimeBound < p)
    (i : Fin 16) : (familySlope i).Coprime p :=
  preSievedSlope_coprime_of_lt affineSlope16_pos affineSlope_le_bound hp hpB i

theorem family_localNu {p : ℕ} (hp : p.Prime) (hpB : smallPrimeBound < p) :
    localNu familySlope familyConstant p = 16 := by
  exact preSieved_localNu_eq_card affineForm16s_admissible affineSlope16_pos
    affineSlope_le_bound hp hpB
    (affine_cross_not_modEq_of_not_dvd_commonCore16 hp (not_dvd_core_of_bound_lt hp hpB))

theorem small_prime_not_dvd_form (n p : ℕ) (hp : p.Prime) (hpB : p ≤ smallPrimeBound)
    (i : Fin 16) : ¬p ∣ familySlope i * n + familyConstant i :=
  not_dvd_preSievedForm_of_le affineForm16s_admissible hp hpB i n

theorem small_prime_not_dvd_product (n p : ℕ) (hp : p.Prime) (hpB : p ≤ smallPrimeBound) :
    ¬p ∣ affineProduct familySlope familyConstant n := by
  rw [prime_dvd_affineProduct_iff hp]
  rintro ⟨i, hi⟩
  exact small_prime_not_dvd_form n p hp hpB i hi

theorem cross_modEq_of_dvd_two_forms {a b c d n p : ℕ}
    (h₁ : p ∣ a * n + b) (h₂ : p ∣ c * n + d) : a * d ≡ c * b [MOD p] := by
  have h₁' := (Nat.modEq_zero_iff_dvd.mpr h₁).mul_left c
  have h₂' := (Nat.modEq_zero_iff_dvd.mpr h₂).mul_left a
  apply Nat.ModEq.add_left_cancel' (a * c * n)
  calc
    a * c * n + a * d = a * (c * n + d) := by ring
    _ ≡ a * 0 [MOD p] := h₂'
    _ = 0 := by simp
    _ ≡ c * 0 [MOD p] := Nat.ModEq.rfl
    _ ≡ c * (a * n + b) [MOD p] := h₁'.symm
    _ = a * c * n + c * b := by ring

theorem family_pairwise_coprime (n : ℕ) :
    Pairwise fun i j ↦ (familySlope i * n + familyConstant i).Coprime
      (familySlope j * n + familyConstant j) := by
  intro i j hij
  apply Nat.coprime_of_dvd
  intro p hp hi hj
  by_cases hpB : p ≤ smallPrimeBound
  · exact small_prime_not_dvd_form n p hp hpB i hi
  · have hdet := affine_cross_not_modEq_of_not_dvd_commonCore16 hp
      (not_dvd_core_of_bound_lt hp (by omega)) i j hij
    rw [family_form_identity] at hi hj
    exact hdet (cross_modEq_of_dvd_two_forms hi hj)

end

end Erdos946.SixteenPresieved
