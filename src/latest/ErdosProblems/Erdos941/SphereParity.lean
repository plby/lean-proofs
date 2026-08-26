import ErdosProblems.Erdos941.OrientedTrajectories

/-! # The parity classes needed by the two forms at 7 -/

namespace Erdos941

private theorem three_residues (A B C : ZMod 8) (h : A ^ 2 + B ^ 2 + C ^ 2 = 3) :
    A.val % 2 = 1 ∧ B.val % 2 = 1 ∧ C.val % 2 = 1 := by
  revert B C
  fin_cases A <;> decide

private theorem six_residues (A B C : ZMod 8) (h : A ^ 2 + B ^ 2 + C ^ 2 = 6) :
    (A.val % 4 = 2 ∧ B.val % 2 = 1 ∧ C.val % 2 = 1) ∨
    (B.val % 4 = 2 ∧ A.val % 2 = 1 ∧ C.val % 2 = 1) ∨
    (C.val % 4 = 2 ∧ A.val % 2 = 1 ∧ B.val % 2 = 1) := by
  revert B C
  fin_cases A <;> decide

theorem odd_coordinates_of_norm_three {v : Triple} (hv : tripleNorm v % 8 = 3) :
    v.1 % 2 = 1 ∧ v.2.1 % 2 = 1 ∧ v.2.2 % 2 = 1 := by
  have hcast : (v.1 : ZMod 8) ^ 2 + (v.2.1 : ZMod 8) ^ 2 + (v.2.2 : ZMod 8) ^ 2 = 3 := by
    have h := (ZMod.intCast_eq_intCast_iff' (tripleNorm v) 3 8).mpr (by simpa using hv)
    simpa only [tripleNorm, norm3, Int.cast_add, Int.cast_pow, Int.cast_ofNat] using h
  have h := three_residues v.1 v.2.1 v.2.2 hcast
  have hA := ZMod.val_intCast (n := 8) v.1
  have hB := ZMod.val_intCast (n := 8) v.2.1
  have hC := ZMod.val_intCast (n := 8) v.2.2
  omega

theorem coordinates_of_norm_six {v : Triple} (hv : tripleNorm v % 8 = 6) :
    (v.1 % 4 = 2 ∧ v.2.1 % 2 = 1 ∧ v.2.2 % 2 = 1) ∨
    (v.2.1 % 4 = 2 ∧ v.1 % 2 = 1 ∧ v.2.2 % 2 = 1) ∨
    (v.2.2 % 4 = 2 ∧ v.1 % 2 = 1 ∧ v.2.1 % 2 = 1) := by
  have hcast : (v.1 : ZMod 8) ^ 2 + (v.2.1 : ZMod 8) ^ 2 + (v.2.2 : ZMod 8) ^ 2 = 6 := by
    have h := (ZMod.intCast_eq_intCast_iff' (tripleNorm v) 6 8).mpr (by simpa using hv)
    simpa only [tripleNorm, norm3, Int.cast_add, Int.cast_pow, Int.cast_ofNat] using h
  have h := six_residues v.1 v.2.1 v.2.2 hcast
  have hA := ZMod.val_intCast (n := 8) v.1
  have hB := ZMod.val_intCast (n := 8) v.2.1
  have hC := ZMod.val_intCast (n := 8) v.2.2
  omega

def SphereParity (evenMiddle : Bool) (v : Triple) : Prop :=
  v.1 % 2 = 1 ∧ (if evenMiddle then v.2.1 % 4 = 2 else v.2.1 % 2 = 1) ∧
    (4 : ℤ) ∣ v.2.2 - v.1

instance (b : Bool) (v : Triple) : Decidable (SphereParity b v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem SphereParity.rotate {b : Bool} {v : Triple} (h : SphereParity b v)
    {a : Axis} (ha : Admissible a v) : SphereParity b (Erdos941.rotate a v) := by
  cases b with
  | false =>
    obtain ⟨hA, hB, hCA⟩ := h
    change v.2.1 % 2 = 1 at hB
    have hC : v.2.2 % 2 = 1 := by omega
    obtain ⟨hx, hy, hz⟩ := rotate_all_odd_mod_four ha hA hB hC
    change (Erdos941.rotate a v).1 % 2 = 1 ∧ (Erdos941.rotate a v).2.1 % 2 = 1 ∧
      (4 : ℤ) ∣ (Erdos941.rotate a v).2.2 - (Erdos941.rotate a v).1
    omega
  | true => exact rotate_preserves_fourteen_parity ha h.1 h.2.1 h.2.2

theorem SphereParity.centeredState {b : Bool} {s : OrientedTriple}
    (h : SphereParity b s.1.2) (L i : ℕ) : SphereParity b (centeredState L s i).1.2 := by
  have hback (k : ℕ) : SphereParity b (orientedStep.symm^[k] s).1.2 := by
    induction k with
    | zero => exact h
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.rotate (orientedStep.symm^[k] s).2.2
  have hforward (k : ℕ) : SphereParity b (orientedStep^[k] (orientedStep.symm^[L] s)).1.2 := by
    induction k with
    | zero => exact hback L
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.rotate (nextAxis_admissible _)
  exact hforward i

end Erdos941
