/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.LocalDensity

/-!
# Finite counting of simultaneous congruence classes

These lemmas isolate the elementary `interval length / modulus + endpoint
error` calculation repeatedly used in BNPZ Sections 7--10.
-/

namespace Erdos387

open scoped BigOperators

/-- Canonical simultaneous residue for two coprime moduli. -/
noncomputable def simultaneousResidue {M d : ℕ}
    (hcop : Nat.Coprime M d) (a b : ℕ) : ℕ :=
  Nat.chineseRemainder hcop a b

theorem simultaneousResidue_mod_left {M d : ℕ}
    (hcop : Nat.Coprime M d) (a b : ℕ) :
    simultaneousResidue hcop a b ≡ a [MOD M] :=
  (Nat.chineseRemainder hcop a b).prop.1

theorem simultaneousResidue_mod_right {M d : ℕ}
    (hcop : Nat.Coprime M d) (a b : ℕ) :
    simultaneousResidue hcop a b ≡ b [MOD d] :=
  (Nat.chineseRemainder hcop a b).prop.2

theorem simultaneousResidue_lt {M d : ℕ}
    (hcop : Nat.Coprime M d) (hM : 0 < M) (hd : 0 < d)
    (a b : ℕ) :
    simultaneousResidue hcop a b < M * d := by
  exact Nat.chineseRemainder_lt_mul hcop a b hM.ne' hd.ne'

/-- Members of a single combined class in `(L,U]`. -/
noncomputable def simultaneousClassIoc
    (L U M d a b : ℕ) (hcop : Nat.Coprime M d) : Finset ℕ :=
  modularPreimageIoc L U (M * d) {simultaneousResidue hcop a b}

theorem mem_simultaneousClassIoc_iff
    {L U M d a b n : ℕ} (hcop : Nat.Coprime M d)
    (hM : 0 < M) (hd : 0 < d) :
    n ∈ simultaneousClassIoc L U M d a b hcop ↔
      n ∈ Finset.Ioc L U ∧ n ≡ a [MOD M] ∧ n ≡ b [MOD d] := by
  classical
  let r := simultaneousResidue hcop a b
  have hr : r < M * d := simultaneousResidue_lt hcop hM hd a b
  constructor
  · intro hn
    rw [simultaneousClassIoc, modularPreimageIoc,
      Finset.mem_filter, Finset.mem_singleton] at hn
    have hnCombined : n ≡ r [MOD M * d] := by
      change n % (M * d) = r % (M * d)
      rw [Nat.mod_eq_of_lt hr]
      exact hn.2
    exact ⟨hn.1,
      (hnCombined.of_mul_right d).trans
        (simultaneousResidue_mod_left hcop a b),
      (hnCombined.of_mul_left M).trans
        (simultaneousResidue_mod_right hcop a b)⟩
  · rintro ⟨hnIoc, hnM, hnd⟩
    rw [simultaneousClassIoc, modularPreimageIoc,
      Finset.mem_filter, Finset.mem_singleton]
    refine ⟨hnIoc, ?_⟩
    have hnCombined : n ≡ r [MOD M * d] :=
      Nat.chineseRemainder_modEq_unique hcop hnM hnd
    exact Nat.mod_eq_of_modEq hnCombined hr

/-- A single simultaneous class has the expected elementary upper bound. -/
theorem card_simultaneousClassIoc_le
    {L U M d a b : ℕ} (hLU : L ≤ U) (hcop : Nat.Coprime M d)
    (hM : 0 < M) (hd : 0 < d) :
    ((simultaneousClassIoc L U M d a b hcop).card : ℝ) ≤
      ((U - L : ℕ) : ℝ) / (M * d : ℕ) + 2 := by
  have h := abs_card_modularPreimageIoc_sub_density
    hLU (Nat.mul_pos hM hd)
    ({simultaneousResidue hcop a b} : Finset ℕ)
    (by
      intro r hr
      rw [Finset.mem_singleton] at hr
      subst r
      exact simultaneousResidue_lt hcop hM hd a b)
  have hupper := (abs_le.mp h).2
  simpa [simultaneousClassIoc, add_comm] using hupper

/-- Union bound for any finite family of single residue classes. -/
theorem card_biUnion_modularPreimageIoc_le
    {I : Type*} [DecidableEq I] {L U : ℕ} (hLU : L ≤ U)
    (T : Finset I) (q r : I → ℕ)
    (hq : ∀ i ∈ T, 0 < q i) (hr : ∀ i ∈ T, r i < q i) :
    (((T.biUnion fun i =>
        modularPreimageIoc L U (q i) {r i}).card : ℕ) : ℝ) ≤
      ∑ i ∈ T, (((U - L : ℕ) : ℝ) / q i + 2) := by
  have hcardNat :
      (T.biUnion fun i => modularPreimageIoc L U (q i) {r i}).card ≤
        ∑ i ∈ T, (modularPreimageIoc L U (q i) {r i}).card :=
    Finset.card_biUnion_le
  have hcardReal :
      (((T.biUnion fun i =>
          modularPreimageIoc L U (q i) {r i}).card : ℕ) : ℝ) ≤
        ∑ i ∈ T,
          ((modularPreimageIoc L U (q i) {r i}).card : ℝ) := by
    exact_mod_cast hcardNat
  refine hcardReal.trans (Finset.sum_le_sum fun i hi => ?_)
  have h := abs_card_modularPreimageIoc_sub_density
    hLU (hq i hi) ({r i} : Finset ℕ)
    (by
      intro a ha
      simp only [Finset.mem_singleton] at ha
      subst a
      exact hr i hi)
  have hupper := (abs_le.mp h).2
  simpa [add_comm] using hupper

end Erdos387
