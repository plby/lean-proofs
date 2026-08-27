/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentCrtClass
import Mathlib.Data.ZMod.Basic

/-!
# Reduced CRT classes of assigned nonzero prime roots

Only selected primes enter the period. The presieve residue and every
selected prime root are units, hence the assembled class is reduced.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α]

omit [Fintype α] in
theorem assignmentRootPair_iff_merged {p : α → ℕ}
    (z : ∀ q, ι → ZMod (p q)) (hinj : ∀ q, Function.Injective (z q))
    (d e : α → Option ι) (P : ℕ) :
    ((∀ q i, d q = some i → (P : ZMod (p q)) = z q i) ∧
      (∀ q i, e q = some i → (P : ZMod (p q)) = z q i)) ↔
      AssignmentCompatible d e ∧
        ∀ q i, mergeAssignment d e q = some i → (P : ZMod (p q)) = z q i := by
  constructor
  · rintro ⟨hd, he⟩
    refine ⟨?_, ?_⟩
    · intro q i l hdi hel
      exact hinj q ((hd q i hdi).symm.trans (he q l hel))
    · intro q i hqi
      rcases (mergeAssignment_some_iff d e q i).mp hqi with hdi | ⟨_, hei⟩
      · exact hd q i hdi
      · exact he q i hei
  · rintro ⟨hc, hm⟩
    exact ⟨fun q i hdi => hm q i (mergeAssignment_of_left hdi),
      fun q i hei => hm q i (mergeAssignment_of_right hc hei)⟩

theorem exists_assignment_reduced_class {W v : ℕ} (hW : 0 < W) (hv : v.Coprime W)
    {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hcop : ∀ q, (p q).Coprime W) (z : ∀ q, ι → ZMod (p q))
    (hz : ∀ q i, z q i ≠ 0) (r : α → Option ι) :
    ∃ c : ℕ, c < W * assignmentPrimeProduct p r ∧
      c.Coprime (W * assignmentPrimeProduct p r) ∧ ∀ P : ℕ,
      (P ≡ v [MOD W] ∧ ∀ q i, r q = some i → (P : ZMod (p q)) = z q i) ↔
        P ≡ c [MOD W * assignmentPrimeProduct p r] := by
  classical
  let d := assignmentPreSieveModulus W p r
  let a : Option α → ℕ := fun q => match q with
    | none => v
    | some q => match r q with
      | none => 0
      | some i => (z q i).val
  have hd (q : Option α) : 0 < d q :=
    assignmentPreSieveModulus_pos hW (fun q => (hp q).pos) r q
  have hpair : Pairwise (fun q s => (d q).Coprime (d s)) :=
    assignmentPreSieveModulus_pairwise hp hinj hcop r
  let crt := Nat.chineseRemainderOfFinset a d Finset.univ
    (fun q _ => (hd q).ne') (hpair.set_pairwise _)
  have hcrt (q : Option α) : crt.val ≡ a q [MOD d q] :=
    crt.property q (Finset.mem_univ q)
  have ha (q : Option α) : (a q).Coprime (d q) := by
    cases q with
    | none => exact hv
    | some q =>
        cases hr : r q with
        | none => simp [a, d, assignmentPreSieveModulus, hr]
        | some i =>
            have hval : ¬p q ∣ (z q i).val := by
              let : NeZero (p q) := ⟨(hp q).ne_zero⟩
              intro hdiv
              exact hz q i ((ZMod.natCast_zmod_val (z q i)).symm.trans
                ((ZMod.natCast_eq_zero_iff _ _).mpr hdiv))
            simpa only [a, d, assignmentPreSieveModulus, hr, Option.some_ne_none, if_false]
              using (((hp q).coprime_iff_not_dvd).mpr hval).symm
  have hperiod : (∏ q, d q) = W * assignmentPrimeProduct p r :=
    prod_assignmentPreSieveModulus W p r
  have hbound : crt.val < W * assignmentPrimeProduct p r := by
    rw [← hperiod]
    exact Nat.chineseRemainderOfFinset_lt_prod a d
      (fun q _ => (hd q).ne') (hpair.set_pairwise _)
  have hunit : crt.val.Coprime (W * assignmentPrimeProduct p r) := by
    rw [← hperiod]
    apply Nat.coprime_prod_right_iff.mpr
    intro q _hq
    change Nat.gcd crt.val (d q) = 1
    rw [(hcrt q).gcd_eq]
    exact ha q
  refine ⟨crt.val, hbound, hunit, ?_⟩
  intro P
  have hlocal :
      (P ≡ v [MOD W] ∧ ∀ q i, r q = some i → (P : ZMod (p q)) = z q i) ↔
        ∀ q, P ≡ a q [MOD d q] := by
    constructor
    · rintro ⟨hP, hroots⟩ q
      cases q with
      | none => exact hP
      | some q =>
          cases hr : r q with
          | none => simp [a, d, assignmentPreSieveModulus, hr, Nat.modEq_one]
          | some i =>
              let : NeZero (p q) := ⟨(hp q).ne_zero⟩
              have he : (P : ZMod (p q)) = ((z q i).val : ZMod (p q)) :=
                (hroots q i hr).trans (ZMod.natCast_zmod_val _).symm
              simpa only [a, d, assignmentPreSieveModulus, hr, Option.some_ne_none, if_false]
                using (ZMod.natCast_eq_natCast_iff _ _ _).mp he
    · intro hP
      refine ⟨hP none, ?_⟩
      intro q i hr
      let : NeZero (p q) := ⟨(hp q).ne_zero⟩
      have he : P ≡ (z q i).val [MOD p q] := by
        simpa only [a, d, assignmentPreSieveModulus, hr, Option.some_ne_none, if_false]
          using hP (some q)
      exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr he).trans (ZMod.natCast_zmod_val _)
  rw [hlocal, ← hperiod]
  have hprod := int_modEq_nat_prod_iff d hpair (P : ℤ) (crt.val : ℤ)
  simp only [Int.natCast_modEq_iff] at hprod
  rw [hprod]
  exact ⟨fun h q => (h q).trans (hcrt q).symm, fun h q => (h q).trans (hcrt q)⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_assignment_reduced_class
