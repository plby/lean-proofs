/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAffineEdges

/-!
# Within-family coprimality forced by the literal CRT system

For a positive compatible divisor quadruple, distinct residue roots
prevent a prime from dividing two coordinates in the same family.
The argument does not require a Maynard transform of the coefficients.
-/

namespace Erdos4b

noncomputable section

theorem firstRoot_eq_of_prime_dvd_forms {n a b q p : ℕ}
    (ha : p ∣ n + a * q) (hb : p ∣ n + b * q) :
    -((a * q : ℕ) : ZMod p) = -((b * q : ℕ) : ZMod p) := by
  have hmod : a * q ≡ b * q [MOD p] := Nat.ModEq.add_left_cancel' n
    ((Nat.modEq_zero_iff_dvd.mpr ha).trans (Nat.modEq_zero_iff_dvd.mpr hb).symm)
  exact congrArg Neg.neg ((ZMod.natCast_eq_natCast_iff _ _ p).mpr hmod)

theorem firstRoot_eq_of_prime_dvd_companion_forms {n a b m q p : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hpm : ¬p ∣ m)
    (ha : p ∣ m * (n + a * q) - 1) (hb : p ∣ m * (n + b * q) - 1) :
    -((a * q : ℕ) : ZMod p) = -((b * q : ℕ) : ZMod p) := by
  have hmA : 1 ≤ m * (n + a * q) := Nat.succ_le_iff.mpr (Nat.mul_pos hm (by omega))
  have hmB : 1 ≤ m * (n + b * q) := Nat.succ_le_iff.mpr (Nat.mul_pos hm (by omega))
  have hA : m * (n + a * q) ≡ 1 [MOD p] := by
    simpa only [Nat.sub_add_cancel hmA, Nat.zero_add] using
      (Nat.modEq_zero_iff_dvd.mpr ha).add_right 1
  have hB : m * (n + b * q) ≡ 1 [MOD p] := by
    simpa only [Nat.sub_add_cancel hmB, Nat.zero_add] using
      (Nat.modEq_zero_iff_dvd.mpr hb).add_right 1
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hpm
  have hmod := Nat.ModEq.cancel_left_of_coprime hcop (hA.trans hB.symm)
  have heq := Nat.ModEq.add_left_cancel' n hmod
  exact congrArg Neg.neg ((ZMod.natCast_eq_natCast_iff _ _ p).mpr heq)

theorem withinFamilyDivisorCoprime_of_compatible_roots
    (H : Finset ℕ) {m q : ℕ} (d : (H ⊕ H) → Bool → ℕ)
    (hm : 0 < m) (hdpos : ∀ i b, 0 < d i b)
    (hmE : ∀ j : H, m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true)))
    (hroots : ∀ p : ℕ, p.Prime → (∃ i b, p ∣ d i b) →
      Function.Injective (fun h : H ↦ -((h.val * q : ℕ) : ZMod p)))
    (hc : LargeGapCoordinateCrtCompatible H m q
      (fun i ↦ d (.inl i) false) (fun i ↦ d (.inr i) false)
      (fun i ↦ d (.inl i) true) (fun i ↦ d (.inr i) true)) :
    WithinFamilyDivisorCoprime d := by
  have hlcmpos (i : H ⊕ H) : 0 < Nat.lcm (d i false) (d i true) :=
    Nat.lcm_pos (hdpos i false) (hdpos i true)
  obtain ⟨n, hn, hfalse, htrue⟩ := exists_positive_largeGapDivisorConditions_of_coordinateCompatible
    hm (fun i ↦ hlcmpos (.inl i)) (fun i ↦ hlcmpos (.inr i)) hmE hc
  have hfirst (i : H) (b : Bool) : d (.inl i) b ∣ n + i.val * q := by
    cases b
    · exact (hfalse i).1
    · exact (htrue i).1
  have hcomp (i : H) (b : Bool) : d (.inr i) b ∣ m * (n + i.val * q) - 1 := by
    cases b
    · exact (hfalse i).2
    · exact (htrue i).2
  have hdivlcm (i : H ⊕ H) (b : Bool) : d i b ∣ Nat.lcm (d i false) (d i true) := by
    cases b
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_lcm_right _ _
  constructor
  · intro i j hij a b
    apply Nat.coprime_of_dvd
    intro p hp hpi hpj
    exact hij ((hroots p hp ⟨.inl i, a, hpi⟩)
      (firstRoot_eq_of_prime_dvd_forms (hpi.trans (hfirst i a)) (hpj.trans (hfirst j b))))
  · intro i j hij a b
    apply Nat.coprime_of_dvd
    intro p hp hpi hpj
    have hpm : ¬p ∣ m := hp.coprime_iff_not_dvd.mp
      ((hmE i).symm.coprime_dvd_left (hpi.trans (hdivlcm (.inr i) a)))
    exact hij ((hroots p hp ⟨.inr i, a, hpi⟩)
      (firstRoot_eq_of_prime_dvd_companion_forms hp hn hm hpm
        (hpi.trans (hcomp i a)) (hpj.trans (hcomp j b))))

theorem withinFamilyDivisorCoprime_preSieved_of_compatible
    {K w m q : ℕ} (d : (preSievedShifts K w ⊕ preSievedShifts K w) → Bool → ℕ)
    (hm : 0 < m) (hKw : K ≤ w) (hdpos : ∀ i b, 0 < d i b)
    (hwcop : ∀ i b, (primorial w).Coprime (d i b))
    (hqcop : ∀ i b, q.Coprime (d i b))
    (hmE : ∀ j : preSievedShifts K w,
      m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true)))
    (hc : LargeGapCoordinateCrtCompatible (preSievedShifts K w) m q
      (fun i ↦ d (.inl i) false) (fun i ↦ d (.inr i) false)
      (fun i ↦ d (.inl i) true) (fun i ↦ d (.inr i) true)) :
    WithinFamilyDivisorCoprime d := by
  apply withinFamilyDivisorCoprime_of_compatible_roots _ d hm hdpos hmE _ hc
  intro p hp hpactive
  obtain ⟨i, b, hpdiv⟩ := hpactive
  have hpw : w < p := by
    by_contra hn
    have hpdvd : p ∣ primorial w := hp.dvd_primorial_iff.mpr (by omega)
    exact hp.not_dvd_one ((Nat.dvd_gcd hpdvd hpdiv).trans (by rw [(hwcop i b).gcd_eq_one]))
  have hpq : ¬p ∣ q := hp.coprime_iff_not_dvd.mp ((hqcop i b).symm.coprime_dvd_left hpdiv)
  intro a c hac
  exact preSievedFirstResidueMap_injOn hp hKw hpw hpq (Set.mem_univ a) (Set.mem_univ c) hac

end

end Erdos4b
