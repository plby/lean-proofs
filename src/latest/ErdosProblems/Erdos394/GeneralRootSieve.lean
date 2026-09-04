import ErdosProblems.Erdos394.RootBoxUnitCRT
import ErdosProblems.Erdos394.RootSieve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fixed-modulus Brun aggregate for a general block length
-/

open Nat Finset

namespace Erdos394

noncomputable local instance zmodUnitsFintypeGeneralRootSieve (q : ℕ) :
    Fintype (ZMod q)ˣ := Fintype.ofFinite _

/-- `t_K(mq)` mass over positive, coprime, sifted quotients. -/
noncomputable def tKMulCoprimeSiftedMass
    (K : ℕ) (P : Finset ℕ) (M q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    if hm : 0 < m then
      if hcop : m.Coprime q then
        if badPrimeSet P m = ∅ then (t K (m * q) : ℝ) else 0
      else 0
    else 0

/-- Weighted sifted mass attached to an arbitrary nonnegative function on
unit residue classes. -/
noncomputable def unitWeightedSiftedMass
    (P : Finset ℕ) (M q : ℕ) (L : (ZMod q)ˣ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    if hm : 0 < m then
      if hcop : m.Coprime q then
        if badPrimeSet P m = ∅ then
          (m : ℝ) * L (ZMod.unitOfCoprime m hcop)
        else 0
      else 0
    else 0

/-- Partition an arbitrary unit-class weight into residue progressions. -/
theorem unitWeightedSiftedMass_eq_sum_units
    (P : Finset ℕ) (M q : ℕ) (hq : 0 < q)
    (L : (ZMod q)ˣ → ℝ) :
    unitWeightedSiftedMass P M q L =
      ∑ a : (ZMod q)ˣ,
        L a * siftedMass (residueClassUpTo M q (unitResidue q a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P) := by
  let : NeZero q := ⟨hq.ne'⟩
  let F : (ZMod q)ˣ → ℕ → ℝ := fun a m ↦
    if 0 < m ∧ badPrimeSet P m = ∅ then L a * (m : ℝ) else 0
  have hfilter : ∀ m : ℕ,
      (Finset.univ.filter (fun a : (ZMod q)ˣ ↦ unitResidue q a = m % q)) =
        if hcop : m.Coprime q then {ZMod.unitOfCoprime m hcop} else ∅ := by
    intro m
    split_ifs with hcop
    · ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact unitResidue_eq_mod_iff_eq_unitOfCoprime hq hcop a
    · ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hres
        exact (hcop (coprime_of_mod_eq_unitResidue hq a hres.symm)).elim
      · intro ha
        simp at ha
  have hpartition :
      (∑ a : (ZMod q)ˣ,
        ∑ m ∈ residueClassUpTo M q (unitResidue q a), F a m) =
      ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
    calc
      (∑ a : (ZMod q)ˣ,
        ∑ m ∈ residueClassUpTo M q (unitResidue q a), F a m) =
        ∑ a : (ZMod q)ˣ, ∑ m ∈ Finset.range (M + 1),
          if unitResidue q a = m % q then F a m else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        unfold residueClassUpTo
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro m hm
        by_cases h : m % q = unitResidue q a
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (Ne.symm h)]
      _ = ∑ m ∈ Finset.range (M + 1), ∑ a : (ZMod q)ˣ,
          if unitResidue q a = m % q then F a m else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ m ∈ Finset.range (M + 1),
          if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← Finset.sum_filter, hfilter m]
        split_ifs <;> simp
  have hnatural : unitWeightedSiftedMass P M q L =
      ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
    unfold unitWeightedSiftedMass
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmpos : 0 < m
    · rw [dif_pos hmpos]
      by_cases hcop : m.Coprime q
      · rw [dif_pos hcop, dif_pos hcop]
        by_cases hsift : badPrimeSet P m = ∅
        · rw [if_pos hsift]
          simp [F, hmpos, hsift]
          ring
        · rw [if_neg hsift]
          simp [F, hmpos, hsift]
      · rw [dif_neg hcop, dif_neg hcop]
    · rw [dif_neg hmpos]
      by_cases hcop : m.Coprime q
      · rw [dif_pos hcop]
        simp [F, hmpos]
      · rw [dif_neg hcop]
  rw [hnatural, ← hpartition]
  apply Finset.sum_congr rfl
  intro a ha
  unfold siftedMass F
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hsift : badPrimeSet P m = ∅
  · rw [if_pos hsift]
    by_cases hmpos : 0 < m
    · rw [if_pos ⟨hmpos, hsift⟩]
    · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
      subst m
      simp
  · rw [if_neg hsift]
    have hpair : ¬(0 < m ∧ badPrimeSet P m = ∅) := fun h ↦ hsift h.2
    rw [if_neg hpair]
    ring

/-- F-070 gives the pointwise root-weight majorant for every sifted quotient. -/
theorem tKMulCoprimeSiftedMass_le_unitLeastHit
    (K : ℕ) (S Q : Finset ℕ) (M : ℕ) (hK : 0 < K)
    (hQprime : ∀ p ∈ Q, p.Prime) :
    tKMulCoprimeSiftedMass K S M (primeProduct Q) ≤
      unitWeightedSiftedMass S M (primeProduct Q) (fun a ↦
        rootBoxTupleLeastHit Q K hK hQprime
          (globalUnitsRootBoxEquiv Q hQprime a)) := by
  unfold tKMulCoprimeSiftedMass unitWeightedSiftedMass
  apply Finset.sum_le_sum
  intro m hm
  by_cases hmpos : 0 < m
  · rw [dif_pos hmpos, dif_pos hmpos]
    by_cases hcop : m.Coprime (primeProduct Q)
    · rw [dif_pos hcop, dif_pos hcop]
      by_cases hsift : badPrimeSet S m = ∅
      · rw [if_pos hsift, if_pos hsift]
        have ht := t_le_mul_globalUnitLeastHit Q K m hK hmpos hQprime hcop
        have htR : (t K (m * primeProduct Q) : ℝ) ≤
            (m * rootBoxTupleLeastHit Q K hK hQprime
              (globalUnitsRootBoxEquiv Q hQprime
                (ZMod.unitOfCoprime m hcop)) : ℕ) := by
          exact_mod_cast ht
        push_cast at htR
        exact htR
      · rw [if_neg hsift, if_neg hsift]
    · rw [dif_neg hcop, dif_neg hcop]
  · rw [dif_neg hmpos, dif_neg hmpos]

/-- Complete fixed-selected-modulus Brun bound for a general block length.
The factor `W` is F-068's explicit linear polynomial in `|Q|`. -/
theorem tKMulCoprimeSiftedMass_le_brun
    (K Z : ℕ) (S Q : Finset ℕ) (M Rbrun : ℕ)
    (hK : 1 < K) (hZ : 1 ≤ Z) (hQ : 0 < Q.card)
    (hQprime : ∀ p ∈ Q, p.Prime)
    (hKp : ∀ p ∈ Q, K < p) (hK2p : ∀ p ∈ Q, K * K < p)
    (hlarge : ∀ p ∈ Q, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ Q, Z ≤ p) (hZ2p : ∀ p ∈ Q, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ Q, 2 * Q.card * K ^ Q.card ≤ p - 1)
    (hratSize : ∀ p ∈ Q, 4 * Q.card * K ≤ p - 1)
    (hZsize : 8 * Q.card * (K * K - 1) ≤ Z)
    (hRq : K ^ Q.card ≤ primeProduct Q)
    (hSprime : ∀ p ∈ S, p.Prime)
    (hcopS : ∀ p ∈ S, (primeProduct Q).Coprime p)
    (hR : Even Rbrun)
    (htail :
      (∑ p ∈ S, (1 / (p : ℝ))) ^ (Rbrun + 1) /
          ((Rbrun + 1).factorial : ℝ) ≤
        localEulerProduct S (fun p ↦ 1 / (p : ℝ))) :
    tKMulCoprimeSiftedMass K S M (primeProduct Q) ≤
      ((((M : ℝ) ^ 2 / (primeProduct Q : ℝ)) *
          localEulerProduct S (fun p ↦ 1 / (p : ℝ)) +
        (truncatedSubsets S Rbrun).card * (2 * (M : ℝ))) *
        (primeUnitCount Q : ℝ)) *
      ((2 + (Q.card : ℝ) *
        (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
          160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))) *
        ((primeProduct Q : ℝ) / ((K ^ Q.card : ℕ) : ℝ))) := by
  have hq : 0 < primeProduct Q := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hQprime p hp).pos
  let : NeZero (primeProduct Q) := ⟨hq.ne'⟩
  let L : (ZMod (primeProduct Q))ˣ → ℝ := fun a ↦
    rootBoxTupleLeastHit Q K (by omega) hQprime
      (globalUnitsRootBoxEquiv Q hQprime a)
  apply (tKMulCoprimeSiftedMass_le_unitLeastHit K S Q M
    (by omega) hQprime).trans
  rw [unitWeightedSiftedMass_eq_sum_units S M (primeProduct Q) hq L]
  let Xmain : ℝ := ((M : ℝ) ^ 2 / (primeProduct Q : ℝ)) *
    localEulerProduct S (fun p ↦ 1 / (p : ℝ)) +
      (truncatedSubsets S Rbrun).card * (2 * (M : ℝ))
  let W : ℝ := (2 + (Q.card : ℝ) *
    (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
      160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1)))
  have hL0 : ∀ a : (ZMod (primeProduct Q))ˣ, 0 ≤ L a := by
    intro a
    dsimp [L]
    positivity
  have hclass : ∀ a : (ZMod (primeProduct Q))ˣ,
      siftedMass (residueClassUpTo M (primeProduct Q)
        (unitResidue (primeProduct Q) a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet S) ≤ Xmain := by
    intro a
    have ha_lt : unitResidue (primeProduct Q) a < primeProduct Q :=
      ZMod.val_lt (a : ZMod (primeProduct Q))
    have hsieve := primeSiftedMass_le_two_product_add_error
      S hSprime (M := M) (q := primeProduct Q)
      (h := unitResidue (primeProduct Q) a) (R := Rbrun)
      hq ha_lt hcopS hR htail
    dsimp [Xmain]
    convert hsieve using 1 <;> ring
  have hsumL := normalized_sum_globalUnitLeastHit_le Q K Z hK hZ hQ
    hQprime hKp hK2p hlarge hZp hZ2p hareaSize hratSize hZsize hRq
  have hphi : (0 : ℝ) < primeUnitCount Q := by
    exact_mod_cast (show 0 < primeUnitCount Q by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have hp2 := (hQprime p hp).two_le
        omega)
  have hEuler0 : 0 ≤ localEulerProduct S (fun p ↦ 1 / (p : ℝ)) := by
    apply localEulerProduct_nonneg S (fun p ↦ 1 / (p : ℝ))
    · intro p hp
      positivity
    · intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hSprime p hp).one_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hSprime p hp).pos
      rw [div_le_iff₀ hp0]
      simpa using hp1
  have hsumL' : (∑ a : (ZMod (primeProduct Q))ˣ, L a) ≤
      (primeUnitCount Q : ℝ) *
        (W * ((primeProduct Q : ℝ) /
          ((K ^ Q.card : ℕ) : ℝ))) := by
    have hscaled := (div_le_iff₀ hphi).mp hsumL
    have htransport := sum_univ_fintype_independent
      (zmodUnitsFintypeGeneralRootSieve (primeProduct Q))
      (Erdos394.zmodUnitsFintypeCRT (primeProduct Q)) L
    have hcustom : (∑ a : (ZMod (primeProduct Q))ˣ, L a) ≤
        (2 + (Q.card : ℝ) *
          (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
            160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))) *
          ((primeProduct Q : ℝ) / ((K ^ Q.card : ℕ) : ℝ)) *
            (primeUnitCount Q : ℝ) := by
      rw [htransport]
      simpa [L] using hscaled
    dsimp [W]
    calc
      (∑ a : (ZMod (primeProduct Q))ˣ, L a) ≤
        (2 + (Q.card : ℝ) *
          (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
            160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))) *
          ((primeProduct Q : ℝ) / ((K ^ Q.card : ℕ) : ℝ)) *
            (primeUnitCount Q : ℝ) := hcustom
      _ = (primeUnitCount Q : ℝ) *
          ((2 + (Q.card : ℝ) *
            (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
              160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))) *
            ((primeProduct Q : ℝ) / ((K ^ Q.card : ℕ) : ℝ))) := by ring
  calc
    (∑ a : (ZMod (primeProduct Q))ˣ,
      L a * siftedMass (residueClassUpTo M (primeProduct Q)
        (unitResidue (primeProduct Q) a))
          (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet S)) ≤
        ∑ a : (ZMod (primeProduct Q))ˣ, L a * Xmain := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hclass a) (hL0 a)
    _ = Xmain * ∑ a : (ZMod (primeProduct Q))ˣ, L a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ Xmain * ((primeUnitCount Q : ℝ) *
        (W * ((primeProduct Q : ℝ) /
          ((K ^ Q.card : ℕ) : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left hsumL' (by
        dsimp [Xmain]
        positivity)
    _ = (Xmain * (primeUnitCount Q : ℝ)) *
        (W * ((primeProduct Q : ℝ) /
          ((K ^ Q.card : ℕ) : ℝ))) := by ring

end Erdos394
