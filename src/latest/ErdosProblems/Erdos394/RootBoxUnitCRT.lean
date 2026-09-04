import ErdosProblems.Erdos394.RootBoxCandidate
import ErdosProblems.Erdos394.UnitProgressions

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# CRT equivalence between global units and independent local-unit tuples
-/

open Nat Finset

namespace Erdos394

noncomputable local instance zmodUnitsFintypeCRT (q : ℕ) :
    Fintype (ZMod q)ˣ := Fintype.ofFinite _

noncomputable local instance rootBoxMultiplierTupleFintypeCRT
    (P : Finset ℕ) : Fintype (RootBoxMultiplierTuple P) := Fintype.ofFinite _

/-- Congruence modulo a finite product of distinct primes is equivalent to
congruence at every prime factor. -/
theorem modEq_primeProduct_iff
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (a b : ℕ) :
    a ≡ b [MOD primeProduct P] ↔ ∀ p ∈ P, a ≡ b [MOD p] := by
  induction P using Finset.induction_on with
  | empty =>
      simp only [primeProduct_empty]
      constructor
      · intro h p hp
        simp at hp
      · intro h
        exact Nat.modEq_one
  | @insert p P hpP ih =>
      have hp := hprime p (Finset.mem_insert_self p P)
      have hPprime : ∀ z ∈ P, z.Prime := by
        intro z hz
        exact hprime z (Finset.mem_insert_of_mem hz)
      have hcop : p.Coprime (primeProduct P) := by
        rw [hp.coprime_iff_not_dvd]
        intro hdiv
        rw [primeProduct] at hdiv
        obtain ⟨z, hz, hpz⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun z : ℕ ↦ z)).mp hdiv
        exact hpP (((Nat.prime_dvd_prime_iff_eq hp (hPprime z hz)).mp hpz) ▸ hz)
      rw [primeProduct_insert hpP,
        ← Nat.modEq_and_modEq_iff_modEq_mul hcop, ih hPprime]
      constructor
      · rintro ⟨hpab, hPab⟩ z hz
        rcases Finset.mem_insert.mp hz with rfl | hzP
        · exact hpab
        · exact hPab z hzP
      · intro hall
        exact ⟨hall p (Finset.mem_insert_self p P),
          fun z hz ↦ hall z (Finset.mem_insert_of_mem hz)⟩

/-- The least residue of a global unit is coprime to its modulus. -/
theorem unitResidue_coprime_modulus
    {q : ℕ} (hq : 0 < q) (u : (ZMod q)ˣ) :
    (unitResidue q u).Coprime q := by
  let : NeZero q := ⟨hq.ne'⟩
  apply coprime_of_mod_eq_unitResidue hq u
  exact Nat.mod_eq_of_lt (ZMod.val_lt (u : ZMod q))

/-- Natural reduction from a global unit modulo `∏P` to its tuple of local
units. -/
noncomputable def globalUnitToRootBoxTuple
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (ZMod (primeProduct P))ˣ → RootBoxMultiplierTuple P := by
  intro u p
  have hq : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun z hz ↦ (hprime z hz).pos
  have hpq : p.val ∣ primeProduct P :=
    (primeProduct_dvd_iff_all_dvd P hprime (primeProduct P)).mp
      (dvd_refl (primeProduct P)) p.val p.property
  have hcopq := unitResidue_coprime_modulus hq u
  exact ZMod.unitOfCoprime (unitResidue (primeProduct P) u)
    (Nat.Coprime.coprime_dvd_right hpq hcopq)

/-- The natural CRT map sends the global class of a coprime integer to its
ordinary reduction at every selected prime. -/
theorem globalUnitToRootBoxTuple_unitOfCoprime
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hcop : m.Coprime (primeProduct P)) (p : ↥P) :
    (globalUnitToRootBoxTuple P hprime
      (ZMod.unitOfCoprime m hcop) p : ZMod p.val) =
        (m : ZMod p.val) := by
  unfold globalUnitToRootBoxTuple
  rw [ZMod.coe_unitOfCoprime, unitResidue_unitOfCoprime hcop]
  apply (ZMod.natCast_eq_natCast_iff (m % primeProduct P) m p.val).mpr
  have hpq : p.val ∣ primeProduct P :=
    (primeProduct_dvd_iff_all_dvd P hprime (primeProduct P)).mp
      (dvd_refl (primeProduct P)) p.val p.property
  exact Nat.ModEq.of_dvd hpq (Nat.mod_modEq m (primeProduct P))

/-- The natural reduction map is injective. -/
theorem globalUnitToRootBoxTuple_injective
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Function.Injective (globalUnitToRootBoxTuple P hprime) := by
  classical
  have hq : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  let : NeZero (primeProduct P) := ⟨hq.ne'⟩
  intro u v huv
  have hall : ∀ p ∈ P,
      unitResidue (primeProduct P) u ≡
        unitResidue (primeProduct P) v [MOD p] := by
    intro p hp
    let pp : ↥P := ⟨p, hp⟩
    have huvP := congrFun huv pp
    have hz := congrArg (fun z : (ZMod p)ˣ ↦ (z : ZMod p)) huvP
    have hz' : (unitResidue (primeProduct P) u : ZMod p) =
        (unitResidue (primeProduct P) v : ZMod p) := by
      simpa [globalUnitToRootBoxTuple, ZMod.coe_unitOfCoprime] using hz
    exact (ZMod.natCast_eq_natCast_iff _ _ p).mp hz'
  have hmod := (modEq_primeProduct_iff P hprime
    (unitResidue (primeProduct P) u)
    (unitResidue (primeProduct P) v)).mpr hall
  have hres : unitResidue (primeProduct P) u =
      unitResidue (primeProduct P) v :=
    hmod.eq_of_lt_of_lt (ZMod.val_lt (u : ZMod (primeProduct P)))
      (ZMod.val_lt (v : ZMod (primeProduct P)))
  apply Units.ext
  apply ZMod.val_injective (primeProduct P)
  simpa [unitResidue] using hres

/-- Euler totient of a product of distinct primes. -/
theorem totient_primeProduct_eq_primeUnitCount
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (primeProduct P).totient = primeUnitCount P := by
  induction P using Finset.induction_on with
  | empty => simp [primeProduct, primeUnitCount]
  | @insert p P hpP ih =>
      have hp := hprime p (Finset.mem_insert_self p P)
      have hPprime : ∀ z ∈ P, z.Prime := by
        intro z hz
        exact hprime z (Finset.mem_insert_of_mem hz)
      have hcop : p.Coprime (primeProduct P) := by
        rw [hp.coprime_iff_not_dvd]
        intro hdiv
        rw [primeProduct] at hdiv
        obtain ⟨z, hz, hpz⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun z : ℕ ↦ z)).mp hdiv
        exact hpP (((Nat.prime_dvd_prime_iff_eq hp (hPprime z hz)).mp hpz) ▸ hz)
      rw [primeProduct_insert hpP, Nat.totient_mul hcop,
        Nat.totient_prime hp, ih hPprime]
      simp [primeUnitCount, hpP]

/-- The independent local-unit tuple type has cardinality `∏(p-1)`. -/
theorem natCard_rootBoxMultiplierTuple
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Nat.card (RootBoxMultiplierTuple P) = primeUnitCount P := by
  classical
  rw [Nat.card_pi]
  calc
    (∏ p : ↥P, Nat.card (ZMod p.val)ˣ) =
        ∏ p : ↥P, (p.val - 1) := by
      apply Fintype.prod_congr
      intro p
      let : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
      let : Fintype (ZMod p.val)ˣ := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime (hprime p.val p.property)]
    _ = primeUnitCount P := by
      simpa [primeUnitCount] using
        Finset.prod_coe_sort P (fun p : ℕ ↦ p - 1)

/-- Natural CRT equivalence on unit groups. -/
noncomputable def globalUnitsRootBoxEquiv
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (ZMod (primeProduct P))ˣ ≃ RootBoxMultiplierTuple P := by
  classical
  have hq : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  letI : NeZero (primeProduct P) := ⟨hq.ne'⟩
  letI : Fintype (ZMod (primeProduct P))ˣ := Fintype.ofFinite _
  letI : Fintype (RootBoxMultiplierTuple P) := Fintype.ofFinite _
  apply Equiv.ofBijective (globalUnitToRootBoxTuple P hprime)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact globalUnitToRootBoxTuple_injective P hprime
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      natCard_rootBoxMultiplierTuple P hprime, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient,
      totient_primeProduct_eq_primeUnitCount P hprime]

@[simp] theorem globalUnitsRootBoxEquiv_apply
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (u : (ZMod (primeProduct P))ˣ) :
    globalUnitsRootBoxEquiv P hprime u =
      globalUnitToRootBoxTuple P hprime u := rfl

/-- F-068 transported from local tuples to ordinary global unit classes. -/
theorem normalized_sum_globalUnitLeastHit_le
    (P : Finset ℕ) (K Z : ℕ) (hK : 1 < K)
    (hZ : 1 ≤ Z) (hP : 0 < P.card)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ P,
      2 * P.card * K ^ P.card ≤ p - 1)
    (hratSize : ∀ p ∈ P, 4 * P.card * K ≤ p - 1)
    (hZsize : 8 * P.card * (K * K - 1) ≤ Z)
    (hRq : K ^ P.card ≤ primeProduct P) :
    (∑ u : (ZMod (primeProduct P))ˣ,
      (rootBoxTupleLeastHit P K (by omega) hprime
        (globalUnitsRootBoxEquiv P hprime u) : ℝ)) /
        (primeUnitCount P : ℝ) ≤
      (2 + (P.card : ℝ) *
        (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
          160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))) *
        ((primeProduct P : ℝ) / ((K ^ P.card : ℕ) : ℝ)) := by
  have hmean := normalized_sum_rootBoxTupleLeastHit_le P K Z hK hZ hP
    hprime hKp hK2p hlarge hZp hZ2p hareaSize hratSize hZsize hRq
  have hsum := Equiv.sum_comp (globalUnitsRootBoxEquiv P hprime)
    (fun h : RootBoxMultiplierTuple P ↦
      (rootBoxTupleLeastHit P K (by omega) hprime h : ℝ))
  have hUniverse : rootBoxMultiplierUniverse P hprime =
      (Finset.univ : Finset (RootBoxMultiplierTuple P)) := by
    apply Finset.eq_univ_of_card
    rw [card_rootBoxMultiplierUniverse P hprime,
      ← Nat.card_eq_fintype_card,
      natCard_rootBoxMultiplierTuple P hprime]
  rw [hsum, ← hUniverse]
  exact hmean

/-- F-069 for the natural global unit class of `m`. -/
theorem t_le_mul_globalUnitLeastHit
    (P : Finset ℕ) (K m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcop : m.Coprime (primeProduct P)) :
    t K (m * primeProduct P) ≤ m *
      rootBoxTupleLeastHit P K hK hprime
        (globalUnitsRootBoxEquiv P hprime
          (ZMod.unitOfCoprime m hcop)) := by
  apply t_le_mul_rootBoxTupleLeastHit P K m hK hm hprime hcop
  intro p
  rw [globalUnitsRootBoxEquiv_apply]
  exact globalUnitToRootBoxTuple_unitOfCoprime P hprime m hcop p

end Erdos394
