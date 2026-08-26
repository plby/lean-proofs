import ErdosProblems.Erdos796.CanonicalExtension

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Multiplicative compatibility of the canonical extension

This file proves the multiplicative part of the canonical-extension lemma.
The proof classifies every factor as either an old cofactor at most the cutoff
or a newly adjoined prime above it.  An old--old product is controlled by the
given compatible prefix.  Any product involving a new prime determines its
unordered factor pair uniquely, so only the two orientations can occur.
-/

namespace Erdos796

/-- An old positive cofactor at cutoff `J`. -/
def IsOldAt (J x : ℕ) : Prop := 1 ≤ x ∧ x ≤ J

/-- A newly eligible prime at cutoff `J`. -/
def IsNewAt (J x : ℕ) : Prop := J < x ∧ x.Prime

theorem new_not_dvd_old {J p x : ℕ} (hp : IsNewAt J p) (hx : IsOldAt J x) :
    ¬p ∣ x := by
  rcases hp with ⟨hJp, hpPrime⟩
  rcases hx with ⟨hxPos, hxJ⟩
  intro hpx
  have hle : p ≤ x := Nat.le_of_dvd hxPos hpx
  omega

/-- If one factor is a new prime and both factors on the other side are
classified as old or new, equality of products determines the unordered
factor pair. -/
theorem eq_or_swap_of_new_left {J a b c d : ℕ}
    (ha : IsNewAt J a)
    (hc : IsOldAt J c ∨ IsNewAt J c)
    (hd : IsOldAt J d ∨ IsNewAt J d)
    (hprod : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hadvd : a ∣ c * d := ⟨b, hprod.symm⟩
  rcases ha.2.dvd_or_dvd hadvd with hac | had
  · rcases hc with hcOld | hcNew
    · exact (new_not_dvd_old ha hcOld hac).elim
    · have hacEq : a = c :=
        (Nat.prime_dvd_prime_iff_eq ha.2 hcNew.2).mp hac
      left
      refine ⟨hacEq, ?_⟩
      subst c
      exact Nat.eq_of_mul_eq_mul_left ha.2.pos hprod
  · rcases hd with hdOld | hdNew
    · exact (new_not_dvd_old ha hdOld had).elim
    · have hadEq : a = d :=
        (Nat.prime_dvd_prime_iff_eq ha.2 hdNew.2).mp had
      right
      refine ⟨hadEq, ?_⟩
      subst d
      exact Nat.eq_of_mul_eq_mul_left ha.2.pos
        (hprod.trans (Nat.mul_comm c a))

/-- If either member of the first pair is new, equality of two classified
products determines the pair up to swapping. -/
theorem eq_or_swap_of_has_new {J a b c d : ℕ}
    (hc : IsOldAt J c ∨ IsNewAt J c)
    (hd : IsOldAt J d ∨ IsNewAt J d)
    (habNew : IsNewAt J a ∨ IsNewAt J b)
    (hprod : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases habNew with haNew | hbNew
  · exact eq_or_swap_of_new_left haNew hc hd hprod
  · have hswap : b * a = c * d := by simpa [Nat.mul_comm] using! hprod
    rcases eq_or_swap_of_new_left hbNew hc hd hswap with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

/-- Every member of a canonical extension is either old or a new prime. -/
theorem mem_canonicalExtension_classify {J i x : ℕ} {U : ℕ → Finset ℕ}
    (hU : CompatiblePrefix J U)
    (hx : x ∈ canonicalExtension J U i) :
    IsOldAt J x ∨ IsNewAt J x := by
  by_cases hi : i ≤ J
  · rw [canonicalExtension_of_le hi] at hx
    have hxIcc := mem_positiveIcc.mp (hU.1 i hi hx)
    exact Or.inl ⟨hxIcc.1, hxIcc.2.trans hi⟩
  · rw [canonicalExtension_of_lt (Nat.lt_of_not_ge hi)] at hx
    rcases Finset.mem_union.mp hx with hxOld | hxNew
    · have hxIcc := mem_positiveIcc.mp (hU.1 J le_rfl hxOld)
      exact Or.inl hxIcc
    · exact Or.inr ⟨(mem_newPrimes.mp hxNew).1, (mem_newPrimes.mp hxNew).2.2⟩

/-- An extension member classified as old belongs to the original fiber at
the capped index `min i J`. -/
theorem mem_canonicalExtension_of_old {J i x : ℕ} {U : ℕ → Finset ℕ}
    (hx : x ∈ canonicalExtension J U i) (hxOld : IsOldAt J x) :
    x ∈ U (min i J) := by
  by_cases hi : i ≤ J
  · rw [canonicalExtension_of_le hi] at hx
    simpa [Nat.min_eq_left hi] using! hx
  · have hJi : J < i := Nat.lt_of_not_ge hi
    rw [canonicalExtension_of_lt hJi] at hx
    rcases Finset.mem_union.mp hx with hxBase | hxNew
    · simpa [Nat.min_eq_right hJi.le] using! hxBase
    · have hxgt : J < x := (mem_newPrimes.mp hxNew).1
      rcases hxOld with ⟨_, hxle⟩
      omega

/-- A product of two old factors cannot also be represented using a new
prime above the cutoff. -/
theorem old_product_forces_old {J a b x y : ℕ}
    (ha : IsOldAt J a) (hb : IsOldAt J b)
    (hx : IsOldAt J x ∨ IsNewAt J x)
    (hy : IsOldAt J y ∨ IsNewAt J y)
    (hprod : x * y = a * b) :
    IsOldAt J x ∧ IsOldAt J y := by
  constructor
  · rcases hx with hxOld | hxNew
    · exact hxOld
    · have hxdvd : x ∣ a * b := ⟨y, hprod.symm⟩
      rcases hxNew.2.dvd_or_dvd hxdvd with hxa | hxb
      · exact (new_not_dvd_old hxNew ha hxa).elim
      · exact (new_not_dvd_old hxNew hb hxb).elim
  · rcases hy with hyOld | hyNew
    · exact hyOld
    · have hydvd : y ∣ a * b :=
        ⟨x, hprod.symm.trans (Nat.mul_comm x y)⟩
      rcases hyNew.2.dvd_or_dvd hydvd with hya | hyb
      · exact (new_not_dvd_old hyNew ha hya).elim
      · exact (new_not_dvd_old hyNew hb hyb).elim

/-- The full canonical extension of a compatible prefix is compatible.  The
statement is valid even for cutoff zero, so no extra positivity hypothesis on
`J` is needed. -/
theorem compatible_canonicalExtension {J : ℕ} {U : ℕ → Finset ℕ}
    (hU : CompatiblePrefix J U) : Compatible (canonicalExtension J U) := by
  constructor
  · exact canonicalExtension_subset hU
  · intro i j m
    let R : Finset (ℕ × ℕ) :=
      ((canonicalExtension J U i).product (canonicalExtension J U j)).filter
        fun xy => xy.1 * xy.2 = m
    change R.card ≤ 2
    by_cases hOldRep : ∃ z ∈ R, IsOldAt J z.1 ∧ IsOldAt J z.2
    · rcases hOldRep with ⟨z, hzR, hzOld⟩
      let Rold : Finset (ℕ × ℕ) :=
        ((U (min i J)).product (U (min j J))).filter
          fun xy => xy.1 * xy.2 = m
      have hsubset : R ⊆ Rold := by
        intro w hwR
        have hw := Finset.mem_filter.mp hwR
        have hz := Finset.mem_filter.mp hzR
        have hwMem := Finset.mem_product.mp hw.1
        have hwClassLeft := mem_canonicalExtension_classify hU hwMem.1
        have hwClassRight := mem_canonicalExtension_classify hU hwMem.2
        have hwProd : w.1 * w.2 = z.1 * z.2 := hw.2.trans hz.2.symm
        have hwOld := old_product_forces_old hzOld.1 hzOld.2
          hwClassLeft hwClassRight hwProd
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hw.2⟩
        · exact mem_canonicalExtension_of_old hwMem.1 hwOld.1
        · exact mem_canonicalExtension_of_old hwMem.2 hwOld.2
      calc
        R.card ≤ Rold.card := Finset.card_le_card hsubset
        _ = productRepCount (U (min i J)) (U (min j J)) m := rfl
        _ ≤ 2 := hU.2 (min i J) (Nat.min_le_right _ _) (min j J)
          (Nat.min_le_right _ _) m
    · by_cases hR : R.Nonempty
      · let z : ℕ × ℕ := hR.choose
        have hzR : z ∈ R := hR.choose_spec
        have hz := Finset.mem_filter.mp hzR
        have hzMem := Finset.mem_product.mp hz.1
        have hzClassLeft := mem_canonicalExtension_classify hU hzMem.1
        have hzClassRight := mem_canonicalExtension_classify hU hzMem.2
        have hzNew : IsNewAt J z.1 ∨ IsNewAt J z.2 := by
          rcases hzClassLeft with hzOldLeft | hzNewLeft
          · rcases hzClassRight with hzOldRight | hzNewRight
            · exact (hOldRep ⟨z, hzR, hzOldLeft, hzOldRight⟩).elim
            · exact Or.inr hzNewRight
          · exact Or.inl hzNewLeft
        have hsubset : R ⊆ {z, (z.2, z.1)} := by
          intro w hwR
          have hw := Finset.mem_filter.mp hwR
          have hwMem := Finset.mem_product.mp hw.1
          have hwClassLeft := mem_canonicalExtension_classify hU hwMem.1
          have hwClassRight := mem_canonicalExtension_classify hU hwMem.2
          have hprod : z.1 * z.2 = w.1 * w.2 := hz.2.trans hw.2.symm
          rcases eq_or_swap_of_has_new hwClassLeft hwClassRight hzNew hprod with hEq | hSwap
          · have : w = z := by
              apply Prod.ext
              · exact hEq.1.symm
              · exact hEq.2.symm
            simp [this]
          · have : w = (z.2, z.1) := by
              apply Prod.ext
              · exact hSwap.2.symm
              · exact hSwap.1.symm
            simp [this]
        exact (Finset.card_le_card hsubset).trans Finset.card_le_two
      · simp [Finset.not_nonempty_iff_eq_empty.mp hR]

end Erdos796
