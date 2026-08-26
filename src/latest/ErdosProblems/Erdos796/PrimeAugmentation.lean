import ErdosProblems.Erdos796.CanonicalExtension
import ErdosProblems.Erdos796.PruningArithmetic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Adjoining primes to a smooth compatible family

In the structural reduction, the cleaned cofactor fibres are `Z`-smooth.
The semiprime contribution is absorbed into the same finite model by adjoining
all primes in `(Z,j]` to the fibre at index `j`.  This file proves that this
operation preserves compatibility.

Unlike the canonical-extension construction, the old fibre is allowed to vary
with `j` and its members need not be at most `Z`.  Smoothness is the exact
replacement for that size bound: a prime larger than `Z` cannot divide an old
cofactor.
-/

namespace Erdos796

open PruningArithmetic

/-- A positive cofactor all of whose prime divisors are at most `Z`. -/
def IsSmoothAt (Z x : ℕ) : Prop :=
  1 ≤ x ∧ ZSmooth Z x

/-- A prime strictly above the smoothness cutoff. -/
def IsPrimeAbove (Z x : ℕ) : Prop :=
  Z < x ∧ x.Prime

/-- A prime above `Z` cannot divide a positive `Z`-smooth integer. -/
theorem primeAbove_not_dvd_smooth {Z p x : ℕ}
    (hp : IsPrimeAbove Z p) (hx : IsSmoothAt Z x) : ¬p ∣ x := by
  intro hpx
  have hle : p ≤ Z := hx.2 p hp.2 hpx
  exact (Nat.not_lt_of_ge hle) hp.1

/-- The fibre obtained by adjoining all eligible primes above `Z`. -/
def primeAugmentation (Z : ℕ) (S : ℕ → Finset ℕ) (j : ℕ) : Finset ℕ :=
  S j ∪ newPrimes Z j

@[simp]
theorem mem_primeAugmentation {Z j x : ℕ} {S : ℕ → Finset ℕ} :
    x ∈ primeAugmentation Z S j ↔ x ∈ S j ∨ x ∈ newPrimes Z j := by
  simp [primeAugmentation]

/-- Every augmented member is either an old smooth cofactor or a new prime. -/
theorem mem_primeAugmentation_classify
    {Z j x : ℕ} {S : ℕ → Finset ℕ}
    (hSrange : ∀ i, S i ⊆ positiveIcc i)
    (hSmooth : ∀ i, ∀ y ∈ S i, ZSmooth Z y)
    (hx : x ∈ primeAugmentation Z S j) :
    IsSmoothAt Z x ∨ IsPrimeAbove Z x := by
  rcases mem_primeAugmentation.mp hx with hxS | hxP
  · have hxpos := (mem_positiveIcc.mp (hSrange j hxS)).1
    exact Or.inl ⟨hxpos, hSmooth j x hxS⟩
  · have hp := mem_newPrimes.mp hxP
    exact Or.inr ⟨hp.1, hp.2.2⟩

/-- A classified smooth member of an augmented fibre was already old. -/
theorem mem_primeAugmentation_of_smooth
    {Z j x : ℕ} {S : ℕ → Finset ℕ}
    (hx : x ∈ primeAugmentation Z S j) (hxSmooth : IsSmoothAt Z x) :
    x ∈ S j := by
  rcases mem_primeAugmentation.mp hx with hxS | hxP
  · exact hxS
  · have hp := mem_newPrimes.mp hxP
    exfalso
    exact primeAbove_not_dvd_smooth ⟨hp.1, hp.2.2⟩ hxSmooth
      (dvd_refl x)

/-- If one factor is a new prime, equality determines the unordered pair. -/
theorem eq_or_swap_of_primeAbove_left {Z a b c d : ℕ}
    (ha : IsPrimeAbove Z a)
    (hc : IsSmoothAt Z c ∨ IsPrimeAbove Z c)
    (hd : IsSmoothAt Z d ∨ IsPrimeAbove Z d)
    (hprod : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hadvd : a ∣ c * d := ⟨b, hprod.symm⟩
  rcases ha.2.dvd_or_dvd hadvd with hac | had
  · rcases hc with hcSmooth | hcNew
    · exact (primeAbove_not_dvd_smooth ha hcSmooth hac).elim
    · have hacEq : a = c :=
        (Nat.prime_dvd_prime_iff_eq ha.2 hcNew.2).mp hac
      left
      refine ⟨hacEq, ?_⟩
      subst c
      exact Nat.eq_of_mul_eq_mul_left ha.2.pos hprod
  · rcases hd with hdSmooth | hdNew
    · exact (primeAbove_not_dvd_smooth ha hdSmooth had).elim
    · have hadEq : a = d :=
        (Nat.prime_dvd_prime_iff_eq ha.2 hdNew.2).mp had
      right
      refine ⟨hadEq, ?_⟩
      subst d
      exact Nat.eq_of_mul_eq_mul_left ha.2.pos
        (hprod.trans (Nat.mul_comm c a))

/-- If either member of the first pair is new, equality determines the pair
up to swapping. -/
theorem eq_or_swap_of_has_primeAbove {Z a b c d : ℕ}
    (hc : IsSmoothAt Z c ∨ IsPrimeAbove Z c)
    (hd : IsSmoothAt Z d ∨ IsPrimeAbove Z d)
    (habNew : IsPrimeAbove Z a ∨ IsPrimeAbove Z b)
    (hprod : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases habNew with haNew | hbNew
  · exact eq_or_swap_of_primeAbove_left haNew hc hd hprod
  · have hswap : b * a = c * d := by simpa [Nat.mul_comm] using! hprod
    rcases eq_or_swap_of_primeAbove_left hbNew hc hd hswap with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

/-- A product of two smooth factors cannot also use a prime above `Z`. -/
theorem smooth_product_forces_smooth {Z a b x y : ℕ}
    (ha : IsSmoothAt Z a) (hb : IsSmoothAt Z b)
    (hx : IsSmoothAt Z x ∨ IsPrimeAbove Z x)
    (hy : IsSmoothAt Z y ∨ IsPrimeAbove Z y)
    (hprod : x * y = a * b) :
    IsSmoothAt Z x ∧ IsSmoothAt Z y := by
  constructor
  · rcases hx with hxSmooth | hxNew
    · exact hxSmooth
    · have hxdvd : x ∣ a * b := ⟨y, hprod.symm⟩
      rcases hxNew.2.dvd_or_dvd hxdvd with hxa | hxb
      · exact (primeAbove_not_dvd_smooth hxNew ha hxa).elim
      · exact (primeAbove_not_dvd_smooth hxNew hb hxb).elim
  · rcases hy with hySmooth | hyNew
    · exact hySmooth
    · have hydvd : y ∣ a * b :=
        ⟨x, hprod.symm.trans (Nat.mul_comm x y)⟩
      rcases hyNew.2.dvd_or_dvd hydvd with hya | hyb
      · exact (primeAbove_not_dvd_smooth hyNew ha hya).elim
      · exact (primeAbove_not_dvd_smooth hyNew hb hyb).elim

/-- The augmented family remains fibrewise inside its index range. -/
theorem primeAugmentation_subset
    {Z : ℕ} {S : ℕ → Finset ℕ}
    (hSrange : ∀ j, S j ⊆ positiveIcc j) (j : ℕ) :
    primeAugmentation Z S j ⊆ positiveIcc j := by
  intro x hx
  rcases mem_primeAugmentation.mp hx with hxS | hxP
  · exact hSrange j hxS
  · have hp := mem_newPrimes.mp hxP
    exact mem_positiveIcc.mpr ⟨hp.2.2.one_le, hp.2.1⟩

/-- Adjoining every prime in `(Z,j]` preserves compatibility for a compatible
family of positive `Z`-smooth cofactors. -/
theorem compatible_primeAugmentation
    {Z : ℕ} {S : ℕ → Finset ℕ}
    (hS : Compatible S)
    (hSmooth : ∀ j, ∀ x ∈ S j, ZSmooth Z x) :
    Compatible (primeAugmentation Z S) := by
  constructor
  · exact primeAugmentation_subset hS.1
  · intro i j m
    let R : Finset (ℕ × ℕ) :=
      ((primeAugmentation Z S i).product
        (primeAugmentation Z S j)).filter fun xy => xy.1 * xy.2 = m
    change R.card ≤ 2
    by_cases hSmoothRep : ∃ z ∈ R, IsSmoothAt Z z.1 ∧ IsSmoothAt Z z.2
    · rcases hSmoothRep with ⟨z, hzR, hzSmooth⟩
      let Rold : Finset (ℕ × ℕ) :=
        ((S i).product (S j)).filter fun xy => xy.1 * xy.2 = m
      have hsubset : R ⊆ Rold := by
        intro w hwR
        have hw := Finset.mem_filter.mp hwR
        have hz := Finset.mem_filter.mp hzR
        have hwMem := Finset.mem_product.mp hw.1
        have hwClassLeft := mem_primeAugmentation_classify hS.1 hSmooth hwMem.1
        have hwClassRight := mem_primeAugmentation_classify hS.1 hSmooth hwMem.2
        have hwProd : w.1 * w.2 = z.1 * z.2 := hw.2.trans hz.2.symm
        have hwSmooth := smooth_product_forces_smooth hzSmooth.1 hzSmooth.2
          hwClassLeft hwClassRight hwProd
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hw.2⟩
        · exact mem_primeAugmentation_of_smooth hwMem.1 hwSmooth.1
        · exact mem_primeAugmentation_of_smooth hwMem.2 hwSmooth.2
      calc
        R.card ≤ Rold.card := Finset.card_le_card hsubset
        _ = productRepCount (S i) (S j) m := rfl
        _ ≤ 2 := hS.2 i j m
    · by_cases hR : R.Nonempty
      · let z : ℕ × ℕ := hR.choose
        have hzR : z ∈ R := hR.choose_spec
        have hz := Finset.mem_filter.mp hzR
        have hzMem := Finset.mem_product.mp hz.1
        have hzClassLeft := mem_primeAugmentation_classify hS.1 hSmooth hzMem.1
        have hzClassRight := mem_primeAugmentation_classify hS.1 hSmooth hzMem.2
        have hzNew : IsPrimeAbove Z z.1 ∨ IsPrimeAbove Z z.2 := by
          rcases hzClassLeft with hzSmoothLeft | hzNewLeft
          · rcases hzClassRight with hzSmoothRight | hzNewRight
            · exact (hSmoothRep ⟨z, hzR, hzSmoothLeft, hzSmoothRight⟩).elim
            · exact Or.inr hzNewRight
          · exact Or.inl hzNewLeft
        have hsubset : R ⊆ {z, (z.2, z.1)} := by
          intro w hwR
          have hw := Finset.mem_filter.mp hwR
          have hwMem := Finset.mem_product.mp hw.1
          have hwClassLeft := mem_primeAugmentation_classify hS.1 hSmooth hwMem.1
          have hwClassRight := mem_primeAugmentation_classify hS.1 hSmooth hwMem.2
          have hprod : z.1 * z.2 = w.1 * w.2 := hz.2.trans hw.2.symm
          rcases eq_or_swap_of_has_primeAbove hwClassLeft hwClassRight hzNew hprod with
            hEq | hSwap
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

/-- The old and new parts of an augmented fibre are disjoint. -/
theorem disjoint_smooth_newPrimes
    {Z j : ℕ} {S : ℕ → Finset ℕ}
    (hSrange : ∀ i, S i ⊆ positiveIcc i)
    (hSmooth : ∀ i, ∀ x ∈ S i, ZSmooth Z x) :
    Disjoint (S j) (newPrimes Z j) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxS hxP
  have hxpos := (mem_positiveIcc.mp (hSrange j hxS)).1
  have hp := mem_newPrimes.mp hxP
  exact primeAbove_not_dvd_smooth ⟨hp.1, hp.2.2⟩
    ⟨hxpos, hSmooth j x hxS⟩ (dvd_refl x)

/-- Exact cardinality of an augmented fibre. -/
theorem card_primeAugmentation
    {Z j : ℕ} {S : ℕ → Finset ℕ}
    (hSrange : ∀ i, S i ⊆ positiveIcc i)
    (hSmooth : ∀ i, ∀ x ∈ S i, ZSmooth Z x) :
    (primeAugmentation Z S j).card = (S j).card + (newPrimes Z j).card := by
  rw [primeAugmentation,
    Finset.card_union_of_disjoint (disjoint_smooth_newPrimes hSrange hSmooth)]

end Erdos796
