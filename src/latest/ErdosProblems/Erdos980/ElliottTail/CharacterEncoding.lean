/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Character encoding of power residues

This file isolates the finite cyclic-group input used in Elliott's treatment of
least `k`-th power nonresidues.  For a prime `p`, the subgroup of complex
Dirichlet characters annihilating the `k`-th powers in `(ZMod p)ˣ` is the dual
of the quotient by the power subgroup.  When `k ∣ p - 1`, that dual subgroup
has cardinality `k` and has a generator of exact order `k`.  The generator is
equal to one precisely on the `k`-th powers.

The final section records the elementary smooth-number consequence: a
multiplicative function which is one on all primes at most `y` is one on every
positive `(y + 1)`-smooth number.
-/

namespace Erdos980

open scoped BigOperators

/-- The subgroup of complex characters modulo `p` that are trivial on all
`k`-th powers in `(ZMod p)ˣ`. -/
noncomputable def powerResidueCharacters (p k : ℕ) :
    Subgroup (DirichletCharacter ℂ p) :=
  DirichletCharacter.annihilator ℂ
    ((powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range : Set (ZMod p)ˣ)

/-- Membership in `powerResidueCharacters p k` means exactly that the
character is one on every `k`-th power unit. -/
theorem mem_powerResidueCharacters_iff {p k : ℕ}
    {χ : DirichletCharacter ℂ p} :
    χ ∈ powerResidueCharacters p k ↔ ∀ u : (ZMod p)ˣ, χ (u ^ k) = 1 := by
  rw [powerResidueCharacters, DirichletCharacter.mem_annihilator_iff]
  constructor
  · intro h u
    exact h (u ^ k) ⟨u, by simp⟩
  · rintro h _ ⟨u, rfl⟩
    simpa using h u

private theorem powerResidueCharacters_eq_dual {p k : ℕ} [NeZero p]
    (hp : p.Prime) :
    powerResidueCharacters p k =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ
        (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range).ofDual := by
  letI : Fact p.Prime := ⟨hp⟩
  ext χ
  rw [mem_powerResidueCharacters_iff,
    MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
  constructor
  · rintro h _ ⟨u, rfl⟩
    simpa using h u
  · intro h u
    exact h (u ^ k) ⟨u, by simp⟩

/-- If `p` is prime and `k ∣ p - 1`, the group of characters annihilating
the `k`-th powers has exactly `k` elements. -/
theorem natCard_powerResidueCharacters {p k : ℕ} (hp : p.Prime)
    (hdiv : k ∣ p - 1) :
    Nat.card (powerResidueCharacters p k) = k := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  rw [powerResidueCharacters_eq_dual hp,
    MulChar.card_subgroupOrderIsoSubgroupMulChar,
    ← Subgroup.index_eq_card,
    IsCyclic.index_powMonoidHom_range,
    Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient,
    Nat.totient_prime hp,
    Nat.gcd_eq_right_iff_dvd.mpr hdiv]

/-- The full kernel criterion for the power subgroup: a unit is a `k`-th
power iff every character trivial on `k`-th powers takes the value one there. -/
theorem mem_powMonoidHom_range_iff_forall_character {p k : ℕ}
    (hp : p.Prime) (u : (ZMod p)ˣ) :
    u ∈ (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range ↔
      ∀ χ : DirichletCharacter ℂ p,
        χ ∈ powerResidueCharacters p k → χ u = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let e := MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ
  change u ∈ (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range ↔ _
  have h := MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff
    (M := ZMod p) (R := ℂ) (X := powerResidueCharacters p k) (m := u)
  simpa [powerResidueCharacters_eq_dual hp, e] using h

/-- For a prime `p` and `k ∣ p - 1`, there is a complex Dirichlet character
of exact order `k` whose kernel on units is precisely the subgroup of `k`-th
powers. -/
theorem exists_dirichletCharacter_exactOrder_kernel_powRange
    {p k : ℕ} (hp : p.Prime) (hdiv : k ∣ p - 1) :
    ∃ χ : DirichletCharacter ℂ p,
      orderOf χ = k ∧
      ∀ u : (ZMod p)ˣ,
        χ u = 1 ↔ u ∈ (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  letI : IsCyclic (DirichletCharacter ℂ p) :=
    ((MulChar.mulEquiv_units (ZMod p) ℂ).some.isCyclic).mpr inferInstance
  let X := powerResidueCharacters p k
  obtain ⟨χ, hχgen⟩ := IsCyclic.exists_generator (α := X)
  refine ⟨χ, ?_, fun u ↦ ?_⟩
  · rw [Subgroup.orderOf_coe χ,
      orderOf_eq_card_of_forall_mem_zpowers hχgen,
      natCard_powerResidueCharacters hp hdiv]
  constructor
  · intro hχu
    apply (mem_powMonoidHom_range_iff_forall_character hp u).mpr
    intro ψ hψ
    obtain ⟨z, hz⟩ := hχgen ⟨ψ, hψ⟩
    have hz' : (χ : DirichletCharacter ℂ p) ^ z = ψ :=
      (X.subtype.map_zpow χ z).symm.trans (congrArg Subtype.val hz)
    rw [← hz']
    change ((χ : DirichletCharacter ℂ p) ^ z) u = 1
    rw [MulChar.zpow_apply_coe]
    rw [← MulChar.coe_toUnitHom, map_zpow]
    have hχu' : (χ : DirichletCharacter ℂ p).toUnitHom u = 1 :=
      Units.ext hχu
    rw [hχu', one_zpow]
    rfl
  · intro hu
    obtain ⟨v, rfl⟩ := hu
    exact mem_powerResidueCharacters_iff.mp χ.property v

/-- A monoid homomorphism which is one on every prime at most `y` is one on
every positive `(y + 1)`-smooth number. -/
theorem MonoidHom.eq_one_of_mem_smoothNumbers
    {M : Type*} [CommMonoid M] (f : ℕ →* M) {y n : ℕ}
    (hn : n ∈ Nat.smoothNumbers (y + 1))
    (hf : ∀ q : ℕ, q.Prime → q ≤ y → f q = 1) :
    f n = 1 := by
  rw [← Nat.prod_primeFactorsList hn.1, map_list_prod]
  apply List.prod_eq_one
  intro _ ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  exact hf q (Nat.prime_of_mem_primeFactorsList hq)
    (Nat.lt_succ_iff.mp (hn.2 q hq))

/-- Dirichlet-character specialization of
`MonoidHom.eq_one_of_mem_smoothNumbers`. -/
theorem DirichletCharacter.eq_one_of_mem_smoothNumbers
    {p y n : ℕ} (χ : DirichletCharacter ℂ p)
    (hn : n ∈ Nat.smoothNumbers (y + 1))
    (hχ : ∀ q : ℕ, q.Prime → q ≤ y → χ (q : ZMod p) = 1) :
    χ (n : ZMod p) = 1 := by
  let f : ℕ →* ℂ :=
    χ.toMonoidHom.comp (Nat.castRingHom (ZMod p)).toMonoidHom
  exact MonoidHom.eq_one_of_mem_smoothNumbers f hn hχ

end Erdos980
