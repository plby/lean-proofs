/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CollisionEquation
import ErdosProblems.Erdos851.LocalEulerProducts
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.ZMod.Basic

/-!
# Local data for the two-affine-form sieve

After a collision equation is divided by its common coefficient, one prime
variable is parameterized by an integer in an interval and two affine forms
must both be prime.  This file begins the checked Selberg-sieve
specialization by proving the key local fact: away from coefficients divisible
by the sieving prime, each affine form excludes at most one residue, so two
forms exclude at most two residues.
-/

namespace Erdos822

open scoped BigOperators

/-- The residue classes modulo `p` on which `a*r+s` vanishes. -/
def affineRootResidues (a s p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun r => p ∣ a * r + s

/-- The union of local bad classes for two affine forms. -/
def twoAffineBadResidues (a s b t p : ℕ) : Finset ℕ :=
  affineRootResidues a s p ∪ affineRootResidues b t p

@[simp]
theorem mem_affineRootResidues_iff {a s p r : ℕ} :
    r ∈ affineRootResidues a s p ↔ r < p ∧ p ∣ a * r + s := by
  simp [affineRootResidues]

@[simp]
theorem mem_twoAffineBadResidues_iff {a s b t p r : ℕ} :
    r ∈ twoAffineBadResidues a s b t p ↔
      (r < p ∧ p ∣ a * r + s) ∨ (r < p ∧ p ∣ b * r + t) := by
  simp [twoAffineBadResidues, mem_affineRootResidues_iff]

/-- If `p` does not divide the slope, an affine form has at most one root
modulo `p`. -/
theorem affineRootResidues_card_le_one_of_not_dvd {a s p : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) :
    (affineRootResidues a s p).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro r r' hr hr'
  rw [mem_affineRootResidues_iff] at hr hr'
  have hzero : a * r + s ≡ 0 [MOD p] := hr.2.modEq_zero_nat
  have hzero' : a * r' + s ≡ 0 [MOD p] := hr'.2.modEq_zero_nat
  have hsum : a * r + s ≡ a * r' + s [MOD p] := hzero.trans hzero'.symm
  have hmul : a * r ≡ a * r' [MOD p] :=
    Nat.ModEq.add_right_cancel' s hsum
  have hcop : Nat.gcd p a = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp (hp.coprime_iff_not_dvd.mpr hpa)
  have hrr' : r ≡ r' [MOD p] := hmul.cancel_left_of_coprime hcop
  have hmod : r % p = r' := Nat.mod_eq_of_modEq hrr' hr'.1
  simpa [Nat.mod_eq_of_lt hr.1] using hmod

/-- A slope invertible modulo `p` has a root for every constant term. -/
theorem affineRootResidues_nonempty_of_not_dvd {a s p : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) :
    (affineRootResidues a s p).Nonempty := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hcop : a.Coprime p := (hp.coprime_iff_not_dvd.mpr hpa).symm
  let z : ZMod p := -(s : ZMod p) * (a : ZMod p)⁻¹
  let r : ℕ := z.val
  have hrlt : r < p := by
    dsimp [r]
    exact ZMod.val_lt z
  have hz : (r : ZMod p) = z := by
    dsimp [r]
    exact ZMod.natCast_zmod_val z
  have hrootZ : (a * r + s : ZMod p) = 0 := by
    rw [hz]
    dsimp [z]
    rw [show (a : ZMod p) * (-(s : ZMod p) * (a : ZMod p)⁻¹) + s =
        -((a : ZMod p) * (a : ZMod p)⁻¹) * s + s by ring,
      ZMod.coe_mul_inv_eq_one a hcop]
    ring
  have hrootZ' : ((a * r + s : ℕ) : ZMod p) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hrootZ
  have hdiv : p ∣ a * r + s :=
    (ZMod.natCast_eq_zero_iff (a * r + s) p).mp hrootZ'
  exact ⟨r, mem_affineRootResidues_iff.mpr ⟨hrlt, hdiv⟩⟩

/-- Hence an invertible affine slope has exactly one root modulo `p`. -/
theorem affineRootResidues_card_eq_one_of_not_dvd {a s p : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) :
    (affineRootResidues a s p).card = 1 := by
  exact Nat.le_antisymm
    (affineRootResidues_card_le_one_of_not_dvd hp hpa)
    (Finset.card_pos.mpr (affineRootResidues_nonempty_of_not_dvd hp hpa))

/-- If the slope vanishes but the constant does not, the affine form has no
root modulo the prime. -/
theorem affineRootResidues_eq_empty_of_dvd_slope_not_constant
    {a s p : ℕ} (hpa : p ∣ a) (hps : ¬ p ∣ s) :
    affineRootResidues a s p = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨r, hr⟩
  rw [mem_affineRootResidues_iff] at hr
  have hrs : p ∣ s + a * r := by simpa [Nat.add_comm] using hr.2
  exact hps ((Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpa r)).mpr hrs)

/-- If the constant is nonzero modulo a prime, an affine form has at most
one root even when its slope is not assumed invertible. -/
theorem affineRootResidues_card_le_one_of_not_dvd_constant
    {a s p : ℕ} (hp : p.Prime) (hps : ¬ p ∣ s) :
    (affineRootResidues a s p).card ≤ 1 := by
  by_cases hpa : p ∣ a
  · rw [affineRootResidues_eq_empty_of_dvd_slope_not_constant hpa hps]
    simp
  · exact affineRootResidues_card_le_one_of_not_dvd hp hpa

/-- With both constants nonzero modulo p, two affine forms exclude at most
two classes without any slope-invertibility hypothesis. -/
theorem twoAffineBadResidues_card_le_two_of_not_dvd_constants
    {a s b t p : ℕ} (hp : p.Prime) (hps : ¬ p ∣ s) (hpt : ¬ p ∣ t) :
    (twoAffineBadResidues a s b t p).card ≤ 2 := by
  calc
    (twoAffineBadResidues a s b t p).card ≤
        (affineRootResidues a s p).card + (affineRootResidues b t p).card := by
      unfold twoAffineBadResidues
      exact Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (affineRootResidues_card_le_one_of_not_dvd_constant hp hps)
      (affineRootResidues_card_le_one_of_not_dvd_constant hp hpt)
    _ = 2 := by norm_num

/-- A common local root forces the prime to divide the affine determinant
`a*t - b*s`. -/
theorem int_dvd_affineDet_of_mem_both {a s b t p r : ℕ}
    (hra : r ∈ affineRootResidues a s p)
    (hrb : r ∈ affineRootResidues b t p) :
    (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s := by
  rw [mem_affineRootResidues_iff] at hra hrb
  obtain ⟨u, hu⟩ := hra.2
  obtain ⟨v, hv⟩ := hrb.2
  have huZ : (a : ℤ) * r + s = p * u := by exact_mod_cast hu
  have hvZ : (b : ℤ) * r + t = p * v := by exact_mod_cast hv
  refine ⟨(a : ℤ) * v - (b : ℤ) * u, ?_⟩
  calc
    (a : ℤ) * t - (b : ℤ) * s =
        (a : ℤ) * ((b : ℤ) * r + t) -
          (b : ℤ) * ((a : ℤ) * r + s) := by ring
    _ = (a : ℤ) * (p * v) - (b : ℤ) * (p * u) := by
      rw [hvZ, huZ]
    _ = (p : ℤ) * ((a : ℤ) * v - (b : ℤ) * u) := by ring

/-- If the determinant is nonzero modulo `p`, the two one-point root sets
are disjoint. -/
theorem disjoint_affineRootResidues_of_not_dvd_det {a s b t p : ℕ}
    (hdet : ¬ (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s) :
    Disjoint (affineRootResidues a s p) (affineRootResidues b t p) := by
  rw [Finset.disjoint_left]
  intro r hra hrb
  exact hdet (int_dvd_affineDet_of_mem_both hra hrb)

/-- Away from primes dividing the determinant, the two-form local bad set
has exactly two classes. -/
theorem twoAffineBadResidues_card_eq_two_of_not_dvd_det
    {a s b t p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hdet : ¬ (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s) :
    (twoAffineBadResidues a s b t p).card = 2 := by
  unfold twoAffineBadResidues
  rw [Finset.card_union_of_disjoint
      (disjoint_affineRootResidues_of_not_dvd_det hdet),
    affineRootResidues_card_eq_one_of_not_dvd hp hpa,
    affineRootResidues_card_eq_one_of_not_dvd hp hpb]

/-- If the determinant vanishes modulo `p`, every root of the first form is
also a root of the second form. -/
theorem mem_affineRootResidues_right_of_dvd_det
    {a s b t p r : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a)
    (hdet : (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s)
    (hra : r ∈ affineRootResidues a s p) :
    r ∈ affineRootResidues b t p := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [mem_affineRootResidues_iff] at hra ⊢
  refine ⟨hra.1, ?_⟩
  have hrootA : ((a * r + s : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (a * r + s) p).2 hra.2
  have hdetZ : (((a : ℤ) * t - (b : ℤ) * s : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdet
  have haZne : (a : ZMod p) ≠ 0 := by
    intro haZ
    exact hpa ((ZMod.natCast_eq_zero_iff a p).mp haZ)
  have hmul : (a : ZMod p) * ((b * r + t : ℕ) : ZMod p) = 0 := by
    push_cast
    have hdetZ' : (a : ZMod p) * t - (b : ZMod p) * s = 0 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hdetZ
    have hrootA' : (a : ZMod p) * r + s = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hrootA
    calc
      (a : ZMod p) * ((b : ZMod p) * r + t) =
          (b : ZMod p) * ((a : ZMod p) * r + s) +
            ((a : ZMod p) * t - (b : ZMod p) * s) := by ring
      _ = 0 := by rw [hrootA', hdetZ']; ring
  have hrootB : ((b * r + t : ℕ) : ZMod p) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left haZne
  exact (ZMod.natCast_eq_zero_iff (b * r + t) p).mp hrootB

/-- When the determinant vanishes, both one-point root sets coincide. -/
theorem affineRootResidues_eq_of_dvd_det
    {a s b t p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hdet : (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s) :
    affineRootResidues a s p = affineRootResidues b t p := by
  ext r
  constructor
  · exact mem_affineRootResidues_right_of_dvd_det hp hpa hdet
  · intro hr
    have hdet' : (p : ℤ) ∣ (b : ℤ) * s - (a : ℤ) * t := by
      simpa [sub_eq_neg_add, add_comm] using Int.dvd_neg.mpr hdet
    exact mem_affineRootResidues_right_of_dvd_det hp hpb hdet' hr

/-- At determinant primes the two-form local bad set has one class. -/
theorem twoAffineBadResidues_card_eq_one_of_dvd_det
    {a s b t p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hdet : (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s) :
    (twoAffineBadResidues a s b t p).card = 1 := by
  unfold twoAffineBadResidues
  rw [affineRootResidues_eq_of_dvd_det hp hpa hpb hdet,
    Finset.union_self, affineRootResidues_card_eq_one_of_not_dvd hp hpb]

/-- At every admissible prime there is at least one local bad class. -/
theorem twoAffineBadResidues_nonempty_of_not_dvd_left
    {a s b t p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) :
    (twoAffineBadResidues a s b t p).Nonempty := by
  exact Finset.Nonempty.mono (Finset.subset_union_left)
    (affineRootResidues_nonempty_of_not_dvd hp hpa)

/-- Two affine forms exclude at most two local residue classes. -/
theorem twoAffineBadResidues_card_le_two_of_not_dvd
    {a s b t p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    (twoAffineBadResidues a s b t p).card ≤ 2 := by
  calc
    (twoAffineBadResidues a s b t p).card ≤
        (affineRootResidues a s p).card + (affineRootResidues b t p).card :=
      by
        unfold twoAffineBadResidues
        exact Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (affineRootResidues_card_le_one_of_not_dvd hp hpa)
      (affineRootResidues_card_le_one_of_not_dvd hp hpb)
    _ = 2 := by norm_num

/-- Every local bad residue is represented by its canonical number below the
modulus. -/
theorem lt_of_mem_twoAffineBadResidues {a s b t p r : ℕ}
    (hr : r ∈ twoAffineBadResidues a s b t p) : r < p := by
  rw [mem_twoAffineBadResidues_iff] at hr
  exact hr.elim And.left And.left

/-- Number of local bad classes for the two affine forms. -/
def twoAffineLocalNu (a s b t p : ℕ) : ℕ :=
  (twoAffineBadResidues a s b t p).card

/-- Multiplicative local density associated to the two affine forms. -/
noncomputable def twoAffineNu (a s b t : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p ↦
    (twoAffineLocalNu a s b t p : ℝ) / p

theorem twoAffineNu_mult (a s b t : ℕ) :
    (twoAffineNu a s b t).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem twoAffineNu_prime {a s b t p : ℕ} (hp : p.Prime) :
    twoAffineNu a s b t p = (twoAffineLocalNu a s b t p : ℝ) / p := by
  rw [twoAffineNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  simp [hp]

theorem twoAffineLocalNu_pos_of_not_dvd_left {a s b t p : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) :
    0 < twoAffineLocalNu a s b t p := by
  exact Finset.card_pos.mpr
    (twoAffineBadResidues_nonempty_of_not_dvd_left hp hpa)

theorem twoAffineLocalNu_le_two_of_not_dvd {a s b t p : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    twoAffineLocalNu a s b t p ≤ 2 :=
  twoAffineBadResidues_card_le_two_of_not_dvd hp hpa hpb

/-- At a sieving prime larger than two and avoiding both slopes, the local
density lies strictly between zero and one. -/
theorem twoAffineNu_pos_lt_one_of_not_dvd {a s b t p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    0 < twoAffineNu a s b t p ∧ twoAffineNu a s b t p < 1 := by
  rw [twoAffineNu_prime hp]
  have hlocalpos : 0 < twoAffineLocalNu a s b t p :=
    twoAffineLocalNu_pos_of_not_dvd_left hp hpa
  have hlocalle : twoAffineLocalNu a s b t p ≤ 2 :=
    twoAffineLocalNu_le_two_of_not_dvd hp hpa hpb
  constructor
  · exact div_pos (by exact_mod_cast hlocalpos) (by exact_mod_cast hp.pos)
  · apply (div_lt_one (by exact_mod_cast hp.pos)).2
    exact_mod_cast hlocalle.trans_lt hp2

/-- If at least one slope is invertible, the two-form bad set is nonempty. -/
theorem twoAffineBadResidues_nonempty_of_one_slope_not_dvd
    {a s b t p : ℕ} (hp : p.Prime) (hslopes : ¬ p ∣ a ∨ ¬ p ∣ b) :
    (twoAffineBadResidues a s b t p).Nonempty := by
  rcases hslopes with hpa | hpb
  · exact twoAffineBadResidues_nonempty_of_not_dvd_left hp hpa
  · exact Finset.Nonempty.mono Finset.subset_union_right
      (affineRootResidues_nonempty_of_not_dvd hp hpb)

/-- At a prime above two, nonzero constants and at least one invertible
slope give a valid local density in the open unit interval. -/
theorem twoAffineNu_pos_lt_one_of_not_dvd_constants_one_slope
    {a s b t p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hps : ¬ p ∣ s) (hpt : ¬ p ∣ t)
    (hslopes : ¬ p ∣ a ∨ ¬ p ∣ b) :
    0 < twoAffineNu a s b t p ∧ twoAffineNu a s b t p < 1 := by
  rw [twoAffineNu_prime hp]
  have hpos : 0 < twoAffineLocalNu a s b t p := by
    exact Finset.card_pos.mpr
      (twoAffineBadResidues_nonempty_of_one_slope_not_dvd hp hslopes)
  have hle : twoAffineLocalNu a s b t p ≤ 2 :=
    twoAffineBadResidues_card_le_two_of_not_dvd_constants hp hps hpt
  constructor
  · exact div_pos (by exact_mod_cast hpos) (by exact_mod_cast hp.pos)
  · apply (div_lt_one (by exact_mod_cast hp.pos)).2
    exact_mod_cast hle.trans_lt hp2

/-- The absolute determinant governing whether the two local roots
coincide.  Its natural absolute value is the shift parameter that appears
in the already-formalized two-shift Euler product. -/
def affineDetNat (a s b t : ℕ) : ℕ :=
  ((a : ℤ) * t - (b : ℤ) * s).natAbs

/-- At an admissible prime, the affine local density is exactly the standard
two-shift density with shift equal to the absolute determinant.  This is the
bridge that lets the affine sieve reuse the pair-shift Euler-product bounds
from Erdős problem 851. -/
theorem twoAffineNu_eq_pairShiftDensity_of_not_dvd
    {a s b t p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    twoAffineNu a s b t p =
      Erdos851.pairShiftDensity (affineDetNat a s b t) p := by
  rw [twoAffineNu_prime hp]
  unfold Erdos851.pairShiftDensity affineDetNat twoAffineLocalNu
  by_cases hdet : p ∣ ((a : ℤ) * t - (b : ℤ) * s).natAbs
  · rw [if_pos hdet]
    have hdetZ : (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s :=
      (Int.natCast_dvd).2 hdet
    rw [twoAffineBadResidues_card_eq_one_of_dvd_det hp hpa hpb hdetZ]
    simp
  · rw [if_neg hdet]
    have hdetZ : ¬ (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s := by
      intro h
      exact hdet ((Int.natCast_dvd).1 h)
    rw [twoAffineBadResidues_card_eq_two_of_not_dvd_det hp hpa hpb hdetZ]
    ring

/-- With nonzero constants, omitting only primes dividing both slopes never
creates a larger local density than the ordinary determinant pair density.
At a determinant prime the one-slope case has exactly one surviving root;
away from the determinant the crude two-root bound is enough. -/
theorem twoAffineNu_le_pairShiftDensity_of_not_dvd_constants_one_slope
    {a s b t p : ℕ} (hp : p.Prime)
    (hps : ¬ p ∣ s) (hpt : ¬ p ∣ t)
    (hslopes : ¬ p ∣ a ∨ ¬ p ∣ b) :
    twoAffineNu a s b t p ≤
      Erdos851.pairShiftDensity (affineDetNat a s b t) p := by
  rw [twoAffineNu_prime hp]
  unfold Erdos851.pairShiftDensity affineDetNat
  by_cases hdet : p ∣ ((a : ℤ) * t - (b : ℤ) * s).natAbs
  · rw [if_pos hdet]
    have hlocal : twoAffineLocalNu a s b t p ≤ 1 := by
      unfold twoAffineLocalNu twoAffineBadResidues
      by_cases hpa : p ∣ a
      · rw [affineRootResidues_eq_empty_of_dvd_slope_not_constant hpa hps,
          Finset.empty_union]
        exact affineRootResidues_card_le_one_of_not_dvd_constant hp hpt
      · by_cases hpb : p ∣ b
        · rw [affineRootResidues_eq_empty_of_dvd_slope_not_constant hpb hpt,
            Finset.union_empty]
          exact affineRootResidues_card_le_one_of_not_dvd_constant hp hps
        · have hdetZ : (p : ℤ) ∣ (a : ℤ) * t - (b : ℤ) * s :=
            (Int.natCast_dvd).2 hdet
          rw [affineRootResidues_eq_of_dvd_det hp hpa hpb hdetZ,
            Finset.union_self,
            affineRootResidues_card_eq_one_of_not_dvd hp hpb]
    change (twoAffineLocalNu a s b t p : ℝ) / p ≤ (p : ℝ)⁻¹
    have hlocalR : (twoAffineLocalNu a s b t p : ℝ) ≤ (1 : ℝ) := by
      exact_mod_cast hlocal
    have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hp.pos.le
    simpa [one_div] using
      (div_le_div_of_nonneg_right hlocalR hpR)
  · rw [if_neg hdet]
    have hlocal : twoAffineLocalNu a s b t p ≤ 2 := by
      unfold twoAffineLocalNu
      exact twoAffineBadResidues_card_le_two_of_not_dvd_constants hp hps hpt
    change (twoAffineLocalNu a s b t p : ℝ) / p ≤ 2 * (p : ℝ)⁻¹
    rw [← div_eq_mul_inv]
    have hlocalR : (twoAffineLocalNu a s b t p : ℝ) ≤ (2 : ℝ) := by
      exact_mod_cast hlocal
    have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hp.pos.le
    exact div_le_div_of_nonneg_right hlocalR hpR

end Erdos822
