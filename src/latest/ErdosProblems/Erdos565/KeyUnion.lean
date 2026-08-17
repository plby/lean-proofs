/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Tactic

/-!
# The finite union bound in the key lemma for Erdős problem 565

This file isolates the bookkeeping at the end of the probabilistic key lemma.
For fixed structural data, the preceding probabilistic estimates give a bound
on a finite bad-event set.  The structural data consists of two vertex sets,
one integer `R` for every color, and one color-dependent object for every
color.  In particular, the `R`-vector contributes `(N + 1) ^ r` possibilities;
it is not silently omitted from the count.

All statements below are exact cardinality inequalities in `ℕ`.  Thus no
probability-measure conventions or negative powers are hidden in the formal
union bound.
-/

@[expose] public section

open scoped BigOperators

namespace Erdos565
namespace KeyUnion

/-- The vector `(R_i)_{i < r}` appearing in a fixed structural tuple.  Each
coordinate lies between `0` and `N`, inclusive. -/
abbrev RVector (r N : ℕ) := Fin r → Fin (N + 1)

/-- The exact number of possible `R`-vectors. -/
theorem card_rVector (r N : ℕ) :
    Fintype.card (RVector r N) = (N + 1) ^ r := by
  simp [RVector, Fintype.card_pi]

/-- Structural data held fixed in one application of the key-lemma event
estimate.  `colorData i` packages the graph/container data in color `i`.

The nested product is used rather than a structure declaration so that its
cardinality reduces transparently to the product formula for finite types. -/
abbrev FixedStructure (N r : ℕ) (ColorData : Fin r → Type*) :=
  (Finset (Fin N) × Finset (Fin N)) ×
    (RVector r N × ((i : Fin r) → ColorData i))

/-- Exact cardinality of the structural-data type. -/
theorem card_fixedStructure (N r : ℕ) (ColorData : Fin r → Type*)
    [∀ i, Fintype (ColorData i)] :
    Fintype.card (FixedStructure N r ColorData) =
      2 ^ N * 2 ^ N * ((N + 1) ^ r * ∏ i, Fintype.card (ColorData i)) := by
  simp [FixedStructure, Fintype.card_pi]

/-- If there are at most `2^(4 D)` choices for the data in each color, then
the complete color-data vector has at most `2^(4 r D)` choices. -/
theorem card_colorData_le (r D : ℕ) (ColorData : Fin r → Type*)
    [∀ i, Fintype (ColorData i)]
    (hColor : ∀ i, Fintype.card (ColorData i) ≤ 2 ^ (4 * D)) :
    Fintype.card ((i : Fin r) → ColorData i) ≤ 2 ^ (4 * r * D) := by
  rw [Fintype.card_pi]
  calc
    ∏ i : Fin r, Fintype.card (ColorData i) ≤
        ∏ _i : Fin r, 2 ^ (4 * D) := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ hColor i)
    _ = (2 ^ (4 * D)) ^ r := by simp
    _ = 2 ^ (4 * r * D) := by
      rw [← pow_mul]
      congr 1
      ring

/-- Counting the two vertex sets, the `R`-vector, and all color data gives
the corrected structural exponent `3 N + 4 r D`.  The hypothesis `hR` is the
separate numerical estimate which absorbs the exact `(N+1)^r` contribution
of the `R`-vector into a third factor `2^N`. -/
theorem card_fixedStructure_le_two_pow
    (N r D : ℕ) (ColorData : Fin r → Type*) [∀ i, Fintype (ColorData i)]
    (hR : (N + 1) ^ r ≤ 2 ^ N)
    (hColor : ∀ i, Fintype.card (ColorData i) ≤ 2 ^ (4 * D)) :
    Fintype.card (FixedStructure N r ColorData) ≤
      2 ^ (3 * N + 4 * r * D) := by
  rw [card_fixedStructure]
  calc
    2 ^ N * 2 ^ N * ((N + 1) ^ r * ∏ i, Fintype.card (ColorData i)) ≤
        2 ^ N * 2 ^ N * (2 ^ N * 2 ^ (4 * r * D)) := by
      gcongr
      have hdata := card_colorData_le r D ColorData hColor
      rw [Fintype.card_pi] at hdata
      exact hdata
    _ = 2 ^ (3 * N + 4 * r * D) := by
      simp only [← pow_add]
      congr 1
      ring

/-! ## A cardinality form of the finite union bound -/

/-- The bad objects belonging to one fixed structural tuple. -/
noncomputable def badSet {Omega Sigma : Type*} [Fintype Omega]
    (bad : Sigma → Omega → Prop) (s : Sigma) : Finset Omega :=
  by
    classical
    exact Finset.univ.filter (bad s)

/-- The union of all fixed-structure bad-event sets. -/
noncomputable def badUnion {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma]
    (bad : Sigma → Omega → Prop) : Finset Omega :=
  by
    classical
    exact Finset.univ.biUnion (badSet bad)

/-- An ordinary finite union bound with a uniform fiber bound. -/
theorem card_badUnion_le {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma]
    (bad : Sigma → Omega → Prop) (K : ℕ)
    (hbad : ∀ s, (badSet bad s).card ≤ K) :
    (badUnion bad).card ≤ Fintype.card Sigma * K := by
  classical
  unfold badUnion
  calc
    (Finset.univ.biUnion (badSet bad)).card ≤
        ∑ s ∈ (Finset.univ : Finset Sigma), (badSet bad s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ (Finset.univ : Finset Sigma), K := by
      exact Finset.sum_le_sum fun s _ ↦ hbad s
    _ = Fintype.card Sigma * K := by simp

/-- The exponent arithmetic behind the last line of the key lemma.

`D` denotes the integer exponent representing `delta^2 N^2`.  If `N ≤ r D`,
then the `3N + 4rD` structural exponent, together with the desired remaining
factor `2^D`, is absorbed by the fixed-structure saving `2^(8rD)`. -/
theorem structural_exponent_add_target_le
    {N r D : ℕ} (hr : 1 ≤ r) (hND : N ≤ r * D) :
    3 * N + 4 * r * D + D ≤ 8 * r * D := by
  have hD : D ≤ r * D := by
    simpa using Nat.mul_le_mul_right D hr
  calc
    3 * N + 4 * r * D + D ≤ 3 * (r * D) + 4 * r * D + D := by
      gcongr
    _ = 7 * (r * D) + D := by ring
    _ ≤ 8 * (r * D) := by omega
    _ = 8 * r * D := by ring

/-- The complete finite union-bound step for the key lemma.

For each fixed structural tuple the bad set has size at most `K`, and the
preceding probabilistic estimate states `K * 2^(8 r D) ≤ |Omega|`.  After
unioning over all structural tuples, including the `R`-vector, the bad union
still satisfies

`|badUnion| * 2^D ≤ |Omega|`,

which is the denominator-cleared meaning of probability at most `2^(-D)`.
-/
theorem key_union_bound
    {Omega : Type*} [Fintype Omega]
    (N r D : ℕ) (ColorData : Fin r → Type*) [∀ i, Fintype (ColorData i)]
    (bad : FixedStructure N r ColorData → Omega → Prop) (K : ℕ)
    (hr : 1 ≤ r) (hND : N ≤ r * D)
    (hR : (N + 1) ^ r ≤ 2 ^ N)
    (hColor : ∀ i, Fintype.card (ColorData i) ≤ 2 ^ (4 * D))
    (hbad : ∀ s, (badSet bad s).card ≤ K)
    (hfixed : K * 2 ^ (8 * r * D) ≤ Fintype.card Omega) :
    (badUnion bad).card * 2 ^ D ≤ Fintype.card Omega := by
  have hstructures : Fintype.card (FixedStructure N r ColorData) ≤
      2 ^ (3 * N + 4 * r * D) :=
    card_fixedStructure_le_two_pow N r D ColorData hR hColor
  have hunion : (badUnion bad).card ≤
      2 ^ (3 * N + 4 * r * D) * K :=
    (card_badUnion_le bad K hbad).trans (Nat.mul_le_mul_right K hstructures)
  calc
    (badUnion bad).card * 2 ^ D ≤
        (2 ^ (3 * N + 4 * r * D) * K) * 2 ^ D :=
      Nat.mul_le_mul_right (2 ^ D) hunion
    _ = K * 2 ^ (3 * N + 4 * r * D + D) := by
      rw [pow_add]
      ring
    _ ≤ K * 2 ^ (8 * r * D) := by
      exact Nat.mul_le_mul_left K
        (Nat.pow_le_pow_right (by decide : 0 < 2)
          (structural_exponent_add_target_le hr hND))
    _ ≤ Fintype.card Omega := hfixed

/-- If the denominator-cleared key estimate has a positive remaining power,
the union is a strict subset of the sample space. -/
theorem card_badUnion_lt
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (N r D : ℕ) (ColorData : Fin r → Type*) [∀ i, Fintype (ColorData i)]
    (bad : FixedStructure N r ColorData → Omega → Prop) (K : ℕ)
    (hr : 1 ≤ r) (hD : 1 ≤ D) (hND : N ≤ r * D)
    (hR : (N + 1) ^ r ≤ 2 ^ N)
    (hColor : ∀ i, Fintype.card (ColorData i) ≤ 2 ^ (4 * D))
    (hbad : ∀ s, (badSet bad s).card ≤ K)
    (hfixed : K * 2 ^ (8 * r * D) ≤ Fintype.card Omega) :
    (badUnion bad).card < Fintype.card Omega := by
  have hkey := key_union_bound N r D ColorData bad K hr hND hR hColor hbad hfixed
  have htwo : 2 ≤ 2 ^ D := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hD
  by_contra hnot
  have hOmega : Fintype.card Omega ≤ (badUnion bad).card := by omega
  have hOmegaPos : 0 < Fintype.card Omega := Fintype.card_pos
  have hbadPos : 0 < (badUnion bad).card := hOmegaPos.trans_le hOmega
  have hstrict : (badUnion bad).card < (badUnion bad).card * 2 := by omega
  have hmul : (badUnion bad).card * 2 ≤
      (badUnion bad).card * 2 ^ D := Nat.mul_le_mul_left _ htwo
  omega

end KeyUnion
end Erdos565
