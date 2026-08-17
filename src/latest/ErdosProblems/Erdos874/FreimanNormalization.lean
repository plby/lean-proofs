/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.FreimanDimension

/-!
# Affine normalization of a finite integer set

Given an anchor `a ∈ A`, let `d` be the gcd of the absolute offsets
`|x-a|`, and map `x` to `(x-a)/d`.  For a set with at least two elements,
`d` is positive.  The map has the exact reconstruction formula
`x = a + d * ((x-a)/d)`.  We prove that it preserves the cardinalities of
`A` and `A+A`, leaves a primitive normalized set, and transports arithmetic-
progression containment back to `A`.  Choosing `a = min A` makes all normalized
coordinates nonnegative.
-/

open scoped Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The gcd of all absolute offsets from a chosen anchor. -/
def differenceContentAt (A : Finset ℤ) (a : ℤ) : ℕ :=
  A.gcd fun x => (x - a).natAbs

/-- Translate by `a` and divide by the gcd of all offsets from `a`. -/
def normalizationCoord (A : Finset ℤ) (a x : ℤ) : ℤ :=
  (x - a) / (differenceContentAt A a : ℤ)

/-- The normalized image of `A` based at `a`. -/
def normalizeAt (A : Finset ℤ) (a : ℤ) : Finset ℤ :=
  A.image (normalizationCoord A a)

/-- The content divides every offset from the anchor. -/
lemma differenceContentAt_dvd_sub (A : Finset ℤ) (a : ℤ) {x : ℤ}
    (hx : x ∈ A) :
    (differenceContentAt A a : ℤ) ∣ x - a := by
  rw [Int.natCast_dvd]
  exact Finset.gcd_dvd hx

/-- With two distinct members, not all offsets from an anchor in the set are
zero, so their gcd is nonzero. -/
lemma differenceContentAt_ne_zero {A : Finset ℤ} {a : ℤ}
    (_ha : a ∈ A) (hcard : 2 ≤ A.card) :
    differenceContentAt A a ≠ 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hxa_or_hya : x ≠ a ∨ y ≠ a := by
    by_cases hxa : x = a
    · right
      intro hya
      exact hxy (hxa.trans hya.symm)
    · exact Or.inl hxa
  intro hzero
  have hall : ∀ z ∈ A, (z - a).natAbs = 0 :=
    Finset.gcd_eq_zero_iff.mp (show A.gcd (fun z => (z - a).natAbs) = 0 by
      simpa [differenceContentAt] using hzero)
  rcases hxa_or_hya with hxa | hya
  · exact hxa (sub_eq_zero.mp (Int.natAbs_eq_zero.mp (hall x hx)))
  · exact hya (sub_eq_zero.mp (Int.natAbs_eq_zero.mp (hall y hy)))

/-- Positivity form of `differenceContentAt_ne_zero`. -/
lemma differenceContentAt_pos {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    0 < differenceContentAt A a :=
  Nat.pos_of_ne_zero (differenceContentAt_ne_zero ha hcard)

/-- Exact reconstruction from a normalized coordinate. -/
lemma add_content_mul_normalizationCoord {A : Finset ℤ} {a x : ℤ}
    (hx : x ∈ A) :
    a + (differenceContentAt A a : ℤ) * normalizationCoord A a x = x := by
  have hdvd := differenceContentAt_dvd_sub A a hx
  have hcancel :
      (differenceContentAt A a : ℤ) *
          ((x - a) / (differenceContentAt A a : ℤ)) = x - a :=
    Int.mul_ediv_cancel' hdvd
  rw [normalizationCoord]
  omega

/-- The normalization coordinate is injective on the original set. -/
lemma normalizationCoord_injOn {A : Finset ℤ} {a : ℤ}
    (_ha : a ∈ A) (_hcard : 2 ≤ A.card) :
    Set.InjOn (normalizationCoord A a) A := by
  intro x hx y hy hxy
  have hxrec := add_content_mul_normalizationCoord (A := A) (a := a) hx
  have hyrec := add_content_mul_normalizationCoord (A := A) (a := a) hy
  rw [hxy] at hxrec
  exact hxrec.symm.trans hyrec

/-- Normalization preserves the number of elements. -/
theorem card_normalizeAt {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    (normalizeAt A a).card = A.card := by
  rw [normalizeAt, Finset.card_image_iff]
  exact normalizationCoord_injOn ha hcard

/-- The chosen anchor becomes zero. -/
lemma zero_mem_normalizeAt {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) :
    0 ∈ normalizeAt A a := by
  apply Finset.mem_image.mpr
  refine ⟨a, ha, ?_⟩
  simp [normalizationCoord]

/-- If the anchor is a lower bound for `A`, every normalized coordinate is
nonnegative. -/
lemma normalizeAt_nonneg {A : Finset ℤ} {a : ℤ}
    (ha : ∀ x ∈ A, a ≤ x) {z : ℤ} (hz : z ∈ normalizeAt A a) :
    0 ≤ z := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact Int.ediv_nonneg (sub_nonneg.mpr (ha x hx)) (by positivity)

/-- The normalization based at a member of a nontrivial set is primitive:
the gcd of all offsets from zero is exactly one. -/
theorem differenceContentAt_normalizeAt_eq_one {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    differenceContentAt (normalizeAt A a) 0 = 1 := by
  let d := differenceContentAt A a
  let e := differenceContentAt (normalizeAt A a) 0
  have hdpos : 0 < d := differenceContentAt_pos ha hcard
  have hde_dvd : d * e ∣ d := by
    apply Finset.dvd_gcd
    intro x hx
    have hdvd : (d : ℤ) ∣ x - a := by
      simpa [d] using differenceContentAt_dvd_sub A a hx
    have hecoord : e ∣ (normalizationCoord A a x).natAbs := by
      have hxnorm : normalizationCoord A a x ∈ normalizeAt A a :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have h := Finset.gcd_dvd (s := normalizeAt A a)
        (f := fun z : ℤ => (z - 0).natAbs) hxnorm
      simpa only [e, differenceContentAt, sub_zero] using h
    have hquotabs :
        (normalizationCoord A a x).natAbs = (x - a).natAbs / d := by
      simpa [normalizationCoord, d] using Int.natAbs_ediv_of_dvd hdvd
    have hdmul : d ∣ (x - a).natAbs := by
      simpa only [d, differenceContentAt] using
        (Finset.gcd_dvd hx : differenceContentAt A a ∣ (x - a).natAbs)
    have hoffset : (x - a).natAbs = d * (normalizationCoord A a x).natAbs := by
      rw [hquotabs]
      exact (Nat.mul_div_cancel' hdmul).symm
    rw [hoffset]
    exact Nat.mul_dvd_mul_left d hecoord
  have he_dvd_one : e ∣ 1 := by
    apply (Nat.mul_dvd_mul_iff_left hdpos).mp
    simpa using hde_dvd
  exact Nat.eq_one_of_dvd_one he_dvd_one

/-- The affine reconstruction map on pair sums. -/
private def denormalizePairSum (A : Finset ℤ) (a z : ℤ) : ℤ :=
  2 * a + (differenceContentAt A a : ℤ) * z

/-- Applying the affine reconstruction map to the normalized pair sumset gives
the original pair sumset exactly. -/
lemma image_denormalizePairSum_add_normalizeAt {A : Finset ℤ} {a : ℤ} :
    (normalizeAt A a + normalizeAt A a).image (denormalizePairSum A a) =
      A + A := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hw
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
    apply Finset.mem_add.mpr
    refine ⟨x, hx, y, hy, ?_⟩
    have hxrec := add_content_mul_normalizationCoord (A := A) (a := a) hx
    have hyrec := add_content_mul_normalizationCoord (A := A) (a := a) hy
    rw [← hwz, ← huv]
    calc
      x + y =
          (a + (differenceContentAt A a : ℤ) * normalizationCoord A a x) +
          (a + (differenceContentAt A a : ℤ) * normalizationCoord A a y) :=
        congrArg₂ (· + ·) hxrec.symm hyrec.symm
      _ = denormalizePairSum A a (u + v) := by
        rw [hxu, hyv]
        simp only [denormalizePairSum]
        ring
  · intro hz
    obtain ⟨x, hx, y, hy, hxyz⟩ := Finset.mem_add.mp hz
    apply Finset.mem_image.mpr
    refine ⟨normalizationCoord A a x + normalizationCoord A a y, ?_, ?_⟩
    · apply Finset.mem_add.mpr
      exact ⟨normalizationCoord A a x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        normalizationCoord A a y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
    · have hxrec := add_content_mul_normalizationCoord (A := A) (a := a) hx
      have hyrec := add_content_mul_normalizationCoord (A := A) (a := a) hy
      calc
        denormalizePairSum A a
            (normalizationCoord A a x + normalizationCoord A a y) =
            (a + (differenceContentAt A a : ℤ) * normalizationCoord A a x) +
            (a + (differenceContentAt A a : ℤ) * normalizationCoord A a y) := by
          simp only [denormalizePairSum]
          ring
        _ = x + y := congrArg₂ (· + ·) hxrec hyrec
        _ = z := hxyz

/-- Normalization preserves the cardinality of the ordinary pair sumset. -/
theorem card_add_normalizeAt {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    (normalizeAt A a + normalizeAt A a).card = (A + A).card := by
  let d := differenceContentAt A a
  have hdne : (d : ℤ) ≠ 0 := by
    exact_mod_cast differenceContentAt_ne_zero ha hcard
  have hinj : Function.Injective (denormalizePairSum A a) := by
    intro x y hxy
    have hmul : (d : ℤ) * x = (d : ℤ) * y := by
      simpa [denormalizePairSum, d] using add_left_cancel hxy
    exact mul_left_cancel₀ hdne hmul
  calc
    (normalizeAt A a + normalizeAt A a).card =
        ((normalizeAt A a + normalizeAt A a).image
          (denormalizePairSum A a)).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = (A + A).card := by rw [image_denormalizePairSum_add_normalizeAt]

/-- Arithmetic-progression containment transports from normalized coordinates
back to the original set. -/
theorem ContainedInAP.denormalize
    {A : Finset ℤ} {a start : ℤ} {step length : ℕ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card)
    (hAP : ContainedInAP (normalizeAt A a) start step length) :
    ContainedInAP A
      (a + (differenceContentAt A a : ℤ) * start)
      (differenceContentAt A a * step) length := by
  refine ⟨Nat.mul_pos (differenceContentAt_pos ha hcard) hAP.step_pos, ?_⟩
  intro x hx
  have hxnorm : normalizationCoord A a x ∈ normalizeAt A a :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi, hcoord⟩ := hAP.exists_coordinate hxnorm
  refine ⟨i, hi, ?_⟩
  have hxrec := add_content_mul_normalizationCoord (A := A) (a := a) hx
  calc
    x = a + (differenceContentAt A a : ℤ) * normalizationCoord A a x :=
      hxrec.symm
    _ = (a + (differenceContentAt A a : ℤ) * start) +
        (i : ℤ) * (differenceContentAt A a * step : ℕ) := by
      rw [hcoord]
      push_cast
      ring

/-! ## The canonical minimum-based normalization -/

/-- Canonical affine normalization: translate by the least element and divide
by the gcd of all differences from it. -/
def freimanNormalize (A : Finset ℤ) (hA : A.Nonempty) : Finset ℤ :=
  normalizeAt A (A.min' hA)

/-- The minimum-based normalization preserves cardinality. -/
theorem card_freimanNormalize {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalize A hA).card = A.card :=
  card_normalizeAt (Finset.min'_mem A hA) hcard

/-- Zero belongs to the minimum-based normalization. -/
lemma zero_mem_freimanNormalize {A : Finset ℤ} (hA : A.Nonempty) :
    0 ∈ freimanNormalize A hA :=
  zero_mem_normalizeAt (Finset.min'_mem A hA)

/-- Every element of the minimum-based normalization is nonnegative. -/
lemma freimanNormalize_nonneg {A : Finset ℤ} (hA : A.Nonempty)
    {z : ℤ} (hz : z ∈ freimanNormalize A hA) :
    0 ≤ z := by
  apply normalizeAt_nonneg (A := A) (a := A.min' hA) (z := z)
  · intro x hx
    exact Finset.min'_le A x hx
  · exact hz

/-- The minimum-based normalization has content one. -/
theorem differenceContentAt_freimanNormalize_eq_one {A : Finset ℤ}
    (hA : A.Nonempty) (hcard : 2 ≤ A.card) :
    differenceContentAt (freimanNormalize A hA) 0 = 1 :=
  differenceContentAt_normalizeAt_eq_one (Finset.min'_mem A hA) hcard

/-- The minimum-based normalization preserves the pair-sumset cardinality. -/
theorem card_add_freimanNormalize {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalize A hA + freimanNormalize A hA).card = (A + A).card :=
  card_add_normalizeAt (Finset.min'_mem A hA) hcard

/-- Progression containment for the minimum-based normalization transports
back to the original set with the expected affine change of start and step. -/
theorem ContainedInAP.denormalize_min
    {A : Finset ℤ} (hA : A.Nonempty) {start : ℤ} {step length : ℕ}
    (hcard : 2 ≤ A.card)
    (hAP : ContainedInAP (freimanNormalize A hA) start step length) :
    ContainedInAP A
      (A.min' hA + (differenceContentAt A (A.min' hA) : ℤ) * start)
      (differenceContentAt A (A.min' hA) * step) length :=
  hAP.denormalize (Finset.min'_mem A hA) hcard

/-! ## Passing a nonnegative integer model to natural numbers -/

/-- Replace every nonnegative integer in `B` by the corresponding natural
number.  The hypotheses proving nonnegativity are kept on the lemmas, so this
definition is also convenient for intermediate constructions. -/
def natify (B : Finset ℤ) : Finset ℕ :=
  B.image Int.toNat

private lemma toNat_eq_natAbs_of_nonneg {z : ℤ} (hz : 0 ≤ z) :
    z.toNat = z.natAbs := by
  exact_mod_cast (Int.toNat_of_nonneg hz).trans (Int.natAbs_of_nonneg hz).symm

/-- On a nonnegative integer finset, membership in `natify B` is equivalent to
membership of the natural cast in `B`. -/
theorem mem_natify_iff {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z) {n : ℕ} :
    n ∈ natify B ↔ (n : ℤ) ∈ B := by
  constructor
  · intro hn
    obtain ⟨z, hz, hzn⟩ := Finset.mem_image.mp hn
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (hB z hz)
    rw [← hzn, hzcast]
    exact hz
  · intro hn
    exact Finset.mem_image.mpr ⟨(n : ℤ), hn, by simp⟩

/-- `Int.toNat` is injective on a nonnegative integer finset. -/
lemma toNat_injOn_of_nonneg {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z) :
    Set.InjOn Int.toNat B := by
  intro x hx y hy hxy
  have hcast : (x.toNat : ℤ) = (y.toNat : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hxy
  simpa [Int.toNat_of_nonneg (hB x hx), Int.toNat_of_nonneg (hB y hy)] using hcast

/-- `natify` preserves cardinality on nonnegative integer finsets. -/
theorem card_natify {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z) :
    (natify B).card = B.card := by
  rw [natify, Finset.card_image_iff]
  exact toNat_injOn_of_nonneg hB

/-- Zero is transported unchanged by `natify`. -/
lemma zero_mem_natify {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z)
    (hzero : 0 ∈ B) :
    0 ∈ natify B :=
  (mem_natify_iff hB).2 (by simpa using hzero)

/-- A natural upper bound on a nonnegative integer model is preserved by
`natify`. -/
lemma natify_le {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z) {M : ℕ}
    (hupper : ∀ z ∈ B, z ≤ (M : ℤ)) {n : ℕ} (hn : n ∈ natify B) :
    n ≤ M := by
  have hnB : (n : ℤ) ∈ B := (mem_natify_iff hB).1 hn
  exact_mod_cast hupper (n : ℤ) hnB

/-- The natural gcd of `natify B` is the integer offset content of a
nonnegative `B` based at zero. -/
theorem gcd_natify_eq_differenceContentAt {B : Finset ℤ}
    (hB : ∀ z ∈ B, 0 ≤ z) :
    (natify B).gcd id = differenceContentAt B 0 := by
  have hforward : (natify B).gcd (fun n : ℕ => n) ∣ differenceContentAt B 0 := by
    rw [differenceContentAt]
    apply Finset.dvd_gcd
    intro z hz
    have hzN : z.toNat ∈ natify B := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hdvd : (natify B).gcd (fun n : ℕ => n) ∣ z.toNat :=
      Finset.gcd_dvd hzN
    simpa [toNat_eq_natAbs_of_nonneg (hB z hz)] using hdvd
  have hbackward : differenceContentAt B 0 ∣ (natify B).gcd (fun n : ℕ => n) := by
    apply Finset.dvd_gcd
    intro n hn
    have hnB : (n : ℤ) ∈ B := (mem_natify_iff hB).1 hn
    have hdvd := Finset.gcd_dvd (s := B)
      (f := fun z : ℤ => (z - 0).natAbs) hnB
    simpa [differenceContentAt] using hdvd
  exact Nat.dvd_antisymm hforward hbackward

/-- In particular, content one becomes the usual natural-finset gcd-one
hypothesis. -/
theorem gcd_natify_eq_one {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z)
    (hcontent : differenceContentAt B 0 = 1) :
    (natify B).gcd id = 1 := by
  rw [gcd_natify_eq_differenceContentAt hB, hcontent]

/-- Casting the sumset of `natify B` back to integers gives `B+B`. -/
lemma image_natCast_add_natify {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z) :
    (natify B + natify B).image (fun n : ℕ => (n : ℤ)) = B + B := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hnz⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hn
    apply Finset.mem_add.mpr
    refine ⟨(u : ℤ), (mem_natify_iff hB).1 hu,
      (v : ℤ), (mem_natify_iff hB).1 hv, ?_⟩
    rw [← hnz, ← huv]
    norm_num
  · intro hz
    obtain ⟨x, hx, y, hy, hxyz⟩ := Finset.mem_add.mp hz
    apply Finset.mem_image.mpr
    refine ⟨x.toNat + y.toNat, ?_, ?_⟩
    · apply Finset.mem_add.mpr
      exact ⟨x.toNat, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        y.toNat, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
    · rw [← hxyz]
      simp [Int.toNat_of_nonneg (hB x hx), Int.toNat_of_nonneg (hB y hy)]

/-- Passing a nonnegative integer set to naturals preserves the cardinality of
its ordinary pair sumset. -/
theorem card_add_natify {B : Finset ℤ} (hB : ∀ z ∈ B, 0 ≤ z) :
    (natify B + natify B).card = (B + B).card := by
  calc
    (natify B + natify B).card =
        ((natify B + natify B).image (fun n : ℕ => (n : ℤ))).card :=
      (Finset.card_image_of_injective _ Int.ofNat_injective).symm
    _ = (B + B).card := by rw [image_natCast_add_natify hB]

/-- The canonical natural-number model associated to a nontrivial integer
finset. -/
def freimanNormalizeNat (A : Finset ℤ) (hA : A.Nonempty) : Finset ℕ :=
  natify (freimanNormalize A hA)

/-- The canonical natural model has the same number of elements as `A`. -/
theorem card_freimanNormalizeNat {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalizeNat A hA).card = A.card := by
  rw [freimanNormalizeNat, card_natify (fun z hz => freimanNormalize_nonneg hA hz),
    card_freimanNormalize hA hcard]

/-- Zero belongs to the canonical natural model. -/
lemma zero_mem_freimanNormalizeNat {A : Finset ℤ} (hA : A.Nonempty) :
    0 ∈ freimanNormalizeNat A hA := by
  apply zero_mem_natify (fun z hz => freimanNormalize_nonneg hA hz)
  exact zero_mem_freimanNormalize hA

/-- The canonical natural model has gcd one. -/
theorem gcd_freimanNormalizeNat_eq_one {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalizeNat A hA).gcd id = 1 := by
  apply gcd_natify_eq_one (fun z hz => freimanNormalize_nonneg hA hz)
  exact differenceContentAt_freimanNormalize_eq_one hA hcard

/-- The canonical natural model and `A` have pair sumsets of the same
cardinality. -/
theorem card_add_freimanNormalizeNat {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalizeNat A hA + freimanNormalizeNat A hA).card =
      (A + A).card := by
  calc
    (freimanNormalizeNat A hA + freimanNormalizeNat A hA).card =
        (freimanNormalize A hA + freimanNormalize A hA).card :=
      card_add_natify (fun z hz => freimanNormalize_nonneg hA hz)
    _ = (A + A).card := card_add_freimanNormalize hA hcard

end

end Erdos874
