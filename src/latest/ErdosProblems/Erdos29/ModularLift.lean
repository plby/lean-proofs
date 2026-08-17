import ErdosProblems.Erdos29.QuadraticFiber
import Mathlib

/-!
# The uniform `p^2` modular lift for Erdős Problem 29

This file separates the elementary lifting and counting argument from the
particular choice of three parabolas.  A `CoefficientSystem p` records three
coefficients over `ZMod p`, a cover of every point of the affine plane by a
sum of two of their parabolas, and the nonvanishing of every ordered sum of
two coefficients.

The lifted tagged atom is

`x + p * val (c * x^2 + s)  (mod p^2)`,

where `s` is either `-1` or `0`.  The negative shift removes the carry in the
standard representatives of two low coordinates.  Thus every residue modulo
`p^2` is covered.  The tagged representation count is at most
`(3 * 2)^2 * 2 * 2 = 144`: after fixing four tags and the low-coordinate
carry, the first low coordinate satisfies a genuine quadratic.
-/

namespace Erdos29.ModularLift

open scoped BigOperators

private abbrev F (p : ℕ) := ZMod p

/-- Abstract finite-field data required by the uniform lift. -/
structure CoefficientSystem (p : ℕ) where
  coeff : Fin 3 → F p
  cover : ∀ u v : F p, ∃ i j : Fin 3, ∃ x y : F p,
    x + y = u ∧ coeff i * x ^ 2 + coeff j * y ^ 2 = v
  coeff_add_ne_zero : ∀ i j : Fin 3, coeff i + coeff j ≠ 0

/-- The two carry-correcting high-coordinate shifts, `-1` and `0`. -/
def shift (p : ℕ) : Fin 2 → F p
  | i => if i = 0 then -1 else 0

@[simp] theorem shift_zero (p : ℕ) : shift p 0 = -1 := by simp [shift]
@[simp] theorem shift_one (p : ℕ) : shift p 1 = 0 := by simp [shift]

/-- A tagged lifted atom: coefficient tag, shift tag, and low coordinate. -/
abbrev Parameter (p : ℕ) := Fin 3 × Fin 2 × F p

/-- The high coordinate of a tagged lifted atom. -/
def high {p : ℕ} (S : CoefficientSystem p) (a : Parameter p) : F p :=
  S.coeff a.1 * a.2.2 ^ 2 + shift p a.2.1

/-- Encode a tagged atom as a residue modulo `p^2`, using standard
representatives in both coordinates. -/
def value {p : ℕ} (S : CoefficientSystem p) (a : Parameter p) : ZMod (p ^ 2) :=
  (a.2.2.val + p * (high S a).val : ℕ)

/-- The finite set of lifted residues. -/
def residueDigitSet {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) : Finset (ZMod (p ^ 2)) :=
  Finset.univ.image (value S)

/-- Standard natural representatives of the lifted residues. -/
def digitSet {p : ℕ} [NeZero p] (S : CoefficientSystem p) : Finset ℕ :=
  (residueDigitSet S).image ZMod.val

@[simp] theorem value_mem_residueDigitSet {p : ℕ} [NeZero p]
    (S : CoefficientSystem p)
    (a : Parameter p) : value S a ∈ residueDigitSet S := by
  classical
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

theorem value_val_mem_digitSet {p : ℕ} [NeZero p] (S : CoefficientSystem p)
    (a : Parameter p) : (value S a).val ∈ digitSet S := by
  classical
  exact Finset.mem_image.mpr ⟨value S a, value_mem_residueDigitSet S a, rfl⟩

theorem mem_digitSet_lt {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (hp0 : 0 < p)
    {d : ℕ} (hd : d ∈ digitSet S) : d < p ^ 2 := by
  classical
  rcases Finset.mem_image.mp hd with ⟨z, _hz, rfl⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  exact z.val_lt

private theorem value_add_eq_of_carry {p : ℕ} (hp0 : 0 < p)
    (S : CoefficientSystem p) (a b : Parameter p) (u : ZMod (p ^ 2))
    (r h e : ℕ)
    (hlow : a.2.2.val + b.2.2.val = r + p * e)
    (hhigh : high S a + high S b + (e : F p) = (h : F p))
    (hu : u.val = r + p * h) :
    value S a + value S b = u := by
  haveI : NeZero p := ⟨Nat.ne_of_gt hp0⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  have hm : (high S a).val + (high S b).val + e ≡ h [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hhigh
  have hm' := hm.mul_left' p
  have hm'' := Nat.ModEq.add_left r hm'
  rw [← u.natCast_zmod_val]
  change ((a.2.2.val + p * (high S a).val : ℕ) : ZMod (p ^ 2)) +
      (b.2.2.val + p * (high S b).val : ℕ) = (u.val : ZMod (p ^ 2))
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  have hraw : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) =
      r + p * ((high S a).val + (high S b).val + e) := by
    calc
      a.2.2.val + p * (high S a).val +
          (b.2.2.val + p * (high S b).val) =
          (a.2.2.val + b.2.2.val) +
            p * ((high S a).val + (high S b).val) := by ring
      _ = (r + p * e) + p * ((high S a).val + (high S b).val) := by rw [hlow]
      _ = r + p * ((high S a).val + (high S b).val + e) := by ring
  rw [hraw, hu]
  simpa only [pow_two] using hm''

/-- Every residue modulo `p^2` is the sum of two tagged lifted atoms. -/
theorem exists_value_add_eq {p : ℕ} (hp : p.Prime) (S : CoefficientSystem p)
    (u : ZMod (p ^ 2)) :
    ∃ a b : Parameter p, value S a + value S b = u := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := u.val % p
  let h := u.val / p
  have hr : r < p := Nat.mod_lt _ hp0
  have hu : u.val = r + p * h := by
    dsimp [r, h]
    exact (Nat.mod_add_div u.val p).symm
  rcases S.cover (r : F p) (h : F p) with ⟨i, j, x, y, hxy, hcurve⟩
  have haddval : (x + y).val = r := by
    rw [hxy]
    exact ZMod.val_natCast_of_lt hr
  by_cases hs : x.val + y.val < p
  · have hlow : x.val + y.val = r := by
      rw [← ZMod.val_add_of_lt hs, haddval]
    refine ⟨(i, 1, x), (j, 1, y),
      value_add_eq_of_carry hp0 S _ _ u r h 0 ?_ ?_ hu⟩
    · simpa using hlow
    · simp only [high, shift_one, add_zero, Nat.cast_zero]
      simpa using hcurve
  · have hlow : x.val + y.val = r + p := by
      calc
        x.val + y.val = (x + y).val + p :=
          ZMod.val_add_val_of_le (not_lt.mp hs)
        _ = r + p := by rw [haddval]
    refine ⟨(i, 0, x), (j, 1, y),
      value_add_eq_of_carry hp0 S _ _ u r h 1 ?_ ?_ hu⟩
    · simpa using hlow
    · simp only [high, shift_zero, shift_one, add_zero, Nat.cast_one]
      linear_combination hcurve

/-- The residue digit set is an additive basis of `ZMod (p^2)`. -/
theorem residueDigitSet_add_cover {p : ℕ} [NeZero p]
    (hp : p.Prime) (S : CoefficientSystem p)
    (u : ZMod (p ^ 2)) :
    ∃ a ∈ residueDigitSet S, ∃ b ∈ residueDigitSet S, a + b = u := by
  rcases exists_value_add_eq hp S u with ⟨a, b, hab⟩
  exact ⟨value S a, value_mem_residueDigitSet S a,
    value S b, value_mem_residueDigitSet S b, hab⟩

/-! ## Uniform tagged representation bound -/

/-- The carry of the two standard low-coordinate representatives. -/
def carry {p : ℕ} (a b : Parameter p) : Fin 2 :=
  if a.2.2.val + b.2.2.val < p then 0 else 1

@[simp] private theorem carry_eq_zero {p : ℕ} {a b : Parameter p}
    (h : a.2.2.val + b.2.2.val < p) : carry a b = 0 := by
  simp [carry, h]

@[simp] private theorem carry_eq_one {p : ℕ} {a b : Parameter p}
    (h : ¬ a.2.2.val + b.2.2.val < p) : carry a b = 1 := by
  simp [carry, h]

private theorem raw_modEq_of_value_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    a.2.2.val + p * (high S a).val +
        (b.2.2.val + p * (high S b).val) ≡ u.val [MOD p ^ 2] := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  calc
    ((a.2.2.val + p * (high S a).val +
        (b.2.2.val + p * (high S b).val) : ℕ) : ZMod (p ^ 2)) =
        value S a + value S b := by
          simp only [value, Nat.cast_add]
    _ = u := hab
    _ = (u.val : ZMod (p ^ 2)) := u.natCast_zmod_val.symm

private theorem low_equation_of_value_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    a.2.2 + b.2.2 = ((u.val % p : ℕ) : F p) := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm2 := raw_modEq_of_value_add_eq hp S hab
  have hm2' : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) ≡ u.val [MOD p * p] := by
    simpa only [pow_two] using hm2
  have hm : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) ≡ u.val [MOD p] :=
    hm2'.of_mul_left p
  have hz : ((a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) : ℕ) : F p) = (u.val : F p) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact hm
  simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    add_zero, ZMod.natCast_zmod_val, ZMod.natCast_mod] using hz

private theorem low_val_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    a.2.2.val + b.2.2.val = u.val % p + p * (carry a b).val := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hfield := low_equation_of_value_add_eq hp S hab
  have hr : u.val % p < p := Nat.mod_lt _ hp.pos
  have hval : (a.2.2 + b.2.2).val = u.val % p := by
    rw [hfield]
    exact ZMod.val_natCast_of_lt hr
  by_cases hs : a.2.2.val + b.2.2.val < p
  · rw [carry_eq_zero hs]
    simpa using (show a.2.2.val + b.2.2.val = u.val % p by
      rw [← ZMod.val_add_of_lt hs, hval])
  · rw [carry_eq_one hs]
    simpa using (show a.2.2.val + b.2.2.val = u.val % p + p by
      calc
        a.2.2.val + b.2.2.val = (a.2.2 + b.2.2).val + p :=
          ZMod.val_add_val_of_le (not_lt.mp hs)
        _ = u.val % p + p := by rw [hval])

private theorem high_equation_of_value_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    high S a + high S b + ((carry a b).val : F p) =
      ((u.val / p : ℕ) : F p) := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm2 := raw_modEq_of_value_add_eq hp S hab
  have hlow := low_val_add_eq hp S hab
  let r := u.val % p
  let h := u.val / p
  have hu : u.val = r + p * h := by
    dsimp [r, h]
    exact (Nat.mod_add_div u.val p).symm
  have hraw : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) =
      r + p * ((high S a).val + (high S b).val + (carry a b).val) := by
    calc
      a.2.2.val + p * (high S a).val +
          (b.2.2.val + p * (high S b).val) =
          (a.2.2.val + b.2.2.val) +
            p * ((high S a).val + (high S b).val) := by ring
      _ = (r + p * (carry a b).val) +
            p * ((high S a).val + (high S b).val) := by rw [hlow]
      _ = r + p * ((high S a).val + (high S b).val + (carry a b).val) := by ring
  rw [hraw, hu] at hm2
  have hcancel : (high S a).val + (high S b).val + (carry a b).val ≡ h [MOD p] := by
    have hc : p * ((high S a).val + (high S b).val + (carry a b).val) ≡
        p * h [MOD p ^ 2] := Nat.ModEq.add_left_cancel' r hm2
    rw [pow_two] at hc
    exact Nat.ModEq.mul_left_cancel' hp.ne_zero hc
  have hz : (((high S a).val + (high S b).val + (carry a b).val : ℕ) : F p) =
      (h : F p) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact hcancel
  simpa only [Nat.cast_add, ZMod.natCast_zmod_val, h] using hz

/-- All discrete tags of an ordered lifted representation, including its
low-coordinate carry. -/
abbrev SliceTag := (Fin 3 × Fin 2) × (Fin 3 × Fin 2) × Fin 2

/-- The tag by which the representation set is partitioned. -/
def sliceTag {p : ℕ} (ab : Parameter p × Parameter p) : SliceTag :=
  ((ab.1.1, ab.1.2.1), (ab.2.1, ab.2.2.1), carry ab.1 ab.2)

/-- Ordered tagged representations of one residue. -/
def taggedRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    Finset (Parameter p × Parameter p) :=
  Finset.univ.filter fun ab ↦ value S ab.1 + value S ab.2 = u

/-- A fixed coefficient/shift/carry slice contains at most two tagged
representations. -/
theorem tagged_slice_card_le_two {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) (t : SliceTag) :
    ((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t).card ≤ 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let r : F p := (u.val % p : ℕ)
  let v : F p := (u.val / p : ℕ) - shift p t.1.2 -
    shift p t.2.1.2 - t.2.2.val
  let Q := QuadraticFiber.lineQuadraticFiber
      (S.coeff t.1.1) (S.coeff t.2.1.1) r v
  have hmaps : Set.MapsTo (fun ab : Parameter p × Parameter p ↦
      (ab.1.2.2, ab.2.2.2))
      (((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t) :
        Set (Parameter p × Parameter p)) (Q : Set (F p × F p)) := by
    intro ab hab
    have hab' := (Finset.mem_filter.mp hab).1
    have htag := (Finset.mem_filter.mp hab).2
    have hsum : value S ab.1 + value S ab.2 = u :=
      (Finset.mem_filter.mp hab').2
    have hlow := low_equation_of_value_add_eq hp S hsum
    have hhigh := high_equation_of_value_add_eq hp S hsum
    have hi : ab.1.1 = t.1.1 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.1.1) htag
    have hsi : ab.1.2.1 = t.1.2 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.1.2) htag
    have hj : ab.2.1 = t.2.1.1 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.2.1.1) htag
    have hsj : ab.2.2.1 = t.2.1.2 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.2.1.2) htag
    have he : carry ab.1 ab.2 = t.2.2 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.2.2) htag
    simp only [Q, QuadraticFiber.lineQuadraticFiber, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simpa [r] using hlow, ?_⟩
    dsimp [high] at hhigh
    dsimp [v]
    rw [hi, hsi, hj, hsj, he] at hhigh
    linear_combination hhigh
  have hinj : Set.InjOn (fun ab : Parameter p × Parameter p ↦
      (ab.1.2.2, ab.2.2.2))
      (((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t) :
        Set (Parameter p × Parameter p)) := by
    intro ab hab cd hcd hlow
    have habtag := (Finset.mem_filter.mp hab).2
    have hcdtag := (Finset.mem_filter.mp hcd).2
    have htags : sliceTag ab = sliceTag cd := habtag.trans hcdtag.symm
    rcases ab with ⟨⟨ia, sa, xa⟩, ⟨ja, ta, ya⟩⟩
    rcases cd with ⟨⟨ib, sb, xb⟩, ⟨jb, tb, yb⟩⟩
    simp only [sliceTag, Prod.mk.injEq] at htags hlow ⊢
    aesop
  calc
    ((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t).card ≤ Q.card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ 2 := QuadraticFiber.lineQuadraticFiber_card_le_two _ _ _ _
      (S.coeff_add_ne_zero _ _)

/-- Uniform bound for ordered tagged representations of a residue modulo
`p^2`. -/
theorem taggedRepresentations_card_le {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    (taggedRepresentations S u).card ≤ 144 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  calc
    (taggedRepresentations S u).card =
        ∑ t : SliceTag,
          ((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t).card := by
      exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)
    _ ≤ ∑ _t : SliceTag, 2 := Finset.sum_le_sum fun t _ ↦ tagged_slice_card_le_two hp S u t
    _ = 144 := by norm_num [Fintype.card_prod, Fintype.card_fin]

/-! ## Untagged residue and natural-representative APIs -/

/-- Ordered representations using the untagged residue digit set. -/
def residueRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    Finset (ZMod (p ^ 2) × ZMod (p ^ 2)) :=
  ((residueDigitSet S).product (residueDigitSet S)).filter fun ab ↦ ab.1 + ab.2 = u

/-- Forgetting the tags cannot increase the representation count. -/
theorem residueRepresentations_card_le {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    (residueRepresentations S u).card ≤ 144 := by
  classical
  let f : Parameter p × Parameter p → ZMod (p ^ 2) × ZMod (p ^ 2) :=
    fun ab ↦ (value S ab.1, value S ab.2)
  have hsurj : Set.SurjOn f (taggedRepresentations S u : Set _)
      (residueRepresentations S u : Set _) := by
    intro zw hzw
    have hprod := (Finset.mem_filter.mp hzw).1
    have hsum := (Finset.mem_filter.mp hzw).2
    have hza := (Finset.mem_product.mp hprod).1
    have hzb := (Finset.mem_product.mp hprod).2
    rcases Finset.mem_image.mp hza with ⟨a, _ha, hva⟩
    rcases Finset.mem_image.mp hzb with ⟨b, _hb, hvb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · simp only [taggedRepresentations, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [f, hva, hvb] using hsum
    · simp [f, hva, hvb]
  exact (Finset.card_le_card_of_surjOn f hsurj).trans
    (taggedRepresentations_card_le hp S u)

/-- Ordered representations by standard natural digit representatives. -/
def digitRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet S).product (digitSet S)).filter fun ab ↦ ab.1 + ab.2 = n

theorem natCast_mem_residueDigitSet {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) {d : ℕ} (hd : d ∈ digitSet S) :
    (d : ZMod (p ^ 2)) ∈ residueDigitSet S := by
  classical
  rcases Finset.mem_image.mp hd with ⟨z, hz, hzd⟩
  rw [← hzd, z.natCast_zmod_val]
  exact hz

/-- The natural representative digit set has at most `144` ordered
representations of every integer. -/
theorem digitRepresentations_card_le {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (n : ℕ) :
    (digitRepresentations S n).card ≤ 144 := by
  classical
  let f : ℕ × ℕ → ZMod (p ^ 2) × ZMod (p ^ 2) :=
    fun ab ↦ (ab.1, ab.2)
  have hmaps : Set.MapsTo f (digitRepresentations S n : Set _)
      (residueRepresentations S (n : ZMod (p ^ 2)) : Set _) := by
    rintro ⟨x, y⟩ hab
    have hprod := (Finset.mem_filter.mp hab).1
    have hsum := (Finset.mem_filter.mp hab).2
    have hxa := (Finset.mem_product.mp hprod).1
    have hxb := (Finset.mem_product.mp hprod).2
    rcases Finset.mem_image.mp hxa with ⟨za, hza, hxaeq⟩
    rcases Finset.mem_image.mp hxb with ⟨zb, hzb, hxbeq⟩
    simp only at hsum hxaeq hxbeq
    subst x
    subst y
    change f (za.val, zb.val) ∈
      ((residueDigitSet S).product (residueDigitSet S)).filter
        (fun ab ↦ ab.1 + ab.2 = (n : ZMod (p ^ 2)))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa [f] using hza
    · simpa [f] using hzb
    · dsimp [f]
      rw [← Nat.cast_add, hsum]
  have hinj : Set.InjOn f (digitRepresentations S n : Set _) := by
    intro ab hab cd hcd heq
    have habp := (Finset.mem_filter.mp hab).1
    have hcdp := (Finset.mem_filter.mp hcd).1
    have hab1 := (Finset.mem_product.mp habp).1
    have hab2 := (Finset.mem_product.mp habp).2
    have hcd1 := (Finset.mem_product.mp hcdp).1
    have hcd2 := (Finset.mem_product.mp hcdp).2
    have ha_lt := mem_digitSet_lt S hp.pos hab1
    have hb_lt := mem_digitSet_lt S hp.pos hab2
    have hc_lt := mem_digitSet_lt S hp.pos hcd1
    have hd_lt := mem_digitSet_lt S hp.pos hcd2
    apply Prod.ext
    · have hz := congrArg Prod.fst heq
      simpa [f, ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hc_lt] using
        congrArg ZMod.val hz
    · have hz := congrArg Prod.snd heq
      simpa [f, ZMod.val_natCast_of_lt hb_lt, ZMod.val_natCast_of_lt hd_lt] using
        congrArg ZMod.val hz
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans
    (residueRepresentations_card_le hp S (n : ZMod (p ^ 2)))

/-- Ordered natural digit pairs whose sum lies in a prescribed residue class
modulo `p^2`.  This is the local multiplicity interface used in the global
mixed-radix count. -/
def digitModRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (r : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet S).product (digitSet S)).filter fun ab ↦
    (ab.1 + ab.2) % (p ^ 2) = r

/-- Every residue class modulo `p^2` has at most `144` ordered
representations by natural digits. -/
theorem digitModRepresentations_card_le {p : ℕ} [NeZero p]
    (hp : p.Prime) (S : CoefficientSystem p) (r : ℕ) (hr : r < p ^ 2) :
    (digitModRepresentations S r).card ≤ 144 := by
  classical
  let f : ℕ × ℕ → ZMod (p ^ 2) × ZMod (p ^ 2) :=
    fun ab ↦ (ab.1, ab.2)
  have hmaps : Set.MapsTo f (digitModRepresentations S r : Set _)
      (residueRepresentations S (r : ZMod (p ^ 2)) : Set _) := by
    intro ab hab
    have hprod := (Finset.mem_filter.mp hab).1
    have hsum := (Finset.mem_filter.mp hab).2
    have hxa := (Finset.mem_product.mp hprod).1
    have hxb := (Finset.mem_product.mp hprod).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨natCast_mem_residueDigitSet S hxa,
      natCast_mem_residueDigitSet S hxb⟩, ?_⟩
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
    show ab.1 + ab.2 ≡ r [MOD p ^ 2]
    simp only [Nat.ModEq, hsum, Nat.mod_eq_of_lt hr]
  have hinj : Set.InjOn f (digitModRepresentations S r : Set _) := by
    intro ab hab cd hcd heq
    have habp := (Finset.mem_filter.mp hab).1
    have hcdp := (Finset.mem_filter.mp hcd).1
    have hab1 := (Finset.mem_product.mp habp).1
    have hab2 := (Finset.mem_product.mp habp).2
    have hcd1 := (Finset.mem_product.mp hcdp).1
    have hcd2 := (Finset.mem_product.mp hcdp).2
    have ha_lt := mem_digitSet_lt S hp.pos hab1
    have hb_lt := mem_digitSet_lt S hp.pos hab2
    have hc_lt := mem_digitSet_lt S hp.pos hcd1
    have hd_lt := mem_digitSet_lt S hp.pos hcd2
    apply Prod.ext
    · have hz := congrArg Prod.fst heq
      simpa [f, ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hc_lt] using
        congrArg ZMod.val hz
    · have hz := congrArg Prod.snd heq
      simpa [f, ZMod.val_natCast_of_lt hb_lt, ZMod.val_natCast_of_lt hd_lt] using
        congrArg ZMod.val hz
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans
    (residueRepresentations_card_le hp S (r : ZMod (p ^ 2)))

/-- Carry-aware local coverage in exactly the form required by the
mixed-radix construction. -/
theorem digit_carryCover {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (r c : ℕ) (hr : r < p ^ 2) (hc : c ≤ 1) :
    ∃ x ∈ digitSet S, ∃ y ∈ digitSet S, ∃ c' ≤ 1,
      x + y + c = r + p ^ 2 * c' := by
  classical
  let u : ZMod (p ^ 2) := (r : ZMod (p ^ 2)) - c
  rcases residueDigitSet_add_cover hp S u with ⟨a, ha, b, hb, hab⟩
  let x := a.val
  let y := b.val
  have hx : x ∈ digitSet S := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hy : y ∈ digitSet S := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hxlt : x < p ^ 2 := mem_digitSet_lt S hp.pos hx
  have hylt : y < p ^ 2 := mem_digitSet_lt S hp.pos hy
  let N := x + y + c
  have hcast : (N : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
    dsimp [N, x, y]
    rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, hab]
    dsimp [u]
    ring
  have hmodEq : N ≡ r [MOD p ^ 2] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hcast
  have hmod : N % (p ^ 2) = r := by
    rw [hmodEq]
    exact Nat.mod_eq_of_lt hr
  let c' := N / (p ^ 2)
  have hbase : 0 < p ^ 2 := pow_pos hp.pos 2
  have hNlt : N < 2 * (p ^ 2) := by
    dsimp [N, x, y]
    omega
  have hc'lt : c' < 2 := by
    exact (Nat.div_lt_iff_lt_mul hbase).2 (by simpa [Nat.mul_comm] using hNlt)
  refine ⟨x, hx, y, hy, c', by omega, ?_⟩
  have hdecomp := Nat.mod_add_div N (p ^ 2)
  dsimp [c']
  omega

end Erdos29.ModularLift
