import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos29.AllowedNonsquare
import ErdosProblems.Erdos29.ModularLift

/-!
# The finite modular ingredient for Erdős Problem 29

This file formalizes the flat-parabola construction used by Ruzsa and by
Jain--Pham--Sawhney--Zakharov.  The finite-field part is kept separate from
the elementary lift from `ZMod p × ZMod p` to `ZMod (p ^ 2)`.
-/

namespace Erdos29.Modular

open scoped BigOperators

private abbrev F (p : ℕ) := ZMod p

/-- The three quadratic coefficients `3, 4, 6`. -/
def coefficient (p : ℕ) : Fin 3 → F p
  | i => if i = 0 then 3 else if i = 1 then 4 else 6

/-- The three carry-correcting shifts `-1, 0, 1`. -/
def shift (p : ℕ) : Fin 3 → F p
  | i => if i = 0 then -1 else if i = 1 then 0 else 1

@[simp] lemma coefficient_zero (p : ℕ) : coefficient p 0 = 3 := by simp [coefficient]
@[simp] lemma coefficient_one (p : ℕ) : coefficient p 1 = 4 := by simp [coefficient]
@[simp] lemma coefficient_two (p : ℕ) : coefficient p 2 = 6 := by simp [coefficient]

@[simp] lemma shift_zero (p : ℕ) : shift p 0 = -1 := by simp [shift]
@[simp] lemma shift_one (p : ℕ) : shift p 1 = 0 := by simp [shift]
@[simp] lemma shift_two (p : ℕ) : shift p 2 = 1 := by simp [shift]

/-- A tagged point on one of the three shifted parabolas. -/
abbrev Parameter (p : ℕ) := Fin 3 × Fin 3 × F p

/-- The high coordinate of a tagged point. -/
def high (p : ℕ) (a : Parameter p) : F p :=
  2 * coefficient p a.1 * a.2.2 ^ 2 + shift p a.2.1

/-- The unshifted parabola equation used to cover `F_p²`. -/
def parabolaEquation (c d x y : F p) (q : F p × F p) : Prop :=
  x + y = q.1 ∧ c * x ^ 2 + d * y ^ 2 = q.2

private lemma two_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) : (2 : F p) ≠ 0 := by
  change ¬ (((2 : ℕ) : ZMod p) = 0)
  rw [ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

private lemma three_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) : (3 : F p) ≠ 0 := by
  change ¬ (((3 : ℕ) : ZMod p) = 0)
  rw [ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

private lemma four_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) : (4 : F p) ≠ 0 := by
  change ¬ (((4 : ℕ) : ZMod p) = 0)
  rw [ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- The two pairs of parabolas cover every point of `F_p²` when `2` is a
nonsquare.  This is the finite-field heart of Ruzsa's construction. -/
theorem exists_parabola_representation {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (h2 : ¬ IsSquare (2 : F p)) (u v : F p) :
    (∃ x y, x + y = u ∧ 3 * x ^ 2 + 6 * y ^ 2 = v) ∨
      ∃ x y, x + y = u ∧ 4 * x ^ 2 + 4 * y ^ 2 = v := by
  letI : Fact p.Prime := ⟨hp⟩
  let T : F p := v - 2 * u ^ 2
  by_cases hT : IsSquare T
  · rcases hT with ⟨z, hz⟩
    left
    refine ⟨(2 * u + z) / 3, (u - z) / 3, ?_, ?_⟩
    · field_simp [three_ne_zero hp hp11]
      ring
    · dsimp [T] at hz
      have hv : v = 2 * u ^ 2 + z ^ 2 := by
        linear_combination hz
      rw [hv]
      field_simp [three_ne_zero hp hp11]
      ring
  · have hT0 : T ≠ 0 := fun h ↦ hT (h ▸ IsSquare.zero)
    have h20 : (2 : F p) ≠ 0 := fun h ↦ h2 (h ▸ IsSquare.zero)
    have hchar : ringChar (F p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    have hprod : IsSquare ((2 : F p) * T) := by
      have hc2 : quadraticChar (F p) (2 : F p) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr h2
      have hcT : quadraticChar (F p) T = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hT
      have hc : quadraticChar (F p) ((2 : F p) * T) = 1 := by
        rw [map_mul, hc2, hcT]
        norm_num
      exact (quadraticChar_one_iff_isSquare (mul_ne_zero h20 hT0)).mp hc
    rcases hprod with ⟨z, hz⟩
    right
    refine ⟨(2 * u + z) / 4, (2 * u - z) / 4, ?_, ?_⟩
    · field_simp [four_ne_zero hp hp11]
      ring
    · dsimp [T] at hz
      have hv : v = 2 * u ^ 2 + z ^ 2 / 2 := by
        field_simp [two_ne_zero hp hp11]
        linear_combination hz
      rw [hv]
      field_simp [two_ne_zero hp hp11, four_ne_zero hp hp11]
      ring

/-- Encode a low coordinate and a high coordinate as a residue modulo `p²`. -/
def encode (p : ℕ) (x q : F p) : ZMod (p ^ 2) :=
  (x.val + p * q.val : ℕ)

/-- The residue represented by a tagged shifted-parabola parameter. -/
def value (p : ℕ) (a : Parameter p) : ZMod (p ^ 2) :=
  encode p a.2.2 (high p a)

/-- The explicit finite modular digit set. -/
def legacyDigitSetZMod (p : ℕ) : Finset (ZMod (p ^ 2)) :=
  if hp : 0 < p then
    letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
    Finset.univ.image (value p)
  else ∅

@[simp] theorem value_mem_legacyDigitSetZMod (p : ℕ) (hp : 0 < p) (a : Parameter p) :
    value p a ∈ legacyDigitSetZMod p := by
  classical
  simp only [legacyDigitSetZMod, dif_pos hp, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

private lemma value_add_eq_of_carry {p : ℕ} (hp0 : 0 < p) (a b : Parameter p)
    (u : ZMod (p ^ 2)) (r h e : ℕ)
    (hlow : a.2.2.val + b.2.2.val = r + p * e)
    (hhigh : high p a + high p b + (e : F p) = (h : F p))
    (hu : u.val = r + p * h) : value p a + value p b = u := by
  haveI : NeZero p := ⟨Nat.ne_of_gt hp0⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  have hm : (high p a).val + (high p b).val + e ≡ h [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hhigh
  have hm' := hm.mul_left' p
  have hm'' := Nat.ModEq.add_left r hm'
  rw [← u.natCast_zmod_val]
  change ((a.2.2.val + p * (high p a).val : ℕ) : ZMod (p ^ 2)) +
      (b.2.2.val + p * (high p b).val : ℕ) = (u.val : ZMod (p ^ 2))
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  have hraw : a.2.2.val + p * (high p a).val +
      (b.2.2.val + p * (high p b).val) =
      r + p * ((high p a).val + (high p b).val + e) := by
    calc
      a.2.2.val + p * (high p a).val + (b.2.2.val + p * (high p b).val) =
          (a.2.2.val + b.2.2.val) + p * ((high p a).val + (high p b).val) := by ring
      _ = (r + p * e) + p * ((high p a).val + (high p b).val) := by rw [hlow]
      _ = r + p * ((high p a).val + (high p b).val + e) := by ring
  rw [hraw, hu]
  simpa only [pow_two] using hm''

private lemma high_add_eq {p : ℕ} (i j s t : Fin 3) (x y : F p) (q e η h : ℕ)
    (hcurve : coefficient p i * x ^ 2 + coefficient p j * y ^ 2 = (q : F p))
    (hshift : shift p s + shift p t + (e : F p) = (η : F p))
    (hh : 2 * q + η = h) :
    high p (i, s, x) + high p (j, t, y) + (e : F p) = (h : F p) := by
  have hh' : ((2 * q + η : ℕ) : F p) = (h : F p) := congrArg (· : ℕ → F p) hh
  simp only [Nat.cast_add, Nat.cast_mul] at hh'
  dsimp [high]
  linear_combination 2 * hcurve + hshift + hh'

/-- Every residue modulo `p²` is the sum of two tagged values. -/
theorem exists_value_add_eq {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (h2 : ¬ IsSquare (2 : F p)) (u : ZMod (p ^ 2)) :
    ∃ a b : Parameter p, value p a + value p b = u := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := u.val % p
  let h := u.val / p
  let q := h / 2
  let η := h % 2
  have hr : r < p := Nat.mod_lt _ hp0
  have hhval : h < p := by
    apply (Nat.div_lt_iff_lt_mul hp0).2
    simpa only [pow_two] using u.val_lt
  have hη : η = 0 ∨ η = 1 := Nat.mod_two_eq_zero_or_one h
  have hhq : 2 * q + η = h := by
    dsimp [q, η]
    omega
  have hu : u.val = r + p * h := by
    dsimp [r, h]
    exact (Nat.mod_add_div u.val p).symm
  rcases exists_parabola_representation hp hp11 h2 (r : F p) (q : F p) with
      h36 | h44
  · rcases h36 with ⟨x, y, hxy, hcurve⟩
    have haddval : (x + y).val = r := by
      rw [hxy]
      exact ZMod.val_natCast_of_lt hr
    have hlow : x.val + y.val = r ∨ x.val + y.val = r + p := by
      by_cases hs : x.val + y.val < p
      · left
        rw [← ZMod.val_add_of_lt hs, haddval]
      · right
        calc
          x.val + y.val = (x + y).val + p := ZMod.val_add_val_of_le (not_lt.mp hs)
          _ = r + p := by rw [haddval]
    rcases hlow with hlow | hlow
    · rcases hη with hη | hη
      · refine ⟨(0, 1, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(0, 2, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]
    · rcases hη with hη | hη
      · refine ⟨(0, 0, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(0, 1, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]
  · rcases h44 with ⟨x, y, hxy, hcurve⟩
    have haddval : (x + y).val = r := by
      rw [hxy]
      exact ZMod.val_natCast_of_lt hr
    have hlow : x.val + y.val = r ∨ x.val + y.val = r + p := by
      by_cases hs : x.val + y.val < p
      · left
        rw [← ZMod.val_add_of_lt hs, haddval]
      · right
        calc
          x.val + y.val = (x + y).val + p := ZMod.val_add_val_of_le (not_lt.mp hs)
          _ = r + p := by rw [haddval]
    rcases hlow with hlow | hlow
    · rcases hη with hη | hη
      · refine ⟨(1, 1, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(1, 2, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]
    · rcases hη with hη | hη
      · refine ⟨(1, 0, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(1, 1, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]

/-- The explicit digit set covers every residue by two summands. -/
theorem legacyDigitSetZMod_add_cover {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (h2 : ¬ IsSquare (2 : F p)) (u : ZMod (p ^ 2)) :
    ∃ a ∈ legacyDigitSetZMod p, ∃ b ∈ legacyDigitSetZMod p, a + b = u := by
  rcases exists_value_add_eq hp hp11 h2 u with ⟨a, b, hab⟩
  exact ⟨value p a, value_mem_legacyDigitSetZMod p hp.pos a,
    value p b, value_mem_legacyDigitSetZMod p hp.pos b, hab⟩

/-! ## The all-prime refinement -/

/-- Coefficients `2, 1+t, 1+t⁻¹` used for an arbitrary chosen nonsquare `t`. -/
def allCoefficient (p : ℕ) (t : F p) : Fin 3 → F p
  | i => if i = 0 then 2 else if i = 1 then 1 + t else 1 + t⁻¹

@[simp] lemma allCoefficient_zero (p : ℕ) (t : F p) : allCoefficient p t 0 = 2 := by
  simp [allCoefficient]

@[simp] lemma allCoefficient_one (p : ℕ) (t : F p) : allCoefficient p t 1 = 1 + t := by
  simp [allCoefficient]

@[simp] lemma allCoefficient_two (p : ℕ) (t : F p) : allCoefficient p t 2 = 1 + t⁻¹ := by
  simp [allCoefficient]

/-- The two lift shifts `-1,0`. -/
def allShift (p : ℕ) : Fin 2 → F p
  | i => if i = 0 then -1 else 0

@[simp] lemma allShift_zero (p : ℕ) : allShift p 0 = -1 := by simp [allShift]
@[simp] lemma allShift_one (p : ℕ) : allShift p 1 = 0 := by simp [allShift]

/-- The three all-prime parabolas cover every point of `F_p²`. -/
theorem exists_all_parabola_representation {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (t : F p) (ht : ¬ IsSquare t) (ht1 : t ≠ -1) (u v : F p) :
    ∃ i j : Fin 3, ∃ x y : F p,
      x + y = u ∧ allCoefficient p t i * x ^ 2 + allCoefficient p t j * y ^ 2 = v := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : F p) ≠ 0 := two_ne_zero hp hp11
  have ht0 : t ≠ 0 := fun h ↦ ht (h ▸ IsSquare.zero)
  have htadd : t + 1 ≠ 0 := by
    intro h
    apply ht1
    linear_combination h
  let T : F p := v - u ^ 2
  by_cases hT : IsSquare T
  · rcases hT with ⟨z, hz⟩
    refine ⟨0, 0, (u + z) / 2, (u - z) / 2, ?_, ?_⟩
    · field_simp [htwo]
      ring
    · dsimp [T] at hz
      have hv : v = u ^ 2 + z ^ 2 := by linear_combination hz
      rw [hv]
      simp only [allCoefficient_zero]
      field_simp [htwo]
      ring
  · have hT0 : T ≠ 0 := fun h ↦ hT (h ▸ IsSquare.zero)
    have hprod : IsSquare (t * T) := by
      have hct : quadraticChar (F p) t = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr ht
      have hcT : quadraticChar (F p) T = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hT
      have hc : quadraticChar (F p) (t * T) = 1 := by
        rw [map_mul, hct, hcT]
        norm_num
      exact (quadraticChar_one_iff_isSquare (mul_ne_zero ht0 hT0)).mp hc
    rcases hprod with ⟨z, hz⟩
    refine ⟨1, 2, (u + z) / (t + 1), (t * u - z) / (t + 1), ?_, ?_⟩
    · field_simp [htadd]
      ring
    · dsimp [T] at hz
      simp only [allCoefficient_one, allCoefficient_two]
      rw [inv_eq_one_div]
      field_simp [ht0, htadd]
      linear_combination -(t + 1) ^ 2 * hz

/-- Tagged parameters for the all-prime construction. -/
abbrev AllParameter (p : ℕ) := Fin 3 × Fin 2 × F p

/-- High digit in the all-prime construction. -/
def allHigh (p : ℕ) (t : F p) (a : AllParameter p) : F p :=
  allCoefficient p t a.1 * a.2.2 ^ 2 + allShift p a.2.1

/-- Lift an all-prime parameter to `ZMod (p²)`. -/
def allValue (p : ℕ) (t : F p) (a : AllParameter p) : ZMod (p ^ 2) :=
  encode p a.2.2 (allHigh p t a)

/-- The finite set of residues produced by all-prime parameters. -/
def allDigitSetZMod (p : ℕ) (t : F p) : Finset (ZMod (p ^ 2)) :=
  if hp : 0 < p then
    letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
    Finset.univ.image (allValue p t)
  else ∅

@[simp] theorem allValue_mem (p : ℕ) (hp : 0 < p) (t : F p) (a : AllParameter p) :
    allValue p t a ∈ allDigitSetZMod p t := by
  classical
  simp only [allDigitSetZMod, dif_pos hp, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

private lemma allValue_add_eq_of_carry {p : ℕ} (hp0 : 0 < p) (t : F p)
    (a b : AllParameter p) (u : ZMod (p ^ 2)) (r h e : ℕ)
    (hlow : a.2.2.val + b.2.2.val = r + p * e)
    (hhigh : allHigh p t a + allHigh p t b + (e : F p) = (h : F p))
    (hu : u.val = r + p * h) : allValue p t a + allValue p t b = u := by
  haveI : NeZero p := ⟨Nat.ne_of_gt hp0⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  have hm : (allHigh p t a).val + (allHigh p t b).val + e ≡ h [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hhigh
  have hm'' := Nat.ModEq.add_left r (hm.mul_left' p)
  rw [← u.natCast_zmod_val]
  change ((a.2.2.val + p * (allHigh p t a).val : ℕ) : ZMod (p ^ 2)) +
      (b.2.2.val + p * (allHigh p t b).val : ℕ) = (u.val : ZMod (p ^ 2))
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  have hraw : a.2.2.val + p * (allHigh p t a).val +
      (b.2.2.val + p * (allHigh p t b).val) =
      r + p * ((allHigh p t a).val + (allHigh p t b).val + e) := by
    calc
      a.2.2.val + p * (allHigh p t a).val +
          (b.2.2.val + p * (allHigh p t b).val) =
          (a.2.2.val + b.2.2.val) +
            p * ((allHigh p t a).val + (allHigh p t b).val) := by ring
      _ = (r + p * e) + p * ((allHigh p t a).val + (allHigh p t b).val) := by rw [hlow]
      _ = r + p * ((allHigh p t a).val + (allHigh p t b).val + e) := by ring
  rw [hraw, hu]
  simpa only [pow_two] using hm''

private lemma allHigh_add_eq {p : ℕ} (t : F p) (i j : Fin 3) (s w : Fin 2)
    (x y : F p) (h e : ℕ)
    (hcurve : allCoefficient p t i * x ^ 2 + allCoefficient p t j * y ^ 2 = (h : F p))
    (hshift : allShift p s + allShift p w + (e : F p) = 0) :
    allHigh p t (i, s, x) + allHigh p t (j, w, y) + (e : F p) = (h : F p) := by
  dsimp [allHigh]
  linear_combination hcurve + hshift

/-- All-prime modular coverage for any admissible nonsquare `t`. -/
theorem exists_allValue_add_eq {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (t : F p) (ht : ¬ IsSquare t) (ht1 : t ≠ -1) (u : ZMod (p ^ 2)) :
    ∃ a b : AllParameter p, allValue p t a + allValue p t b = u := by
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
  rcases exists_all_parabola_representation hp hp11 t ht ht1 (r : F p) (h : F p) with
    ⟨i, j, x, y, hxy, hcurve⟩
  have haddval : (x + y).val = r := by
    rw [hxy]
    exact ZMod.val_natCast_of_lt hr
  by_cases hs : x.val + y.val < p
  · have hlow : x.val + y.val = r := by rw [← ZMod.val_add_of_lt hs, haddval]
    refine ⟨(i, 1, x), (j, 1, y), allValue_add_eq_of_carry hp0 t _ _ u r h 0 ?_ ?_ hu⟩
    · simpa using hlow
    · apply allHigh_add_eq (h := h) (e := 0) <;> simp_all [allShift]
  · have hlow : x.val + y.val = r + p := by
      calc
        x.val + y.val = (x + y).val + p := ZMod.val_add_val_of_le (not_lt.mp hs)
        _ = r + p := by rw [haddval]
    refine ⟨(i, 0, x), (j, 1, y), allValue_add_eq_of_carry hp0 t _ _ u r h 1 ?_ ?_ hu⟩
    · simpa using hlow
    · apply allHigh_add_eq (h := h) (e := 1) <;> simp_all [allShift]

/-- Natural representatives of the all-prime digit residues. -/
def allDigitSetNat (p : ℕ) (t : F p) : Finset ℕ :=
  (allDigitSetZMod p t).image ZMod.val

theorem allDigitSetNat_subset_range (p : ℕ) (hp : 0 < p) (t : F p) :
    allDigitSetNat p t ⊆ Finset.range (p ^ 2) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  intro a ha
  simp only [allDigitSetNat, Finset.mem_image] at ha
  rcases ha with ⟨z, -, rfl⟩
  exact Finset.mem_range.mpr z.val_lt

/-- Natural-form modular coverage, in the exact shape used by mixed-radix digits. -/
theorem allDigitSetNat_cover {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (t : F p) (ht : ¬ IsSquare t) (ht1 : t ≠ -1) {r : ℕ} (hr : r < p ^ 2) :
    ∃ a ∈ allDigitSetNat p t, ∃ b ∈ allDigitSetNat p t, (a + b) % (p ^ 2) = r := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases exists_allValue_add_eq hp hp11 t ht ht1 (r : ZMod (p ^ 2)) with ⟨a, b, hab⟩
  refine ⟨(allValue p t a).val, ?_, (allValue p t b).val, ?_, ?_⟩
  · simp only [allDigitSetNat, Finset.mem_image]
    exact ⟨allValue p t a, allValue_mem p hp.pos t a, rfl⟩
  · simp only [allDigitSetNat, Finset.mem_image]
    exact ⟨allValue p t b, allValue_mem p hp.pos t b, rfl⟩
  · rw [← ZMod.val_add, hab, ZMod.val_natCast_of_lt hr]

/-! ## Public local digit set -/

/-- The coefficient system obtained from the bounded-search allowed nonsquare.
It works for every prime at least `11`; no congruence restriction on the prime
is imposed. -/
def allPrimeCoefficientSystem (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) :
    ModularLift.CoefficientSystem p where
  coeff := allCoefficient p (Erdos29.allowedT p)
  cover := exists_all_parabola_representation hp hp11 (Erdos29.allowedT p)
    (Erdos29.allowedT_not_isSquare hp hp11) (Erdos29.allowedT_ne_neg_one hp hp11)
  coeff_add_ne_zero := by
    intro i j
    apply Erdos29.parabolaCoefficients_add_ne_zero hp hp11
    · fin_cases i <;> simp [allCoefficient, Erdos29.parabolaCoefficients]
    · fin_cases j <;> simp [allCoefficient, Erdos29.parabolaCoefficients]

/-- The completely explicit local digit set used in the global construction.
The nonsquare is selected by the bounded search in `AllowedNonsquare.lean`.
In particular, the definition itself does not contain primality proofs. -/
def digitSet (p : ℕ) : Finset ℕ :=
  allDigitSetNat p (Erdos29.allowedT p)

theorem digitSet_subset_range {p : ℕ} (hp : p.Prime) :
    digitSet p ⊆ Finset.range (p ^ 2) := by
  exact allDigitSetNat_subset_range p hp.pos (Erdos29.allowedT p)

theorem digitSet_mem_lt {p d : ℕ} (hp : p.Prime) (hd : d ∈ digitSet p) :
    d < p ^ 2 := Finset.mem_range.mp (digitSet_subset_range hp hd)

/-- Exact modular coverage by natural representatives. -/
theorem digitSet_cover {p r : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hr : r < p ^ 2) :
    ∃ a ∈ digitSet p, ∃ b ∈ digitSet p, (a + b) % (p ^ 2) = r := by
  exact allDigitSetNat_cover hp hp11 (Erdos29.allowedT p)
    (Erdos29.allowedT_not_isSquare hp hp11)
    (Erdos29.allowedT_ne_neg_one hp hp11) hr

/-- At a prime at least `11`, the proof-independent digit set agrees with the
natural digit set attached to `allPrimeCoefficientSystem`. -/
theorem digitSet_eq_lift {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    digitSet p = ModularLift.digitSet (allPrimeCoefficientSystem p hp hp11) := by
  classical
  simp only [digitSet, allDigitSetNat, allDigitSetZMod, dif_pos hp.pos,
    ModularLift.digitSet, ModularLift.residueDigitSet]
  congr 2

/-- Carry-aware local coverage, with an incoming and outgoing carry in
`{0,1}`, in the exact natural-number form used by mixed-radix arguments. -/
theorem digitSet_carryCover {p r c : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hr : r < p ^ 2) (hc : c ≤ 1) :
    ∃ x ∈ digitSet p, ∃ y ∈ digitSet p, ∃ c' ≤ 1,
      x + y + c = r + p ^ 2 * c' := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [digitSet_eq_lift hp hp11]
  exact ModularLift.digit_carryCover hp (allPrimeCoefficientSystem p hp hp11)
    r c hr hc

/-- Ordered representations of `n` by the explicit natural local digits. -/
def digitRepresentations (p n : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet p).product (digitSet p)).filter fun ab ↦ ab.1 + ab.2 = n

/-- Every integer has at most `144` ordered exact-sum representations by the
local digit set. -/
theorem digitRepresentations_card_le {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (n : ℕ) : (digitRepresentations p n).card ≤ 144 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [digitRepresentations, digitSet_eq_lift hp hp11]
  exact ModularLift.digitRepresentations_card_le hp
    (allPrimeCoefficientSystem p hp hp11) n

/-- Ordered natural digit pairs whose sum is a prescribed residue modulo
`p^2`. -/
def digitModRepresentations (p r : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet p).product (digitSet p)).filter fun ab ↦
    (ab.1 + ab.2) % (p ^ 2) = r

/-- The explicit digit set has at most `144` ordered representations of each
residue modulo `p^2`. -/
theorem digitModRepresentations_card_le {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (r : ℕ) (hr : r < p ^ 2) : (digitModRepresentations p r).card ≤ 144 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [digitModRepresentations, digitSet_eq_lift hp hp11]
  exact ModularLift.digitModRepresentations_card_le hp
    (allPrimeCoefficientSystem p hp hp11) r hr

end Erdos29.Modular
