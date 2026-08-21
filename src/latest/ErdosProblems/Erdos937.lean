import ErdosProblems.Erdos937.Erdos937Elliptic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Int.Interval

namespace Erdos937

open Nat Set

/-! ## The orbit modulo 73

The short model has both coefficients divisible by 73.  Thus its reduction is the cuspidal
cubic `Y² = X³`; on its nonsingular locus multiplication by five sends `(X,Y)` to
`(X / 25, Y / 125)`.  We record reduction of rational numbers by an elementary relation,
so no nonexistent homomorphism from all of `ℚ` to `ZMod 73` is used. -/

private abbrev F73 := ZMod 73

private instance : Fact (Nat.Prime 73) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- `Reduces73 q z` means that `q` has a presentation with denominator prime to 73 whose
reduction is `z`. -/
private def Reduces73 (q : ℚ) (z : F73) : Prop :=
  ∃ a b : ℤ, (b : F73) ≠ 0 ∧
    q = (a : ℚ) / (b : ℚ) ∧ z = (a : F73) / (b : F73)

private lemma reduces73_int (a : ℤ) : Reduces73 (a : ℚ) (a : F73) := by
  refine ⟨a, 1, by norm_num, ?_, ?_⟩ <;> norm_num

private lemma reduces73_add {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) : Reduces73 (q + r) (x + y) := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  rcases hr with ⟨c, d, hd, hr, hy⟩
  have hb0 : b ≠ 0 := by intro h; subst b; simp at hb
  have hd0 : d ≠ 0 := by intro h; subst d; simp at hd
  refine ⟨a * d + c * b, b * d, ?_, ?_, ?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hb hd
  · rw [hq, hr]
    push_cast
    field_simp [hb0, hd0]
  · rw [hx, hy]
    push_cast
    field_simp [hb, hd]

private lemma reduces73_neg {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (-q) (-x) := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  refine ⟨-a, b, hb, ?_, ?_⟩
  · rw [hq]
    push_cast
    ring
  · rw [hx]
    push_cast
    ring

private lemma reduces73_sub {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) : Reduces73 (q - r) (x - y) := by
  simpa [sub_eq_add_neg] using reduces73_add hq (reduces73_neg hr)

private lemma reduces73_mul {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) : Reduces73 (q * r) (x * y) := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  rcases hr with ⟨c, d, hd, hr, hy⟩
  have hb0 : b ≠ 0 := by intro h; subst b; simp at hb
  have hd0 : d ≠ 0 := by intro h; subst d; simp at hd
  refine ⟨a * c, b * d, ?_, ?_, ?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hb hd
  · rw [hq, hr]
    push_cast
    field_simp [hb0, hd0]
  · rw [hx, hy]
    push_cast
    field_simp [hb, hd]

private lemma reduces73_pow {q : ℚ} {x : F73} (hq : Reduces73 q x) (n : ℕ) :
    Reduces73 (q ^ n) (x ^ n) := by
  induction n with
  | zero => simpa using reduces73_int 1
  | succ n ih => simpa [pow_succ] using reduces73_mul ih hq

private lemma reduces73_inv {q : ℚ} {x : F73} (hq : Reduces73 q x) (hx0 : x ≠ 0) :
    Reduces73 q⁻¹ x⁻¹ := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  have ha : (a : F73) ≠ 0 := by
    intro ha
    apply hx0
    rw [hx, ha]
    simp
  have ha0 : a ≠ 0 := by intro h; subst a; simp at ha
  have hb0 : b ≠ 0 := by intro h; subst b; simp at hb
  refine ⟨b, a, ha, ?_, ?_⟩
  · rw [hq]
    push_cast
    field_simp [ha0, hb0]
  · rw [hx]
    push_cast
    field_simp [ha, hb]

private lemma reduces73_div {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) (hy0 : y ≠ 0) :
    Reduces73 (q / r) (x / y) := by
  simpa [div_eq_mul_inv] using reduces73_mul hq (reduces73_inv hr hy0)

private lemma reduces73_right {q : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hxy : x = y) : Reduces73 q y := by
  simpa [hxy] using hq

private lemma shortA_reduces73 : Reduces73 shortA 0 := by
  convert reduces73_int (-478842624) using 1
  · norm_num [shortA]
  · decide

private lemma shortB_reduces73 : Reduces73 shortB 0 := by
  convert reduces73_int 3011551764480 using 1
  · norm_num [shortB]
  · decide

private lemma curvePoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (curvePoly q) (x ^ 3) := by
  simpa [curvePoly] using
    reduces73_add (reduces73_add (reduces73_pow hq 3)
      (reduces73_mul shortA_reduces73 hq)) shortB_reduces73

private lemma threePoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (threePoly q) (3 * x ^ 4) := by
  have h3 := reduces73_int 3
  have h6 := reduces73_int 6
  have h12 := reduces73_int 12
  simpa [threePoly] using
    reduces73_sub
      (reduces73_add
        (reduces73_add (reduces73_mul h3 (reduces73_pow hq 4))
          (reduces73_mul (reduces73_mul h6 shortA_reduces73) (reduces73_pow hq 2)))
        (reduces73_mul (reduces73_mul h12 shortB_reduces73) hq))
      (reduces73_pow shortA_reduces73 2)

private lemma fourPoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fourPoly q) (x ^ 6) := by
  have h4 := reduces73_int 4
  have h5 := reduces73_int 5
  have h8 := reduces73_int 8
  have h20 := reduces73_int 20
  have raw := reduces73_sub
      (reduces73_sub
        (reduces73_sub
          (reduces73_sub
            (reduces73_add
              (reduces73_add
                (reduces73_add (reduces73_pow hq 6)
                  (reduces73_mul (reduces73_mul h5 shortA_reduces73)
                    (reduces73_pow hq 4)))
                (reduces73_mul (reduces73_mul h20 shortB_reduces73)
                  (reduces73_pow hq 3)))
              (reduces73_neg (reduces73_mul
                (reduces73_mul h5 (reduces73_pow shortA_reduces73 2))
                (reduces73_pow hq 2))))
            (reduces73_mul
              (reduces73_mul (reduces73_mul h4 shortA_reduces73) shortB_reduces73) hq))
          (reduces73_mul h8 (reduces73_pow shortB_reduces73 2)))
        (reduces73_pow shortA_reduces73 3))
      (reduces73_int 0)
  convert raw using 1
  · simp only [fourPoly, shortA, shortB]
    ring
  · ring

private lemma fivePoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fivePoly q) (5 * x ^ 12) := by
  have hc := curvePoly_reduces73 hq
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul (reduces73_mul (reduces73_int 32) (reduces73_pow hc 2)) h4)
    (reduces73_pow h3 3)
  apply reduces73_right (by simpa [fivePoly] using raw)
  ring

private lemma fivePhi_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fivePhi q) (x ^ 25) := by
  have hc := curvePoly_reduces73 hq
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have h5 := fivePoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul hq (reduces73_pow h5 2))
    (reduces73_mul
      (reduces73_mul
        (reduces73_mul (reduces73_mul (reduces73_int 8) hc) h3) h4)
      (reduces73_sub h5
        (reduces73_mul (reduces73_int 4) (reduces73_pow h4 2))))
  apply reduces73_right (by simpa [fivePhi] using raw)
  ring

private lemma sevenPoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (sevenPoly q) (7 * x ^ 24) := by
  have hc := curvePoly_reduces73 hq
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have h5 := fivePoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul h5 (reduces73_pow h3 3))
    (reduces73_mul
      (reduces73_mul (reduces73_int 128) (reduces73_pow hc 2))
      (reduces73_pow h4 3))
  apply reduces73_right (by simpa [sevenPoly] using raw)
  ring

private lemma fiveYPoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fiveYPoly q) (x ^ 36) := by
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have h5 := fivePoly_reduces73 hq
  have h7 := sevenPoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul (reduces73_mul (reduces73_int 4) (reduces73_pow h4 2)) h7)
    (reduces73_mul (reduces73_pow h3 3)
      (reduces73_pow (reduces73_sub h5
        (reduces73_mul (reduces73_int 4) (reduces73_pow h4 2))) 2))
  apply reduces73_right (by simpa [fiveYPoly] using raw)
  ring

private lemma fiveMap_reduces73 {P : ℚ × ℚ} {x y : F73}
    (hx : Reduces73 P.1 x) (hy : Reduces73 P.2 y) (hx0 : x ≠ 0) :
    Reduces73 (fiveMap P).1 (x / 25) ∧ Reduces73 (fiveMap P).2 (y / 125) := by
  have h5 := fivePoly_reduces73 hx
  have hphi := fivePhi_reduces73 hx
  have hY := fiveYPoly_reduces73 hx
  have h5z : (5 : F73) * x ^ 12 ≠ 0 :=
    mul_ne_zero (by decide) (pow_ne_zero _ hx0)
  constructor
  · have raw := reduces73_div hphi (reduces73_pow h5 2) (pow_ne_zero _ h5z)
    apply reduces73_right (by simpa [fiveMap] using raw)
    field_simp [hx0]
    ring
  · have raw := reduces73_div (reduces73_mul hy hY) (reduces73_pow h5 3)
      (pow_ne_zero _ h5z)
    apply reduces73_right (by simpa [fiveMap] using raw)
    field_simp [hx0]
    ring

private lemma shortStart_reduces73 :
    Reduces73 shortStart.1 48 ∧ Reduces73 shortStart.2 17 := by
  constructor
  · refine ⟨21443383536, 511225, by decide, ?_, ?_⟩
    simp [shortStart, Rat.divInt_eq_div]
    field_simp [show (511225 : F73) ≠ 0 by decide] <;> decide
  · refine ⟨-2752977651830784, 365525875, by decide, ?_, ?_⟩
    simp [shortStart, Rat.divInt_eq_div]
    field_simp [show (365525875 : F73) ≠ 0 by decide] <;> decide

private def orbitX73 (n : ℕ) : F73 := 48 / 25 ^ n
private def orbitY73 (n : ℕ) : F73 := 17 / 125 ^ n

private lemma orbit_reduces73 (n : ℕ) :
    Reduces73 (orbit n).1 (orbitX73 n) ∧ Reduces73 (orbit n).2 (orbitY73 n) := by
  induction n with
  | zero => simpa [orbit, orbitX73, orbitY73] using shortStart_reduces73
  | succ n ih =>
      rw [orbit, Function.iterate_succ_apply']
      have hn := fiveMap_reduces73 ih.1 ih.2 (by
        simp only [orbitX73]
        exact div_ne_zero (by decide) (pow_ne_zero _ (by decide)))
      constructor
      · apply reduces73_right hn.1
        simp only [orbitX73, pow_succ]
        field_simp
      · apply reduces73_right hn.2
        simp only [orbitY73, pow_succ]
        field_simp

private lemma orbit_sample_reduces73 (k : ℕ) :
    Reduces73 (orbit (57 + 72 * k)).1 57 ∧
      Reduces73 (orbit (57 + 72 * k)).2 49 := by
  have h := orbit_reduces73 (57 + 72 * k)
  have h25 : (25 : F73) ^ 72 = 1 := by decide
  have h125 : (125 : F73) ^ 72 = 1 := by decide
  constructor
  · apply reduces73_right h.1
    simp only [orbitX73, pow_add, pow_mul, h25, one_pow, mul_one]
    field_simp [show (25 : F73) ≠ 0 by decide] <;> decide
  · apply reduces73_right h.2
    simp only [orbitY73, pow_add, pow_mul, h125, one_pow, mul_one]
    field_simp [show (125 : F73) ≠ 0 by decide] <;> decide

lemma orbit_sample_old_ratio_reduces73 (k : ℕ) :
    Reduces73 (bbcX (orbit (57 + 72 * k)) / bbcY (orbit (57 + 72 * k))) 2 := by
  have h := orbit_sample_reduces73 k
  have hXraw := reduces73_div
    (reduces73_sub h.1 (reduces73_int 17808)) (reduces73_int 36) (by decide)
  have hX : Reduces73 (bbcX (orbit (57 + 72 * k))) 24 := by
    apply reduces73_right (by simpa [bbcX] using hXraw)
    field_simp [show (36 : F73) ≠ 0 by decide] <;> decide
  have hYraw := reduces73_div
    (reduces73_add
      (reduces73_add
        (reduces73_div h.2 (reduces73_int 108) (by decide))
        (reduces73_mul (reduces73_int 128) hX))
      (reduces73_int 3360))
    (reduces73_int 2) (by decide)
  have hY : Reduces73 (bbcY (orbit (57 + 72 * k))) 12 := by
    apply reduces73_right (by simpa [bbcY] using hYraw)
    field_simp [show (108 : F73) ≠ 0 by decide,
      show (2 : F73) ≠ 0 by decide] <;> decide
  have hr := reduces73_div hX hY (by decide)
  apply reduces73_right hr
  field_simp [show (12 : F73) ≠ 0 by decide] <;> decide

private lemma quarticX_num_congr_5329 {P : ℚ × ℚ}
    (h : Reduces73 (bbcX P / bbcY P) 2) :
    (5329 : ℤ) ∣ (quarticX P).num - 290 * ((quarticX P).den : ℤ) := by
  rcases h with ⟨u, v, hv, hr, hred⟩
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  have huv73 : (u : F73) = 2 * (v : F73) := by
    have huv := (div_eq_iff hv).mp hred.symm
    simpa [mul_comm] using huv
  have h73 : (73 : ℤ) ∣ u - 2 * v := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u - 2 * v) 73).mp
    push_cast
    rw [huv73]
    ring
  obtain ⟨s, hs⟩ := h73
  let q := quarticX P
  have hformula : q = ((146 * u - 2 * v : ℤ) : ℚ) / (v : ℚ) := by
    dsimp [q]
    calc
      quarticX P = 146 * (bbcX P / bbcY P) - 2 := by
        simp only [quarticX]
        ring
      _ = 146 * ((u : ℚ) / (v : ℚ)) - 2 := by rw [hr]
      _ = ((146 * u - 2 * v : ℤ) : ℚ) / (v : ℚ) := by
        push_cast
        field_simp [hv0]
  have heqQ :
      (q.num : ℚ) / (q.den : ℚ) =
        ((146 * u - 2 * v : ℤ) : ℚ) / (v : ℚ) := by
    rw [q.num_div_den, hformula]
  have hcross : q.num * v = (146 * u - 2 * v) * (q.den : ℤ) := by
    field_simp [hv0, q.den_nz] at heqQ
    have hi : q.num * v = (q.den : ℤ) * (146 * u - 2 * v) := by
      exact_mod_cast heqQ
    simpa [mul_comm] using hi
  have hprodEq :
      (q.num - 290 * (q.den : ℤ)) * v =
        (73 : ℤ) ^ 2 * (2 * s * (q.den : ℤ)) := by
    calc
      (q.num - 290 * (q.den : ℤ)) * v =
          q.num * v - 290 * (q.den : ℤ) * v := by ring
      _ = (146 * u - 2 * v) * (q.den : ℤ) -
          290 * (q.den : ℤ) * v := by rw [hcross]
      _ = 146 * (u - 2 * v) * (q.den : ℤ) := by ring
      _ = (73 : ℤ) ^ 2 * (2 * s * (q.den : ℤ)) := by rw [hs]; ring
  have hprod : (73 : ℤ) ^ 2 ∣ (q.num - 290 * (q.den : ℤ)) * v :=
    ⟨2 * s * (q.den : ℤ), hprodEq⟩
  have hnot : ¬(73 : ℤ) ∣ v := by
    intro hd
    apply hv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd v 73).2 hd
  have hnotNat : ¬73 ∣ v.natAbs := by
    intro hd
    exact hnot (Int.natCast_dvd.mpr hd)
  have hcopNat : Nat.Coprime (73 ^ 2) v.natAbs :=
    ((show Nat.Prime 73 by decide).coprime_iff_not_dvd.mpr hnotNat).pow_left _
  have hcop : IsCoprime ((73 : ℤ) ^ 2) v := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hcopNat
  change (73 : ℤ) ^ 2 ∣ q.num - 290 * (q.den : ℤ)
  exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hprod)

lemma orbit_sample_quartic_num_congr_5329 (k : ℕ) :
    (5329 : ℤ) ∣ (quarticX (orbit (57 + 72 * k))).num -
      290 * ((quarticX (orbit (57 + 72 * k))).den : ℤ) :=
  quarticX_num_congr_5329 (orbit_sample_old_ratio_reduces73 k)

/-! ## Primitive integral points on the quartic -/

private lemma quartic_dvd_5329 {a b : ℤ}
    (h : (5329 : ℤ) ∣ a - 290 * b) : (5329 : ℤ) ∣ quartic a b := by
  obtain ⟨t, ht⟩ := h
  have ha : a = 290 * b + 5329 * t := by omega
  refine ⟨1290649 * b ^ 4 + 95538768 * b ^ 3 * t +
      2651934218 * b ^ 2 * t ^ 2 + 32714773632 * b * t ^ 3 +
      151334226289 * t ^ 4, ?_⟩
  rw [ha]
  simp only [quartic]
  ring

private lemma rat_eq_int_of_sq_eq_int {r : ℚ} {n : ℤ}
    (h : r ^ 2 = (n : ℚ)) : ∃ c : ℤ, r = (c : ℚ) := by
  have hd := congrArg Rat.den h
  simp only [Rat.den_pow, Rat.den_intCast] at hd
  have hd1 : r.den = 1 := by nlinarith [r.den_pos]
  refine ⟨r.num, ?_⟩
  rw [← r.num_div_den]
  simp [hd1]

/-- Each selected orbit point yields a primitive integral quartic solution with the required
extra factor `73²` in its square coordinate. -/
lemma orbit_sample_primitive_solution (k : ℕ) :
    ∃ a b c : ℤ,
      0 < b ∧ Nat.Coprime a.natAbs b.natAbs ∧
      quartic a b = (73 : ℤ) ^ 3 * c ^ 2 ∧
      quarticX (orbit (57 + 72 * k)) = (a : ℚ) / (b : ℚ) := by
  let P := orbit (57 + 72 * k)
  let q := quarticX P
  let a : ℤ := q.num
  let b : ℤ := q.den
  have hb : 0 < b := by simpa [b] using q.den_pos
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hcop : Nat.Coprime a.natAbs b.natAbs := by
    simpa [a, b] using q.reduced
  have hq : q = (a : ℚ) / (b : ℚ) := by
    simpa [a, b] using q.num_div_den.symm
  have he := BBC_to_quartic (orbit_onCurve (57 + 72 * k))
    (orbit_bbcY_ne_zero (57 + 72 * k))
  change q ^ 4 - 8 * q ^ 3 + 2 * q ^ 2 + 8 * q + 1 =
    73 * quarticY P ^ 2 at he
  rw [hq] at he
  have hhom :
      ((quartic a b : ℤ) : ℚ) =
        73 * (quarticY P * (b : ℚ) ^ 2) ^ 2 := by
    simp only [quartic]
    push_cast
    field_simp [hb0] at he
    linear_combination (norm := ring) he
  have hcon : (5329 : ℤ) ∣ a - 290 * b := by
    simpa [P, q, a, b] using orbit_sample_quartic_num_congr_5329 k
  have hdiv := quartic_dvd_5329 hcon
  obtain ⟨m, hm⟩ := hdiv
  have hrsq :
      (quarticY P * (b : ℚ) ^ 2) ^ 2 = ((73 * m : ℤ) : ℚ) := by
    rw [hm] at hhom
    push_cast at hhom ⊢
    ring_nf at hhom ⊢
    linarith
  obtain ⟨c, hc⟩ := rat_eq_int_of_sq_eq_int hrsq
  have hFc : quartic a b = (73 : ℤ) * c ^ 2 := by
    rw [hc] at hhom
    exact_mod_cast hhom
  obtain ⟨m', hm'⟩ := quartic_dvd_5329 hcon
  have hc2 : (73 : ℤ) ∣ c ^ 2 := by
    refine ⟨m', ?_⟩
    have hcancel : (73 : ℤ) * c ^ 2 = (73 : ℤ) * (73 * m') := by
      rw [← hFc, hm']
      ring
    exact mul_left_cancel₀ (by norm_num : (73 : ℤ) ≠ 0) hcancel
  have hcdiv : (73 : ℤ) ∣ c :=
    (show _root_.Prime (73 : ℤ) by decide).dvd_of_dvd_pow hc2
  obtain ⟨c', rfl⟩ := hcdiv
  refine ⟨a, b, c', hb, hcop, ?_, ?_⟩
  · rw [hFc]
    ring
  · simpa [P, q] using hq

/-! ## Parity normalization -/

/-- The two parameters have opposite parity.  Writing this as oddness of their sum is
particularly convenient for all three square roots below. -/
def OppositeParity (a b : ℤ) : Prop := Odd (a + b)

/-- A primitive quartic solution can be normalized to opposite parity.  If its two
parameters are odd, the half-sum/half-difference substitution divides the square
coordinate by two and preserves the required `73³` signature. -/
lemma orbit_sample_normalized_solution (k : ℕ) :
    ∃ a b c : ℤ,
      Nat.Coprime a.natAbs b.natAbs ∧ OppositeParity a b ∧
      quartic a b = (73 : ℤ) ^ 3 * c ^ 2 ∧
      (quarticX (orbit (57 + 72 * k)) = (a : ℚ) / (b : ℚ) ∨
        quarticX (orbit (57 + 72 * k)) =
          ((a + b : ℤ) : ℚ) / ((a - b : ℤ) : ℚ)) := by
  obtain ⟨a, b, c, hb, hab, hF, hq⟩ := orbit_sample_primitive_solution k
  have habZ : IsCoprime a b := Int.isCoprime_iff_nat_coprime.mpr hab
  rcases Int.even_or_odd a with ha | ha
  · rcases Int.even_or_odd b with hb' | hb'
    · have hu : IsUnit (2 : ℤ) := habZ.isUnit_of_dvd' ha.two_dvd hb'.two_dvd
      exfalso
      have hdiv : (2 : ℤ) ∣ 1 := IsUnit.dvd hu
      norm_num at hdiv
    · exact ⟨a, b, c, hab, ha.add_odd hb', hF, Or.inl hq⟩
  · rcases Int.even_or_odd b with hb' | hb'
    · exact ⟨a, b, c, hab, ha.add_even hb', hF, Or.inl hq⟩
    · obtain ⟨u, hu⟩ := (ha.add_odd hb').two_dvd
      obtain ⟨v, hv⟩ := (ha.sub_odd hb').two_dvd
      have hau : a = u + v := by omega
      have hbv : b = u - v := by omega
      have huvCoprime : Nat.Coprime u.natAbs v.natAbs := by
        apply Int.isCoprime_iff_nat_coprime.mp
        rcases habZ with ⟨r, s, hrs⟩
        refine ⟨r + s, r - s, ?_⟩
        rw [hau, hbv] at hrs
        linear_combination hrs
      have huvParity : OppositeParity u v := by
        rw [OppositeParity, ← hau]
        exact ha
      have hfour : 4 * quartic u v = (73 : ℤ) ^ 3 * c ^ 2 := by
        rw [← hF, hau, hbv]
        simp only [quartic]
        ring
      have htwo : (2 : ℤ) ∣ (73 : ℤ) ^ 3 * c ^ 2 := by
        rw [← hfour]
        exact ⟨2 * quartic u v, by ring⟩
      have hcSq : (2 : ℤ) ∣ c ^ 2 := by
        rcases (show _root_.Prime (2 : ℤ) by decide).dvd_mul.mp htwo with h73 | hc
        · have : (2 : ℤ) ∣ 73 :=
            (show _root_.Prime (2 : ℤ) by decide).dvd_of_dvd_pow h73
          norm_num at this
        · exact hc
      have hc : (2 : ℤ) ∣ c :=
        (show _root_.Prime (2 : ℤ) by decide).dvd_of_dvd_pow hcSq
      obtain ⟨c', rfl⟩ := hc
      have hnormalized : quartic u v = (73 : ℤ) ^ 3 * c' ^ 2 := by
        apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
        rw [hfour]
        ring
      refine ⟨u, v, c', huvCoprime, huvParity, hnormalized, Or.inr ?_⟩
      simpa [hau, hbv] using hq

/-! ## Resultant certificates for pairwise coprimality -/

private lemma odd_apX {a b : ℤ} (h : OppositeParity a b) : Odd (apX a b) := by
  rcases h with ⟨k, hk⟩
  refine ⟨2 * k ^ 2 + 2 * k - b ^ 2, ?_⟩
  have ha : a = 2 * k + 1 - b := by linarith
  rw [ha]
  simp only [apX]
  ring

private lemma odd_apY {a b : ℤ} (h : OppositeParity a b) : Odd (apY a b) := by
  rcases h with ⟨k, hk⟩
  refine ⟨2 * k ^ 2 + 2 * k - a * b, ?_⟩
  have ha : a = 2 * k + 1 - b := by linarith
  rw [ha]
  simp only [apY]
  ring

private lemma odd_apZ {a b : ℤ} (h : OppositeParity a b) : Odd (apZ a b) := by
  rcases h with ⟨k, hk⟩
  refine ⟨2 * k ^ 2 + 2 * k - 2 * a * b - b ^ 2, ?_⟩
  have ha : a = 2 * k + 1 - b := by linarith
  rw [ha]
  simp only [apZ]
  ring

/-- A homogeneous resultant identity proves coprimality once the first form is coprime
to the resultant constant and to the second parameter. -/
private lemma coprime_of_resultant {a b r s C U V t : ℤ} {n : ℕ}
    (hab : Nat.Coprime a.natAbs b.natAbs)
    (hrepr : r = a ^ 2 + b * t) (hC : IsCoprime r C)
    (hid : U * r + V * s = C * b ^ n) : Nat.Coprime r.natAbs s.natAbs := by
  have habZ : IsCoprime a b := Int.isCoprime_iff_nat_coprime.mpr hab
  have hrb : IsCoprime r b := by
    rw [hrepr]
    exact (habZ.pow_left).add_mul_left_left t
  have hrprod : IsCoprime r (C * b ^ n) := hC.mul_right hrb.pow_right
  have hcomb : IsCoprime r (U * r + V * s) := by rw [hid]; exact hrprod
  have hcomb' : IsCoprime r (V * s + U * r) := by simpa [add_comm] using hcomb
  have hVs : IsCoprime r (V * s) := IsCoprime.of_add_mul_right_right hcomb'
  exact Int.isCoprime_iff_nat_coprime.mp hVs.of_mul_right_right

private lemma coprime_apX_apY {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apX a b).natAbs (apY a b).natAbs := by
  have h2 : IsCoprime (apX a b) (2 : ℤ) := Int.isCoprime_two_right.mpr (odd_apX hpar)
  have h4 : IsCoprime (apX a b) (4 : ℤ) := by
    have hp : IsCoprime (apX a b) ((2 : ℤ) ^ 2) := h2.pow_right
    norm_num at hp ⊢
    exact hp
  apply coprime_of_resultant hab (t := 2 * a - b) (C := 4) (n := 3)
    (U := -a - b) (V := a + 3 * b)
  · simp only [apX]
    ring
  · exact h4
  · simp only [apX, apY]
    ring

private lemma coprime_pow_two_of_odd {r : ℤ} (hr : Odd r) (n : ℕ) :
    IsCoprime r ((2 : ℤ) ^ n) :=
  (Int.isCoprime_two_right.mpr hr).pow_right

private lemma coprime_apX_apZ {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apX a b).natAbs (apZ a b).natAbs := by
  have h4 : IsCoprime (apX a b) (4 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apX hpar) 2
  apply coprime_of_resultant hab (t := 2 * a - b) (C := 4) (n := 3)
    (U := a - 2 * b) (V := -a - 2 * b)
  · simp only [apX]
    ring
  · exact h4
  · simp only [apX, apZ]
    ring

private lemma coprime_apY_apZ {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apY a b).natAbs (apZ a b).natAbs := by
  have h4 : IsCoprime (apY a b) (4 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apY hpar) 2
  apply coprime_of_resultant hab (t := b) (C := 4) (n := 3)
    (U := 3 * b - a) (V := a - b)
  · simp only [apY]
    ring
  · exact h4
  · simp only [apY, apZ]
    ring

private abbrev F3 := ZMod 3

private lemma zmod3_apX_zero :
    ∀ x y : F3, x ^ 2 - y ^ 2 + 2 * x * y = 0 → x = 0 ∧ y = 0 := by
  decide

private lemma coprime_apX_three {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) : IsCoprime (apX a b) (3 : ℤ) := by
  have habZ : IsCoprime a b := Int.isCoprime_iff_nat_coprime.mpr hab
  have hnot : ¬(3 : ℤ) ∣ apX a b := by
    intro hd
    have hz : (apX a b : F3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (apX a b) 3).2 hd
    have hz' : (a : F3) ^ 2 - (b : F3) ^ 2 + 2 * (a : F3) * (b : F3) = 0 := by
      simpa [apX] using hz
    have hzero := zmod3_apX_zero (a : F3) (b : F3) hz'
    have hda : (3 : ℤ) ∣ a :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).1 hzero.1
    have hdb : (3 : ℤ) ∣ b :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).1 hzero.2
    have hu : IsUnit (3 : ℤ) := habZ.isUnit_of_dvd' hda hdb
    have hdiv : (3 : ℤ) ∣ 1 := IsUnit.dvd hu
    norm_num at hdiv
  have hnotNat : ¬3 ∣ (apX a b).natAbs := by
    intro hd
    exact hnot (Int.natCast_dvd.mpr hd)
  have hcNat : Nat.Coprime 3 (apX a b).natAbs :=
    (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hnotNat
  have hc : IsCoprime (3 : ℤ) (apX a b) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hcNat
  exact hc.symm

private lemma coprime_apX_quartic {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apX a b).natAbs (quartic a b).natAbs := by
  have h8 : IsCoprime (apX a b) (8 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apX hpar) 3
  have h3 := coprime_apX_three hab
  have h24 : IsCoprime (apX a b) (24 : ℤ) := by
    have hm : IsCoprime (apX a b) ((3 : ℤ) * 8) := h3.mul_right h8
    norm_num at hm ⊢
    exact hm
  apply coprime_of_resultant hab (t := 2 * a - b) (C := 24) (n := 5)
    (U := -2 * a ^ 3 + 15 * a ^ 2 * b + 4 * a * b ^ 2 - 19 * b ^ 3)
    (V := 2 * a + 5 * b)
  · simp only [apX]
    ring
  · exact h24
  · simp only [apX, quartic]
    ring

private lemma coprime_apY_quartic {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apY a b).natAbs (quartic a b).natAbs := by
  have h16 : IsCoprime (apY a b) (16 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apY hpar) 4
  apply coprime_of_resultant hab (t := b) (C := 16) (n := 5)
    (U := a ^ 3 - 8 * a ^ 2 * b + a * b ^ 2 + 16 * b ^ 3) (V := -a)
  · simp only [apY]
    ring
  · exact h16
  · simp only [apY, quartic]
    ring

private lemma coprime_apZ_quartic {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apZ a b).natAbs (quartic a b).natAbs := by
  have h8 : IsCoprime (apZ a b) (8 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apZ hpar) 3
  apply coprime_of_resultant hab (t := -2 * a - b) (C := 8) (n := 5)
    (U := -2 * a ^ 3 + 17 * a ^ 2 * b - 12 * a * b ^ 2 - 13 * b ^ 3)
    (V := 2 * a - 5 * b)
  · simp only [apZ]
    ring
  · exact h8
  · simp only [apZ, quartic]
    ring

/-! ## The natural-number progression -/

private def squareNat (z : ℤ) : ℕ := z.natAbs ^ 2
private def fourthNat (a b : ℤ) : ℕ := (quartic a b).natAbs
private def apStep (a b : ℤ) : ℕ := (4 * apDelta a b).natAbs

/-- Reverse the progression exactly when its displayed integer common difference is
negative. -/
private def apProgression (p : ℤ × ℤ) : ℕ × ℕ :=
  if 0 ≤ apDelta p.1 p.2 then
    (squareNat (apX p.1 p.2), apStep p.1 p.2)
  else
    (fourthNat p.1 p.2, apStep p.1 p.2)

private lemma coe_squareNat (z : ℤ) : ((squareNat z : ℕ) : ℤ) = z ^ 2 := by
  simp [squareNat]

private lemma coe_apStep_of_nonneg {a b : ℤ} (h : 0 ≤ apDelta a b) :
    ((apStep a b : ℕ) : ℤ) = 4 * apDelta a b := by
  simp only [apStep, Int.natCast_natAbs]
  rw [abs_of_nonneg]
  exact mul_nonneg (by norm_num) h

private lemma coe_apStep_of_neg {a b : ℤ} (h : apDelta a b < 0) :
    ((apStep a b : ℕ) : ℤ) = -(4 * apDelta a b) := by
  simp only [apStep, Int.natCast_natAbs]
  rw [abs_of_neg]
  exact mul_neg_of_pos_of_neg (by norm_num) h

private lemma one_ne_73_cube_mul_sq (c : ℤ) :
    (1 : ℤ) ≠ (73 : ℤ) ^ 3 * c ^ 2 := by
  intro h
  have hd : (73 : ℤ) ∣ 1 := ⟨(73 : ℤ) ^ 2 * c ^ 2, by rw [h]; ring⟩
  norm_num at hd

private lemma apDelta_ne_zero {a b c : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) : apDelta a b ≠ 0 := by
  intro hd
  have hprod : a * b = 0 ∨ b ^ 2 - a ^ 2 = 0 := by
    simpa [apDelta] using (mul_eq_zero.mp hd)
  rcases hprod with hab0 | hs
  · rcases mul_eq_zero.mp hab0 with ha | hb
    · subst a
      have hbabs : b.natAbs = 1 := by simpa using hab
      rcases Int.natAbs_eq_iff.mp hbabs with rfl | rfl <;>
        exact one_ne_73_cube_mul_sq c (by simpa [quartic] using hF)
    · subst b
      have haabs : a.natAbs = 1 := by simpa using hab
      rcases Int.natAbs_eq_iff.mp haabs with rfl | rfl <;>
        exact one_ne_73_cube_mul_sq c (by simpa [quartic] using hF)
  · have hfac : (b - a) * (b + a) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hba | hba
    · have : b = a := by linarith
      subst b
      rcases hpar with ⟨k, hk⟩
      omega
    · have : b = -a := by linarith
      subst b
      rcases hpar with ⟨k, hk⟩
      omega

private lemma forward_progression_values {a b c : ℤ}
    (hD : 0 ≤ apDelta a b)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) :
    squareNat (apY a b) = squareNat (apX a b) + apStep a b ∧
    squareNat (apZ a b) = squareNat (apX a b) + 2 * apStep a b ∧
    fourthNat a b = squareNat (apX a b) + 3 * apStep a b := by
  have hFn : 0 ≤ quartic a b := by rw [hF]; positivity
  have hs := coe_apStep_of_nonneg hD
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, coe_squareNat, hs]
    linear_combination apY_sq_sub_apX_sq a b
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, coe_squareNat, hs]
    linear_combination (apY_sq_sub_apX_sq a b) + (apZ_sq_sub_apY_sq a b)
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination (apY_sq_sub_apX_sq a b) +
      (apZ_sq_sub_apY_sq a b) + (quartic_sub_apZ_sq a b)

private lemma reverse_progression_values {a b c : ℤ}
    (hD : apDelta a b < 0)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) :
    squareNat (apZ a b) = fourthNat a b + apStep a b ∧
    squareNat (apY a b) = fourthNat a b + 2 * apStep a b ∧
    squareNat (apX a b) = fourthNat a b + 3 * apStep a b := by
  have hFn : 0 ≤ quartic a b := by rw [hF]; positivity
  have hs := coe_apStep_of_neg hD
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination -(quartic_sub_apZ_sq a b)
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination -(quartic_sub_apZ_sq a b) - (apZ_sq_sub_apY_sq a b)
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination -(quartic_sub_apZ_sq a b) - (apZ_sq_sub_apY_sq a b) -
      (apY_sq_sub_apX_sq a b)

private lemma powerful_sq (n : ℕ) : Nat.Powerful (n ^ 2) := by
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have pn : p ∣ n := pp.dvd_of_dvd_pow pd
  exact pow_dvd_pow_of_dvd pn 2

private lemma powerful_cube (n : ℕ) : Nat.Powerful (n ^ 3) := by
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have pn : p ∣ n := pp.dvd_of_dvd_pow pd
  obtain ⟨d, rfl⟩ := pn
  refine ⟨d ^ 3 * p, ?_⟩
  ring

private lemma powerful_mul {m n : ℕ} (hm : Nat.Powerful m) (hn : Nat.Powerful n) :
    Nat.Powerful (m * n) := by
  intro p hp
  rcases Nat.mem_primeFactors.mp hp with ⟨pp, pd, hmn⟩
  have hm0 : m ≠ 0 := by intro h; subst m; simp at hmn
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hmn
  rcases pp.dvd_mul.mp pd with hpm | hpn
  · exact dvd_mul_of_dvd_left (hm p (pp.mem_primeFactors hpm hm0)) n
  · exact dvd_mul_of_dvd_right (hn p (pp.mem_primeFactors hpn hn0)) m

private lemma goodParam_mem {a b c : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) :
    IsCoprimePowerfulAP4 (apProgression (a, b)).1 (apProgression (a, b)).2 := by
  have hdelta := apDelta_ne_zero hab hpar hF
  have hdpos : 0 < apStep a b := by
    exact Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hdelta)
  have pX : Nat.Powerful (squareNat (apX a b)) := powerful_sq _
  have pY : Nat.Powerful (squareNat (apY a b)) := powerful_sq _
  have pZ : Nat.Powerful (squareNat (apZ a b)) := powerful_sq _
  have hfourth : fourthNat a b = 73 ^ 3 * c.natAbs ^ 2 := by
    simp [fourthNat, hF, Int.natAbs_mul, Int.natAbs_pow]
  have pF : Nat.Powerful (fourthNat a b) := by
    rw [hfourth]
    exact powerful_mul (powerful_cube 73) (powerful_sq c.natAbs)
  have hXY : Nat.Coprime (squareNat (apX a b)) (squareNat (apY a b)) := by
    simpa [squareNat] using (coprime_apX_apY hab hpar).pow 2 2
  have hXZ : Nat.Coprime (squareNat (apX a b)) (squareNat (apZ a b)) := by
    simpa [squareNat] using (coprime_apX_apZ hab hpar).pow 2 2
  have hYZ : Nat.Coprime (squareNat (apY a b)) (squareNat (apZ a b)) := by
    simpa [squareNat] using (coprime_apY_apZ hab hpar).pow 2 2
  have hXF : Nat.Coprime (squareNat (apX a b)) (fourthNat a b) := by
    simpa [squareNat, fourthNat] using (coprime_apX_quartic hab hpar).pow_left 2
  have hYF : Nat.Coprime (squareNat (apY a b)) (fourthNat a b) := by
    simpa [squareNat, fourthNat] using (coprime_apY_quartic hab hpar).pow_left 2
  have hZF : Nat.Coprime (squareNat (apZ a b)) (fourthNat a b) := by
    simpa [squareNat, fourthNat] using (coprime_apZ_quartic hab hpar).pow_left 2
  by_cases hD : 0 ≤ apDelta a b
  · have hv := forward_progression_values hD hF
    rw [show apProgression (a, b) =
      (squareNat (apX a b), apStep a b) by simp [apProgression, hD]]
    simp only [Prod.fst, Prod.snd]
    unfold IsCoprimePowerfulAP4
    rw [← hv.1, ← hv.2.1, ← hv.2.2]
    exact ⟨hdpos, pX, pY, pZ, pF, hXY, hXZ, hXF, hYZ, hYF, hZF⟩
  · have hD' : apDelta a b < 0 := lt_of_not_ge hD
    have hv := reverse_progression_values hD' hF
    rw [show apProgression (a, b) =
      (fourthNat a b, apStep a b) by simp [apProgression, hD]]
    simp only [Prod.fst, Prod.snd]
    unfold IsCoprimePowerfulAP4
    rw [← hv.1, ← hv.2.1, ← hv.2.2]
    exact ⟨hdpos, pF, pZ, pY, pX, hZF.symm, hYF.symm, hXF.symm,
      hYZ.symm, hXZ.symm, hXY.symm⟩

/-! ## Infinitely many parameters -/

private structure GoodParam (k : ℕ) where
  a : ℤ
  b : ℤ
  c : ℤ
  coprime : Nat.Coprime a.natAbs b.natAbs
  parity : OppositeParity a b
  signature : quartic a b = (73 : ℤ) ^ 3 * c ^ 2
  source :
    quarticX (orbit (57 + 72 * k)) = (a : ℚ) / (b : ℚ) ∨
    quarticX (orbit (57 + 72 * k)) =
      ((a + b : ℤ) : ℚ) / ((a - b : ℤ) : ℚ)

private noncomputable def goodParam (k : ℕ) : GoodParam k := by
  classical
  choose a b c hab hpar hF hsource using orbit_sample_normalized_solution k
  exact ⟨a, b, c, hab, hpar, hF, hsource⟩

private noncomputable def paramPair (k : ℕ) : ℤ × ℤ :=
  ((goodParam k).a, (goodParam k).b)

private lemma sampleQ_injective :
    Function.Injective (fun k : ℕ ↦ quarticX (orbit (57 + 72 * k))) := by
  intro k l h
  have hi := quarticX_orbit_injective h
  omega

private lemma paramPair_range_infinite : (Set.range paramPair).Infinite := by
  classical
  have hqinf :
      (Set.range (fun k : ℕ ↦ quarticX (orbit (57 + 72 * k)))).Infinite :=
    Set.infinite_range_of_injective sampleQ_injective
  intro hfinite
  apply hqinf
  let f₁ : ℤ × ℤ → ℚ := fun p ↦ (p.1 : ℚ) / (p.2 : ℚ)
  let f₂ : ℤ × ℤ → ℚ := fun p ↦
    ((p.1 + p.2 : ℤ) : ℚ) / ((p.1 - p.2 : ℤ) : ℚ)
  refine ((hfinite.image f₁).union (hfinite.image f₂)).subset ?_
  rintro q ⟨k, rfl⟩
  rcases (goodParam k).source with h | h
  · apply Set.mem_union_left
    refine ⟨paramPair k, ⟨k, rfl⟩, ?_⟩
    simpa [f₁, paramPair] using h.symm
  · apply Set.mem_union_right
    refine ⟨paramPair k, ⟨k, rfl⟩, ?_⟩
    simpa [f₂, paramPair] using h.symm

private lemma apY_natAbs (a b : ℤ) :
    (apY a b).natAbs = a.natAbs ^ 2 + b.natAbs ^ 2 := by
  apply Int.ofNat_inj.mp
  push_cast
  have hY : 0 ≤ apY a b := by
    simp only [apY]
    positivity
  rw [abs_of_nonneg hY]
  simp only [apY]
  rw [sq_abs, sq_abs]

private lemma progression_fiber_finite (x : ℕ × ℕ) :
    (Set.range paramPair ∩ apProgression ⁻¹' {x}).Finite := by
  classical
  let M : ℕ := x.1 + 3 * x.2
  let box : Set (ℤ × ℤ) :=
    Set.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Set.Icc (-(M : ℤ)) (M : ℤ)
  have hbox : box.Finite := by
    dsimp [box]
    exact (Set.finite_Icc (-(M : ℤ)) (M : ℤ)).prod
      (Set.finite_Icc (-(M : ℤ)) (M : ℤ))
  apply hbox.subset
  rintro p ⟨⟨k, rfl⟩, hp⟩
  let a := (goodParam k).a
  let b := (goodParam k).b
  have hpair : paramPair k = (a, b) := by rfl
  have hprog : apProgression (a, b) = x := by
    simpa [hpair] using (show apProgression (paramPair k) ∈ ({x} : Set (ℕ × ℕ)) from hp)
  have hF : quartic a b = (73 : ℤ) ^ 3 * (goodParam k).c ^ 2 := by
    simpa [a, b] using (goodParam k).signature
  have hyBound : squareNat (apY a b) ≤ M := by
    by_cases hD : 0 ≤ apDelta a b
    · have hv := forward_progression_values hD hF
      have hx1 : x.1 = squareNat (apX a b) := by
        rw [← hprog]
        simp [apProgression, hD]
      have hx2 : x.2 = apStep a b := by
        rw [← hprog]
        simp [apProgression, hD]
      dsimp [M]
      omega
    · have hD' : apDelta a b < 0 := lt_of_not_ge hD
      have hv := reverse_progression_values hD' hF
      have hx1 : x.1 = fourthNat a b := by
        rw [← hprog]
        simp [apProgression, hD]
      have hx2 : x.2 = apStep a b := by
        rw [← hprog]
        simp [apProgression, hD]
      dsimp [M]
      omega
  have haYabs : a.natAbs ≤ (apY a b).natAbs := by
    rw [apY_natAbs]
    exact le_trans (Nat.le_mul_self a.natAbs) (by
      simpa [pow_two] using Nat.le_add_right (a.natAbs ^ 2) (b.natAbs ^ 2))
  have hbYabs : b.natAbs ≤ (apY a b).natAbs := by
    rw [apY_natAbs]
    exact le_trans (Nat.le_mul_self b.natAbs) (by
      simpa [pow_two] using Nat.le_add_left (b.natAbs ^ 2) (a.natAbs ^ 2))
  have hYsq : (apY a b).natAbs ≤ squareNat (apY a b) := by
    simpa [squareNat, pow_two] using Nat.le_mul_self (apY a b).natAbs
  have haM : a.natAbs ≤ M := haYabs.trans (hYsq.trans hyBound)
  have hbM : b.natAbs ≤ M := hbYabs.trans (hYsq.trans hyBound)
  have haCast : (a.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast haM
  have hbCast : (b.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hbM
  have haAbs : |a| ≤ (M : ℤ) := by simpa only [Int.natCast_natAbs] using haCast
  have hbAbs : |b| ≤ (M : ℤ) := by simpa only [Int.natCast_natAbs] using hbCast
  rw [hpair]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (neg_le_neg haAbs).trans (neg_abs_le a)
  · exact (le_abs_self a).trans haAbs
  · exact (neg_le_neg hbAbs).trans (neg_abs_le b)
  · exact (le_abs_self b).trans hbAbs

private lemma coprime_powerful_progressions_infinite :
    {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite := by
  classical
  intro htarget
  apply paramPair_range_infinite
  apply Set.Finite.of_finite_fibers apProgression
  · apply htarget.subset
    rintro y ⟨p, ⟨k, rfl⟩, rfl⟩
    change IsCoprimePowerfulAP4 (apProgression (paramPair k)).1
      (apProgression (paramPair k)).2
    simpa [paramPair] using goodParam_mem (goodParam k).coprime
      (goodParam k).parity (goodParam k).signature
  · intro x _
    exact progression_fiber_finite x

/-- Erdős Problem 937: there are infinitely many nonconstant four-term arithmetic
progressions of pairwise coprime powerful natural numbers. -/
theorem erdos_937 :
    answer(True) ↔ {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite := by
  constructor
  · intro _
    exact coprime_powerful_progressions_infinite
  · intro _
    trivial

#print axioms Erdos937.erdos_937

end Erdos937
