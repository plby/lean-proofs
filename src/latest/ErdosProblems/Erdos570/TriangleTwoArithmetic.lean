import ErdosProblems.Erdos570.TriangleArithmetic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Cast

/-!
# Degree-two arithmetic for the triangle extension
-/

namespace Erdos570

theorem triangle_degree_two_c1_real
    {p t f y : ℝ} (hf : 1 ≤ f) (hp : 11 ≤ p)
    (hpf : p = t + f) (ht0 : 0 ≤ t) (hy0 : 0 ≤ y)
    (hlower : 12 * p ≤ 5 * (y + t))
    (hupper : y ≤ p + t) :
    y * (t - 1) * f ≤ (y - t) * (t * (y - t) - y) := by
  have hpt : p + t ≤ 2 * y := by nlinarith
  have ha : 0 ≤ 5 * y + 5 * t - 12 * p := by nlinarith
  have hb : 0 ≤ 7 * p - 10 * t + 5 * y := by nlinarith
  have hquad : 84 * p ^ 2 - 155 * p * t + 75 * t ^ 2 ≤
      25 * (y ^ 2 - y * (p + t) + t ^ 2) := by
    nlinarith [mul_nonneg ha hb]
  have hcompare : 4 * p ^ 2 + 75 * f ^ 2 ≤
      84 * p ^ 2 - 155 * p * t + 75 * t ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ p by nlinarith)
      (show 0 ≤ f by nlinarith)]
  have hc : 0 ≤ p - 11 := by nlinarith
  have hd : 0 ≤ 4 * p - 6 := by nlinarith
  have hpquad : 25 * (p + t) ≤ 4 * p ^ 2 + 75 * f ^ 2 := by
    nlinarith [mul_nonneg hc hd, sq_nonneg (f - 1)]
  have hL : t * (p + t) ≤
      t * (y ^ 2 - y * (p + t) + t ^ 2) := by
    have := mul_le_mul_of_nonneg_left
      (hpquad.trans (hcompare.trans hquad)) ht0
    nlinarith
  have hR : y * (y - p) ≤ t * (p + t) := by
    have hypt : y * t ≤ (p + t) * t :=
      mul_le_mul_of_nonneg_right hupper ht0
    nlinarith [mul_nonneg hy0 (show 0 ≤ t - (y - p) by nlinarith)]
  nlinarith

theorem triangle_degree_two_c2_below
    {p t f s y : ℝ} (hf : 2 ≤ f) (hpf : p = t + f)
    (hty : t ≤ y) (hsp : s ≤ p) (hdegree : 3 * p ≤ y + t + s)
    (hindependent : 4 * s ≤ y + t) (hy : y ≤ 2 * t) :
    y * (t - 1) * f ≤ s * (t * (y - t) - y) := by
  have ht0 : 0 ≤ t := by nlinarith
  have hs3f : 3 * f ≤ s := by nlinarith
  have hA : f * t + f * y ≤ s * (y - t) := by
    have hprod : 0 ≤ (s - 3 * f) * (p - s) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    nlinarith
  have hthree : 4 * s ≤ 3 * t := by nlinarith
  have hs : 2 * (s - f) ≤ f * t := by
    have hprod : 0 ≤ (f - 2) * t := mul_nonneg (by nlinarith) ht0
    nlinarith
  have hB : (s - f) * y ≤ f * t ^ 2 := by
    have hprod := mul_le_mul_of_nonneg_left hy (show 0 ≤ s - f by nlinarith)
    have hprod' := mul_le_mul_of_nonneg_right hs ht0
    nlinarith
  have htA := mul_le_mul_of_nonneg_left hA ht0
  nlinarith

theorem triangle_degree_two_c2_regular
    {t f s y : ℝ} (hf : 2 ≤ f) (ht : 2 * f + 1 ≤ t)
    (ht6 : 6 ≤ t) (hfs : f ≤ s) (hy : 2 * t ≤ y)
    (halpha : 5 * f < 2 * s) :
    y * (t - 1) * f ≤ s * (t * (y - t) - y) := by
  have ht0 : 0 ≤ t := by nlinarith
  have hcriterion : 2 * f * (t - 1) ≤ s * (t - 2) := by
    have hprod : 0 ≤ (2 * s - 5 * f) * (t - 2) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    have hprod' : 0 ≤ f * (t - 6) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    nlinarith
  have hcoef : 0 ≤ (y - 2 * t) * ((s - f) * (t - 1)) :=
    mul_nonneg (by nlinarith) (mul_nonneg (by nlinarith) (by nlinarith))
  have hbase := mul_le_mul_of_nonneg_left hcriterion ht0
  nlinarith

theorem triangle_degree_two_c2_parameterized (b c e r : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) (hr : 0 ≤ r) :
    let a := r + 1 + b
    let f := 2 * a + e
    let t := 2 * f + 1 + c
    let s := 2 * f + a
    let σ := f - r
    let y := 2 * t + σ
    y * (t - 1) * (σ * s + r * t) ≤
      s * (y - t) * (t * (y - t) - y) := by
  dsimp only
  have hfr : r ≤ 2 * (r + 1 + b) + e := by nlinarith
  have hprod : 0 ≤
      (4*b + c + 2*e + 4*r + 5) *
      (80*b^3 + 40*b^2*c + 112*b^2*e + 200*b^2*r + 230*b^2 +
        5*b*c^2 + 36*b*c*e + 62*b*c*r + 80*b*c + 52*b*e^2 +
        184*b*e*r + 215*b*e + 164*b*r^2 + 377*b*r + 215*b +
        2*c^2*e + 3*c^2*r + 5*c^2 + 8*c*e^2 + 27*c*e*r +
        36*c*e + 23*c*r^2 + 60*c*r + 40*c + 8*e^3 +
        42*e^2*r + 50*e^2 + 74*e*r^2 + 173*e*r + 101*e +
        44*r^3 + 151*r^2 + 172*r + 65) := by positivity
  nlinarith

theorem triangle_degree_two_extension_arithmetic
    {m p s t f y : ℕ} (hf : 1 ≤ f) (hp11 : 11 ≤ p)
    (hpf : p = t + f) (hhostLower : 2 * m + 1 ≤ t + y)
    (hhostUpper : t + y + 1 ≤ p + 2 * t)
    (hdegrees : 3 * p ≤ 2 * m + s)
    (hindependent : 2 * s ≤ m) (hsp : s ≤ p) :
    2 * f < t ∧ t ≤ y ∧ t * (y - t) ≥ y ∧
      y * (t - 1) * f ≤
        (y - t) * (t * (y - t) - y) ∧
      let σ := y - 2 * t
      σ < f → 2 ≤ f →
        y * (t - 1) * (σ * s + (f - σ) * (y - t - σ)) ≤
          s * (y - t) * (t * (y - t) - y) := by
  have hft : 2 * f < t := by
    by_contra hnot
    have ht : t ≤ 2 * f := by omega
    nlinarith
  have hkey : 12 * p ≤ 10 * m := by nlinarith
  have hty : t ≤ y := by omega
  have hygap : t + 3 ≤ y := by omega
  have ht3 : 3 ≤ t := by omega
  have hmean : y ≤ t * (y - t) := by
    let g := y - t
    have hyEq : y = t + g := by dsimp only [g]; omega
    have hg3 : 3 ≤ g := by dsimp only [g]; omega
    have hprod : 1 ≤ (t - 1) * (g - 1) :=
      Nat.mul_pos (by omega) (by omega)
    change y ≤ t * g
    nlinarith
  refine ⟨hft, hty, hmean, ?_, ?_⟩
  · have hlowerR : (12 : ℝ) * p ≤ 5 * (y + t) := by
      exact_mod_cast (show 12 * p ≤ 5 * (y + t) by omega)
    have hupper : y ≤ p + t := by omega
    have hR := triangle_degree_two_c1_real
      (p := (p : ℝ)) (t := (t : ℝ)) (f := (f : ℝ)) (y := (y : ℝ))
      (by exact_mod_cast hf) (by exact_mod_cast hp11)
      (by exact_mod_cast hpf) (by positivity) (by positivity)
      hlowerR (by exact_mod_cast hupper)
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ t),
      ← Nat.cast_sub hty] at hR
    have hinner : (((t * (y - t) - y : ℕ) : ℝ)) =
        (t : ℝ) * ((y - t : ℕ) : ℝ) - (y : ℝ) := by
      rw [Nat.cast_sub hmean]
      push_cast
      ring
    rw [← hinner] at hR
    exact_mod_cast hR
  · dsimp only
    intro hσf hf2
    by_cases hy2t : y ≤ 2 * t
    · have hdegree' : 3 * p ≤ y + t + s := by omega
      have hindependent' : 4 * s ≤ y + t := by omega
      have hR := triangle_degree_two_c2_below
        (p := (p : ℝ)) (t := (t : ℝ)) (f := (f : ℝ))
        (s := (s : ℝ)) (y := (y : ℝ))
        (by exact_mod_cast hf2) (by exact_mod_cast hpf)
        (by exact_mod_cast hty) (by exact_mod_cast hsp)
        (by exact_mod_cast hdegree') (by exact_mod_cast hindependent')
        (by exact_mod_cast hy2t)
      have hσ : y - 2 * t = 0 := Nat.sub_eq_zero_of_le hy2t
      rw [hσ]
      simp only [zero_mul, zero_add, Nat.sub_zero]
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ t),
        ← Nat.cast_sub hty] at hR
      have hinner : (((t * (y - t) - y : ℕ) : ℝ)) =
          (t : ℝ) * ((y - t : ℕ) : ℝ) - (y : ℝ) := by
        rw [Nat.cast_sub hmean]
        push_cast
        ring
      rw [← hinner] at hR
      have hRnat : y * (t - 1) * f ≤
          s * (t * (y - t) - y) := by exact_mod_cast hR
      calc
        y * (t - 1) * (f * (y - t)) =
            (y * (t - 1) * f) * (y - t) := by ring
        _ ≤ (s * (t * (y - t) - y)) * (y - t) :=
          Nat.mul_le_mul_right _ hRnat
        _ = s * (y - t) * (t * (y - t) - y) := by ring
    · have h2ty : 2 * t ≤ y := Nat.le_of_not_ge hy2t
      let σ := y - 2 * t
      have hyEq : y = 2 * t + σ := by
        dsimp only [σ]
        omega
      have hyts : y - t - σ = t := by omega
      rw [hyts]
      change y * (t - 1) * (σ * s + (f - σ) * t) ≤
        s * (y - t) * (t * (y - t) - y)
      by_cases halpha : 5 * f < 2 * s
      · have ht6 : 6 ≤ t := by omega
        have hR := triangle_degree_two_c2_regular
          (t := (t : ℝ)) (f := (f : ℝ)) (s := (s : ℝ)) (y := (y : ℝ))
          (by exact_mod_cast hf2) (by exact_mod_cast (show 2 * f + 1 ≤ t by omega))
          (by exact_mod_cast ht6) (by exact_mod_cast (show f ≤ s by omega))
          (by exact_mod_cast h2ty) (by exact_mod_cast halpha)
        have htarget : σ * s + (f - σ) * t ≤ f * (y - t) := by
          have hfEq : f = σ + (f - σ) := by omega
          have hpEq : p = s + (p - s) := by omega
          have hyg : y - t = t + σ := by omega
          have hid : f * (y - t) =
              (σ * s + (f - σ) * t) + σ * (p - s) := by
            have hftmul : f * t = σ * t + (f - σ) * t := by
              calc
                f * t = (σ + (f - σ)) * t :=
                  congrArg (fun z : ℕ => z * t) hfEq
                _ = σ * t + (f - σ) * t := by ring
            have hspmul : σ * p = σ * s + σ * (p - s) := by
              calc
                σ * p = σ * (s + (p - s)) :=
                  congrArg (fun z : ℕ => σ * z) hpEq
                _ = σ * s + σ * (p - s) := by ring
            have hptmul : σ * p = σ * t + σ * f := by
              calc
                σ * p = σ * (t + f) :=
                  congrArg (fun z : ℕ => σ * z) hpf
                _ = σ * t + σ * f := by ring
            have hcomm : f * σ = σ * f := by ring
            calc
              f * (y - t) = f * (t + σ) :=
                congrArg (fun z : ℕ => f * z) hyg
              _ = f * t + f * σ := by ring
              _ = (σ * s + (f - σ) * t) + σ * (p - s) := by
                omega
          rw [hid]
          exact Nat.le_add_right _ _
        have hregular := Nat.mul_le_mul_left (y * (t - 1)) htarget
        have hRnat : y * (t - 1) * f ≤
            s * (t * (y - t) - y) := by
          rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ t),
            ← Nat.cast_sub hty] at hR
          have hinner : (((t * (y - t) - y : ℕ) : ℝ)) =
              (t : ℝ) * ((y - t : ℕ) : ℝ) - (y : ℝ) := by
            rw [Nat.cast_sub hmean]
            push_cast
            ring
          rw [← hinner] at hR
          exact_mod_cast hR
        exact hregular.trans (by
          calc
            y * (t - 1) * (f * (y - t)) =
                (y * (t - 1) * f) * (y - t) := by ring
            _ ≤ (s * (t * (y - t) - y)) * (y - t) :=
              Nat.mul_le_mul_right _ hRnat
            _ = s * (y - t) * (t * (y - t) - y) := by ring)
      · have halphaLe : 2 * s ≤ 5 * f := by omega
        let a := s - 2 * f
        let r := f - σ
        have hσLower : 3 * f + 1 ≤ s + σ := by omega
        have hra : r + 1 ≤ a := by
          dsimp only [r, a, σ]
          omega
        have h2af : 2 * a ≤ f := by
          dsimp only [a]
          omega
        let b := a - (r + 1)
        let c := t - (2 * f + 1)
        let e := f - 2 * a
        have haEq : a = r + 1 + b := by dsimp only [b]; omega
        have hfEq : f = 2 * a + e := by dsimp only [e]; omega
        have htEq : t = 2 * f + 1 + c := by dsimp only [c]; omega
        have hsEq : s = 2 * f + a := by dsimp only [a]; omega
        have hσEq : σ = f - r := by dsimp only [r]; omega
        have hparam := triangle_degree_two_c2_parameterized
          (b : ℝ) (c : ℝ) (e : ℝ) (r : ℝ)
          (by positivity) (by positivity) (by positivity) (by positivity)
        dsimp only at hparam
        have haEqR : (a : ℝ) = (r : ℝ) + 1 + (b : ℝ) := by exact_mod_cast haEq
        have hfEqR : (f : ℝ) = 2 * (a : ℝ) + (e : ℝ) := by exact_mod_cast hfEq
        have htEqR : (t : ℝ) = 2 * (f : ℝ) + 1 + (c : ℝ) := by exact_mod_cast htEq
        have hsEqR : (s : ℝ) = 2 * (f : ℝ) + (a : ℝ) := by exact_mod_cast hsEq
        have hrle : r ≤ f := by omega
        have hσEqR : (σ : ℝ) = (f : ℝ) - (r : ℝ) := by
          rw [hσEq, Nat.cast_sub hrle]
        have hfσ : σ ≤ f := by omega
        have hrEqR : (r : ℝ) = (f : ℝ) - (σ : ℝ) := by
          dsimp only [r]
          rw [Nat.cast_sub hfσ]
        have hyEqR : (y : ℝ) = 2 * (t : ℝ) + (σ : ℝ) := by exact_mod_cast hyEq
        rw [← haEqR, ← hfEqR, ← htEqR, ← hsEqR, ← hσEqR,
          ← hyEqR, hrEqR] at hparam
        rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ t),
          ← Nat.cast_sub hty, ← Nat.cast_sub hfσ] at hparam
        have hinner : (((t * (y - t) - y : ℕ) : ℝ)) =
            (t : ℝ) * ((y - t : ℕ) : ℝ) - (y : ℝ) := by
          rw [Nat.cast_sub hmean]
          push_cast
          ring
        rw [← hinner] at hparam
        exact_mod_cast hparam

/-- Cauchy--Schwarz in the exact form needed for the degree-two candidate
sets.  The left side is the second factorial moment of their total degree. -/
theorem degree_two_candidate_cauchy
    {Y : Type*} [Fintype Y] (deg : Y → ℕ) {t y : ℕ}
    (hcard : Fintype.card Y = y)
    (hsum : ∑ z : Y, deg z = t * (y - t))
    (hmean : y ≤ t * (y - t)) :
    (t * (y - t)) * (t * (y - t) - y) ≤
      2 * y * ∑ z : Y, (deg z).choose 2 := by
  classical
  let D := t * (y - t)
  have hsumR : ∑ z : Y, (deg z : ℝ) = (D : ℝ) := by
    rw [← Nat.cast_sum, hsum]
  have hsqR : ∑ z : Y, (deg z : ℝ) ^ 2 =
      (D : ℝ) + 2 * ∑ z : Y, ((deg z).choose 2 : ℝ) := by
    calc
      ∑ z : Y, (deg z : ℝ) ^ 2 =
          ∑ z : Y, ((deg z : ℝ) + 2 * ((deg z).choose 2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro z _hz
        rw [Nat.cast_choose_two (K := ℝ)]
        ring
      _ = (∑ z : Y, (deg z : ℝ)) +
          2 * ∑ z : Y, ((deg z).choose 2 : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hsumR]
  have hCS : (∑ z : Y, (deg z : ℝ)) ^ 2 ≤
      (Fintype.card Y : ℝ) * ∑ z : Y, (deg z : ℝ) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset Y)) (f := fun z ↦ (deg z : ℝ)))
  rw [hsumR, hsqR, hcard] at hCS
  have hmeanR : (y : ℝ) ≤ (D : ℝ) := by exact_mod_cast hmean
  have hR : (D : ℝ) * ((D : ℝ) - y) ≤
      2 * y * ∑ z : Y, ((deg z).choose 2 : ℝ) := by
    nlinarith
  have hcastSub : (((D - y : ℕ) : ℝ)) = (D : ℝ) - y := by
    rw [Nat.cast_sub hmean]
  rw [← hcastSub] at hR
  exact_mod_cast hR

/-- Multiplying a factorial-moment endpoint estimate by `t` and applying
Cauchy--Schwarz converts it to the binomial candidate bound used by Hall's
argument. -/
theorem degree_two_candidate_endpoint
    {Y : Type*} [Fintype Y] (deg : Y → ℕ) {t y q r : ℕ}
    (hcard : Fintype.card Y = y)
    (hsum : ∑ z : Y, deg z = t * (y - t))
    (hmean : y ≤ t * (y - t)) (ht : 1 ≤ t) (hy : 1 ≤ y)
    (hendpoint : y * (t - 1) * q ≤
      r * (y - t) * (t * (y - t) - y)) :
    t.choose 2 * q ≤ r * ∑ z : Y, (deg z).choose 2 := by
  have hC := degree_two_candidate_cauchy deg hcard hsum hmean
  have hRend : (y : ℝ) * ((t : ℝ) - 1) * q ≤
      r * (y - t : ℕ) * (t * (y - t) - y : ℕ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub ht]
    exact_mod_cast hendpoint
  have hCR : ((t * (y - t) : ℕ) : ℝ) *
      ((t * (y - t) - y : ℕ) : ℝ) ≤
        2 * y * ∑ z : Y, ((deg z).choose 2 : ℝ) := by
    exact_mod_cast hC
  push_cast at hCR
  have hchoose : ((t.choose 2 : ℕ) : ℝ) =
      (t : ℝ) * ((t : ℝ) - 1) / 2 :=
    Nat.cast_choose_two (K := ℝ) t
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have htargetR : ((t.choose 2 : ℕ) : ℝ) * q ≤
      r * ∑ z : Y, ((deg z).choose 2 : ℝ) := by
    rw [hchoose]
    have hnonneg : (0 : ℝ) ≤ t := by positivity
    have hmult := mul_le_mul_of_nonneg_left hRend hnonneg
    have hmultC := mul_le_mul_of_nonneg_left hCR (show (0 : ℝ) ≤ r by positivity)
    nlinarith
  exact_mod_cast htargetR

end Erdos570
