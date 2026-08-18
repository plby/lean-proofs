/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleJensen

/-!
# Arithmetic for the dense triangle branch

These are the integer consequences of the degree sum, the independent
minimum-degree set, and the one-vertex deletion obstruction in the
Goddard--Kleitman argument.
-/

open scoped BigOperators

noncomputable section

namespace Erdos570

/-- All numerical estimates needed by the candidate-set argument.  The
equalities name `f=p-t` and `y=2m+1-t` without natural-subtraction noise. -/
theorem triangle_dense_numeric
    {δ m p s t f y : ℕ} (hδ : 3 ≤ δ) (hf : 1 ≤ f)
    (hpf : p = t + f) (hny : 2 * m + 1 ≤ t + y)
    (hdelete : 2 * m + 2 ≤ p + δ * t)
    (hdegrees : (δ + 1) * p ≤ 2 * m + s)
    (hindependent : δ * s ≤ m) :
    (2 * δ - 2) * f < t ∧ δ * f ≤ s ∧ δ * f ≤ y - t ∧
      2 * (δ - 1) + 1 ≤ t ∧ (δ - 1) * t ≤ y ∧
      (2 * δ + 1) * (2 * m) ≥ 2 * δ * (δ + 1) * p := by
  have hdf : δ * f ≤ s := by
    nlinarith
  have hkey : 2 * δ * (δ + 1) * p ≤ (2 * δ + 1) * (2 * m) := by
    nlinarith [Nat.zero_le m, Nat.zero_le s]
  have hscaledIndependent : 2 * δ * (δ * f) ≤ 2 * m := by
    calc
      2 * δ * (δ * f) ≤ 2 * δ * s := by gcongr
      _ = 2 * (δ * s) := by ring
      _ ≤ 2 * m := by gcongr
  have hδdecomp : δ = (δ - 1) + 1 := by omega
  have hcoef : 2 * δ - 2 = 2 * (δ - 1) := by omega
  have htstrong : (2 * δ - 2) * f < t := by
    by_contra hnot
    have htupper : t ≤ (2 * δ - 2) * f := by omega
    have hsumUpper : p + δ * t ≤
        (δ + 1) * ((2 * δ - 2) * f) + f := by
      rw [hpf]
      calc
        t + f + δ * t = (δ + 1) * t + f := by ring
        _ ≤ (δ + 1) * ((2 * δ - 2) * f) + f := by gcongr
    have hidentity :
        (δ + 1) * ((2 * δ - 2) * f) + f + f =
          2 * δ * (δ * f) := by
      nlinarith [hδdecomp]
    have hstrict : (δ + 1) * ((2 * δ - 2) * f) + f <
        2 * δ * (δ * f) := by omega
    omega
  have hcoefle : (2 * δ - 2) * 1 ≤ (2 * δ - 2) * f := by
    gcongr
  have ht : 2 * (δ - 1) + 1 ≤ t := by
    omega
  have hy : (δ - 1) * t ≤ y := by
    by_contra hnot
    have hfactor : δ * t = t + (δ - 1) * t := by
      calc
        δ * t = ((δ - 1) + 1) * t := by rw [← hδdecomp]
        _ = t + (δ - 1) * t := by ring
    have hmLt : 2 * m < δ * t := by omega
    have hupper : (2 * δ + 1) * (2 * m) <
        (2 * δ + 1) * (δ * t) := by gcongr
    have hpLower : t + 1 ≤ p := by omega
    have hlower : 2 * δ * (δ + 1) * (t + 1) ≤
        2 * δ * (δ + 1) * p := by gcongr
    have hbetween : (2 * δ + 1) * (δ * t) <
        2 * δ * (δ + 1) * (t + 1) := by
      have hid : 2 * δ * (δ + 1) * (t + 1) =
          (2 * δ + 1) * (δ * t) + δ * t + 2 * δ * (δ + 1) := by
        ring
      rw [hid]
      omega
    omega
  have hty : t ≤ y := by
    exact (show t ≤ (δ - 1) * t by
      calc
        t = 1 * t := by ring
        _ ≤ (δ - 1) * t := by gcongr <;> omega).trans hy
  have hgap : δ * f ≤ y - t := by
    rw [Nat.le_sub_iff_add_le hty]
    have hcoeff : δ ≤ (δ - 2) * (2 * δ - 2) := by
      calc
        δ ≤ 2 * δ - 2 := by omega
        _ = 1 * (2 * δ - 2) := by ring
        _ ≤ (δ - 2) * (2 * δ - 2) := by gcongr <;> omega
    have hmult : (δ - 2) * ((2 * δ - 2) * f) ≤
        (δ - 2) * t := by gcongr
    have hsmall : δ * f ≤ (δ - 2) * ((2 * δ - 2) * f) := by
      calc
        δ * f ≤ ((δ - 2) * (2 * δ - 2)) * f := by gcongr
        _ = (δ - 2) * ((2 * δ - 2) * f) := by ring
    calc
      δ * f + t = t + δ * f := by omega
      _ ≤ t + (δ - 2) * t := by
        exact Nat.add_le_add_left (hsmall.trans hmult) t
      _ = (δ - 1) * t := by
        have hdec : δ - 1 = (δ - 2) + 1 := by omega
        rw [hdec]
        ring
      _ ≤ y := hy
  exact ⟨htstrong, hdf, hgap, ht, hy, hkey⟩

/-- The mean cross-degree is far enough into the convex range of the
binomial coefficient. -/
theorem triangle_average_floor
    {δ t y : ℕ} (hδ : 3 ≤ δ)
    (ht : 2 * (δ - 1) ≤ t) (hy : (δ - 1) * t ≤ y) :
    δ - 1 ≤ t * (y - t) / y := by
  have hty : t ≤ y := by
    calc
      t = 1 * t := by ring
      _ ≤ (δ - 1) * t := by gcongr <;> omega
      _ ≤ y := hy
  have hypos : 0 < y := by
    have htpos : 0 < t := by omega
    exact htpos.trans_le hty
  rw [Nat.le_div_iff_mul_le hypos]
  let d := δ - 1
  let a := t - d
  let b := y - t
  have hd2 : 2 ≤ d := by omega
  have hdt : d + a = t := by
    dsimp only [a]
    omega
  have htyb : t + b = y := by
    dsimp only [b]
    omega
  have hda : d ≤ a := by
    dsimp only [a, d] at ⊢
    omega
  have hb : (d - 1) * t ≤ b := by
    have hddec : d = (d - 1) + 1 := by omega
    have hid : d * t = t + (d - 1) * t := by
      calc
        d * t = ((d - 1) + 1) * t := by rw [← hddec]
        _ = t + (d - 1) * t := by ring
    have hdy : d * t ≤ y := by simpa [d] using hy
    omega
  have hfactor : d ≤ a * (d - 1) := by
    calc
      d = d * 1 := by ring
      _ ≤ d * (d - 1) := by gcongr <;> omega
      _ ≤ a * (d - 1) := by gcongr
  have hleft : d * t ≤ a * ((d - 1) * t) := by
    calc
      d * t ≤ (a * (d - 1)) * t := by gcongr
      _ = a * ((d - 1) * t) := by ring
  have hcross : d * t ≤ a * b := hleft.trans (by gcongr)
  change d * y ≤ t * b
  calc
    d * y = d * t + d * b := by rw [← htyb]; ring
    _ ≤ d * b + a * b := by omega
    _ = t * b := by rw [← hdt]; ring

/-- Usable version of the preceding product estimate, retaining the global
key inequality from which the degree-four and degree-five constants follow. -/
theorem triangle_product_lower_of_key
    {δ m p t f y : ℕ} (hδ : 3 ≤ δ) (hf : 1 ≤ f)
    (hpf : p = t + f) (hny : 2 * m + 1 ≤ t + y)
    (ht7 : 7 ≤ t) (ht : 2 * (δ - 1) + 1 ≤ t)
    (hy : (δ - 1) * t ≤ y)
    (hkey : 2 * δ * (δ + 1) * p ≤ (2 * δ + 1) * (2 * m)) :
    (1 : ℝ) / δ ≤
      ∏ j ∈ Finset.Icc 1 (δ - 1),
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
  rcases eq_or_lt_of_le hδ with rfl | hδ4
  · have hy17 : 17 * t + 31 ≤ 7 * y := by nlinarith
    simpa using product_lower_degree_three t y ht7 hy17
  have hδ4le : 4 ≤ δ := by omega
  rcases eq_or_lt_of_le hδ4le with rfl | hδ5
  · have ht7 : 7 ≤ t := by omega
    have hy31 : 31 * (t + 1) ≤ 9 * y := by
      nlinarith
    simpa using product_lower_degree_four t y ht7 hy31
  have hδ5le : 5 ≤ δ := by omega
  rcases eq_or_lt_of_le hδ5le with rfl | hδ6
  · have ht9 : 9 ≤ t := by omega
    have hy49 : 49 * (t + 1) ≤ 11 * y := by
      nlinarith
    simpa using product_lower_degree_five t y ht9 hy49
  · have hd5 : 5 ≤ δ - 1 := by omega
    have hnat : δ - 1 + 1 = δ := by omega
    have hcast : ((δ - 1 : ℕ) : ℝ) + 1 = (δ : ℝ) := by
      exact_mod_cast hnat
    simpa [one_div, hcast] using
      product_lower_large_degree (δ - 1) t y hd5 (by omega) hy

end Erdos570
