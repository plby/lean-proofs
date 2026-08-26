import ErdosProblems.Erdos1038.CertifiedLog


/-!
# The removable `artanh` quotient for the one-cut soft chart

The coordinate `s = tanh(log(u) / 2)^2` turns the coalescing inner root into
an ordinary root at `s = 0`.  The only non-rational function left in that
chart is `artanh(sqrt s) / sqrt s`; this file supplies its exact finite-series
bounds and its derivative away from the removable endpoint.
-/

open Filter Set
open scoped Topology

namespace Erdos1038

noncomputable section

def softT (s : ℝ) : ℝ :=
  if s = 0 then 1 else Real.artanh (Real.sqrt s) / Real.sqrt s

def softTPrime (s : ℝ) : ℝ :=
  if s = 0 then 1 / 3 else
    (1 / (1 - s) - softT s) / (2 * s)

def softTLower (n : Nat) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, s ^ i / (2 * (i : ℝ) + 1)

def softTUpper (n : Nat) (s : ℝ) : ℝ :=
  softTLower n s + s ^ n / (1 - s)

private theorem odd_power_div_sqrt {s : ℝ} (hs : 0 < s) (i : Nat) :
    (Real.sqrt s) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) /
        Real.sqrt s =
      s ^ i / (2 * (i : ℝ) + 1) := by
  have ht : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hsq : (Real.sqrt s) ^ 2 = s := by
    nlinarith [Real.sq_sqrt hs.le]
  field_simp [ht]
  rw [show 2 * i + 1 = 2 * i + 1 by rfl, pow_add, pow_mul, hsq]
  ring

private theorem odd_sum_div_sqrt {s : ℝ} (hs : 0 < s) (n : Nat) :
    (∑ i ∈ Finset.range n,
        (Real.sqrt s) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) /
        Real.sqrt s = softTLower n s := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => odd_power_div_sqrt hs i

private theorem softTLower_zero {n : Nat} (hn : 0 < n) :
    softTLower n 0 = 1 := by
  rw [softTLower, Finset.sum_eq_single 0]
  · norm_num
  · intro i hi hi0
    rw [zero_pow hi0]
    norm_num
  · exact fun h => (h (Finset.mem_range.2 hn)).elim

theorem softT_bounds {n : Nat} (hn : 0 < n) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    softTLower n s ≤ softT s ∧ softT s ≤ softTUpper n s := by
  by_cases hs : s = 0
  · subst s
    rw [softTLower_zero hn]
    simp [softT, softTUpper, softTLower_zero hn,
      zero_pow (Nat.ne_of_gt hn)]
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    let t := Real.sqrt s
    have ht0 : 0 ≤ t := Real.sqrt_nonneg s
    have htpos : 0 < t := Real.sqrt_pos.2 hspos
    have htsq : t ^ 2 = s := by
      dsimp [t]
      nlinarith [Real.sq_sqrt hs0]
    have ht1 : t < 1 := by
      nlinarith [sq_lt_sq₀ ht0 (by norm_num : (0 : ℝ) ≤ 1), htsq, hs1]
    have hlo := Real.sum_range_le_log_div ht0 ht1 n
    have hhi := Real.log_div_le_sum_range_add ht0 ht1 n
    have hart : Real.artanh t =
        1 / 2 * Real.log ((1 + t) / (1 - t)) :=
      Real.artanh_eq_half_log ⟨by linarith, ht1.le⟩
    have hsum :
        (∑ i ∈ Finset.range n,
            t ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) / t =
          softTLower n s := by
      simpa [t] using! odd_sum_div_sqrt hspos n
    have htail :
        t ^ (2 * n + 1) / (1 - t ^ 2) / t =
          s ^ n / (1 - s) := by
      have htne : t ≠ 0 := htpos.ne'
      rw [pow_add, pow_mul, htsq]
      field_simp [htne, show 1 - s ≠ 0 by linarith]
    have hlo' := (div_le_div_iff_of_pos_right htpos).2 hlo
    have hhi' := (div_le_div_iff_of_pos_right htpos).2 hhi
    have hleft :
        (1 / 2 * Real.log ((1 + t) / (1 - t))) / t =
          Real.artanh t / t := by rw [hart]
    have hright :
        ((∑ i ∈ Finset.range n,
            t ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
            t ^ (2 * n + 1) / (1 - t ^ 2)) / t =
          softTLower n s + s ^ n / (1 - s) := by
      rw [add_div, hsum, htail]
    rw [hsum, hleft] at hlo'
    rw [hleft, hright] at hhi'
    simpa [softT, hs, softTUpper, t] using! And.intro hlo' hhi'

private theorem eventually_artanh_eq_half_log {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh =ᶠ[𝓝 t]
      (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x))) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩

private theorem hasDerivAt_artanh {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - t ^ 2)) t := by
  rcases ht with ⟨htlo, hthi⟩
  have hn : HasDerivAt (fun x : ℝ => 1 + x) 1 t := by
    simpa only [Pi.add_apply, id_eq, zero_add] using!
      (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
  have hd : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using!
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have hden : 1 - t ≠ 0 := (sub_pos.2 hthi).ne'
  have hnum : 1 + t ≠ 0 := (by linarith : 0 < 1 + t).ne'
  have hone : 1 - t ^ 2 ≠ 0 := by
    have : 0 < (1 - t) * (1 + t) :=
      mul_pos (sub_pos.2 hthi) (by linarith)
    nlinarith
  have hratio : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x))
      (2 / (1 - t) ^ 2) t := by
    convert! hn.div hd hden using 1
    field_simp [hden]
    ring
  have hratioNe : (1 + t) / (1 - t) ≠ 0 := by
    exact div_ne_zero hnum hden
  have hlog := hratio.log hratioNe
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hformula : HasDerivAt
      (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x)))
      (1 / (1 - t ^ 2)) t := by
    convert! hhalf using 1
    · field_simp [hden, hnum, hone]
      ring
  exact hformula.congr_of_eventuallyEq
    (eventually_artanh_eq_half_log ⟨htlo, hthi⟩)

theorem hasDerivAt_softT {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt softT (softTPrime s) s := by
  have hsne : s ≠ 0 := hs0.ne'
  have htpos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have htsq : (Real.sqrt s) ^ 2 = s := by
    nlinarith [Real.sq_sqrt hs0.le]
  have ht1 : Real.sqrt s < 1 := by
    nlinarith [sq_lt_sq₀ (Real.sqrt_nonneg s)
      (by norm_num : (0 : ℝ) ≤ 1), htsq, hs1]
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hs0)
  have hart := (hasDerivAt_artanh ⟨by linarith, ht1⟩).comp s hsqrt
  have hquot := hart.div hsqrt (Real.sqrt_ne_zero'.2 hs0)
  have hevent : softT =ᶠ[𝓝 s]
      (fun x => Real.artanh (Real.sqrt x) / Real.sqrt x) := by
    filter_upwards [eventually_ne_nhds hsne] with x hx
    simp [softT, hx]
  have hraw := hquot.congr_of_eventuallyEq (by
    simpa [Function.comp_def, Pi.div_apply] using! hevent)
  simp only [Function.comp_apply] at hraw
  convert! hraw using 1
  simp only [softTPrime, if_neg hsne]
  rw [show softT s = Real.artanh (Real.sqrt s) / Real.sqrt s by
    simp [softT, hsne]]
  field_simp [hsne, htpos.ne', show 1 - s ≠ 0 by linarith]
  rw [htsq]
  ring

theorem softTPrime_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 / 3 + 2 * s / 5 + 3 * s ^ 2 / 7 : ℝ) ≤ softTPrime s ∧
      softTPrime s ≤
        1 / (2 * (1 - s)) - 1 / 6 - s / 10 - s ^ 2 / 14 := by
  by_cases hs : s = 0
  · subst s
    norm_num [softTPrime]
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hT4 := softT_bounds (n := 4) (by norm_num) hs0 hs1
    rw [softTPrime, if_neg hs]
    constructor
    · have hu := hT4.2
      simp [softTUpper, softTLower, Finset.sum_range_succ] at hu
      have hden : 0 < 2 * s := by positivity
      apply (le_div_iff₀ hden).2
      have h1s : 0 < 1 - s := sub_pos.2 hs1
      field_simp [h1s.ne'] at hu ⊢
      nlinarith
    · have hl := hT4.1
      simp [softTLower, Finset.sum_range_succ] at hl
      have hden : 0 < 2 * s := by positivity
      apply (div_le_iff₀ hden).2
      have h1s : 0 < 1 - s := sub_pos.2 hs1
      field_simp [h1s.ne'] at hl ⊢
      nlinarith

end

end Erdos1038
