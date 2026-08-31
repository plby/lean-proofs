/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Short Egyptian expansions from factorials

The elementary mixed-radix construction in this file is the quantitative
replacement for an unrestricted greedy Egyptian-fraction expansion.  Every
integer below `L!` is a sum of at most `L - 1` distinct positive divisors of
`L!`.  Consequently every proper fraction `a / q`, with `q \mid L!`, is a
sum of at most `2 * (L - 1)` distinct unit fractions.
-/

namespace Erdos284

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Every `x < L!` is a sum of at most `L - 1` distinct positive divisors of
`L!`.  This is the descending mixed-radix expansion with radices
`L, L-1, ..., 2`.
-/
theorem exists_divisor_sum_factorial :
    ∀ L x : ℕ, x < L.factorial →
      ∃ D : Finset ℕ,
        (∀ d ∈ D, 0 < d ∧ d ∣ L.factorial) ∧
        D.sum id = x ∧ D.card ≤ L - 1 := by
  intro L
  induction L with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa using hx
      subst x
      exact ⟨∅, by simp⟩
  | succ L ih =>
      intro x hx
      let q := x / (L + 1)
      let a := x % (L + 1)
      have hfac : (L + 1).factorial = (L + 1) * L.factorial := by
        rw [Nat.factorial_succ]
      have hq : q < L.factorial := by
        dsimp [q]
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < L + 1)]
        simpa [hfac, Nat.mul_comm] using hx
      obtain ⟨D, hDpos, hDsum, hDcard⟩ := ih q hq
      let E := D.image (fun d ↦ (L + 1) * d)
      have hinj : Set.InjOn (fun d : ℕ ↦ (L + 1) * d) D := by
        intro d hd e he hde
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < L + 1) hde
      have hEsum : E.sum id = (L + 1) * q := by
        rw [show E = D.image (fun d ↦ (L + 1) * d) by rfl,
          Finset.sum_image hinj]
        have h := congrArg (fun z : ℕ ↦ (L + 1) * z) hDsum
        simpa [Finset.mul_sum] using h
      have hEcard : E.card = D.card := by
        exact Finset.card_image_iff.mpr hinj
      have hEpos : ∀ d ∈ E, 0 < d ∧ d ∣ (L + 1).factorial := by
        intro d hd
        rw [show E = D.image (fun d ↦ (L + 1) * d) by rfl,
          Finset.mem_image] at hd
        rcases hd with ⟨e, he, rfl⟩
        refine ⟨Nat.mul_pos (by omega) (hDpos e he).1, ?_⟩
        rw [hfac]
        exact Nat.mul_dvd_mul_left (L + 1) (hDpos e he).2
      have ha_lt : a < L + 1 := by
        exact Nat.mod_lt _ (by omega)
      have hdecomp : x = (L + 1) * q + a := by
        dsimp [q, a]
        exact (Nat.div_add_mod x (L + 1)).symm
      by_cases ha0 : a = 0
      · subst a
        refine ⟨E, hEpos, ?_, ?_⟩
        · exact hEsum.trans (by omega)
        · rw [hEcard]
          omega
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        have hadvd : a ∣ (L + 1).factorial := by
          rw [hfac]
          exact dvd_mul_of_dvd_right
            (Nat.dvd_factorial hapos (by omega : a ≤ L)) (L + 1)
        have haE : a ∉ E := by
          intro ha
          obtain ⟨ha_pos, _⟩ := hEpos a ha
          rw [show E = D.image (fun d ↦ (L + 1) * d) by rfl,
            Finset.mem_image] at ha
          rcases ha with ⟨d, hd, had⟩
          have hlarge : L + 1 ≤ (L + 1) * d := by
            exact Nat.le_mul_of_pos_right (L + 1) (hDpos d hd).1
          omega
        refine ⟨insert a E, ?_, ?_, ?_⟩
        · intro d hd
          rw [Finset.mem_insert] at hd
          rcases hd with rfl | hd
          · exact ⟨hapos, hadvd⟩
          · exact hEpos d hd
        · rw [Finset.sum_insert haE, hEsum]
          simp [hdecomp, add_comm]
        · rw [Finset.card_insert_of_notMem haE, hEcard]
          omega

/-- A proper fraction whose denominator is at most `L!` has a distinct
Egyptian expansion with at most `2 * (L - 1)` terms. -/
theorem exists_short_egyptian_of_le_factorial
    {L a q : ℕ} (ha : 0 < a) (haq : a < q) (hq : q ≤ L.factorial) :
    ∃ E : Finset ℕ,
      0 ∉ E ∧ UnitFractions.rec_sum E = (a : ℚ) / q ∧
        E.card ≤ 2 * (L - 1) := by
  let Q := L.factorial
  let b := a * Q / q
  let r := a * Q % q
  have hqpos : 0 < q := ha.trans haq
  have hQpos : 0 < Q := by
    exact Nat.factorial_pos L
  have hbQ : b < Q := by
    dsimp [b]
    rw [Nat.div_lt_iff_lt_mul hqpos]
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right haq hQpos
  have hrq : r < q := by
    exact Nat.mod_lt _ hqpos
  have hrQ : r < Q := hrq.trans_le hq
  obtain ⟨D, hDpos, hDsum, hDcard⟩ :=
    exists_divisor_sum_factorial L b hbQ
  obtain ⟨R, hRpos, hRsum, hRcard⟩ :=
    exists_divisor_sum_factorial L r hrQ
  let F := D.image (fun d ↦ Q / d)
  let G := R.image (fun d ↦ q * Q / d)
  have hdivInj : Set.InjOn (fun d : ℕ ↦ Q / d) D := by
    intro d hd e he hde
    have hdQ := (hDpos d hd).2
    have heQ := (hDpos e he).2
    have hcpos : 0 < Q / d := Nat.div_pos (Nat.le_of_dvd hQpos hdQ) (hDpos d hd).1
    have hmul : (Q / d) * d = (Q / e) * e := by
      rw [Nat.div_mul_cancel hdQ, Nat.div_mul_cancel heQ]
    change Q / d = Q / e at hde
    apply Nat.eq_of_mul_eq_mul_left hcpos
    exact hmul.trans (by rw [hde])
  have hqdivInj : Set.InjOn (fun d : ℕ ↦ q * Q / d) R := by
    intro d hd e he hde
    have hdQ := (hRpos d hd).2
    have heQ := (hRpos e he).2
    have hdqQ : d ∣ q * Q := hdQ.trans (Nat.dvd_mul_left Q q)
    have heqQ : e ∣ q * Q := heQ.trans (Nat.dvd_mul_left Q q)
    have hqQpos : 0 < q * Q := Nat.mul_pos hqpos hQpos
    have hcpos : 0 < q * Q / d :=
      Nat.div_pos (Nat.le_of_dvd hqQpos hdqQ) (hRpos d hd).1
    have hmul : (q * Q / d) * d = (q * Q / e) * e := by
      rw [Nat.div_mul_cancel hdqQ, Nat.div_mul_cancel heqQ]
    change q * Q / d = q * Q / e at hde
    apply Nat.eq_of_mul_eq_mul_left hcpos
    exact hmul.trans (by rw [hde])
  have hFcard : F.card = D.card := by
    exact Finset.card_image_iff.mpr hdivInj
  have hGcard : G.card = R.card := by
    exact Finset.card_image_iff.mpr hqdivInj
  have hFpos : ∀ n ∈ F, 0 < n := by
    intro n hn
    rw [show F = D.image (fun d ↦ Q / d) by rfl,
      Finset.mem_image] at hn
    rcases hn with ⟨d, hd, rfl⟩
    exact Nat.div_pos (Nat.le_of_dvd hQpos (hDpos d hd).2) (hDpos d hd).1
  have hGpos : ∀ n ∈ G, 0 < n := by
    intro n hn
    rw [show G = R.image (fun d ↦ q * Q / d) by rfl,
      Finset.mem_image] at hn
    rcases hn with ⟨d, hd, rfl⟩
    have hdvd : d ∣ q * Q := (hRpos d hd).2.trans (Nat.dvd_mul_left Q q)
    exact Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hqpos hQpos) hdvd) (hRpos d hd).1
  have hFle : ∀ n ∈ F, n ≤ Q := by
    intro n hn
    rw [show F = D.image (fun d ↦ Q / d) by rfl,
      Finset.mem_image] at hn
    rcases hn with ⟨d, hd, rfl⟩
    exact Nat.div_le_self _ _
  have hGgt : ∀ n ∈ G, Q < n := by
    intro n hn
    rw [show G = R.image (fun d ↦ q * Q / d) by rfl,
      Finset.mem_image] at hn
    rcases hn with ⟨d, hd, rfl⟩
    have hdle : d ≤ r := by
      rw [← hRsum]
      exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hd
    have hdq : d < q := hdle.trans_lt hrq
    obtain ⟨c, hc⟩ := (hRpos d hd).2
    have hQc : Q = d * c := by simpa [Q] using hc
    have hcpos : 0 < c := by
      by_contra hc0
      have : c = 0 := Nat.eq_zero_of_not_pos hc0
      have hQzero : Q = 0 := by simpa [this] using hQc
      exact (Nat.ne_of_gt hQpos) hQzero
    have hdiv : q * Q / d = q * c := by
      rw [hQc]
      have hrearr : q * (d * c) = d * (q * c) := by ac_rfl
      rw [hrearr]
      exact Nat.mul_div_cancel_left (q * c) (hRpos d hd).1
    rw [hdiv, hQc]
    exact Nat.mul_lt_mul_of_pos_right hdq hcpos
  have hFG : Disjoint F G := by
    rw [Finset.disjoint_left]
    intro n hnF hnG
    exact (not_lt_of_ge (hFle n hnF)) (hGgt n hnG)
  have hFsum : UnitFractions.rec_sum F = (b : ℚ) / Q := by
    rw [UnitFractions.rec_sum]
    rw [show F = D.image (fun d ↦ Q / d) by rfl,
      Finset.sum_image hdivInj]
    calc
      (∑ d ∈ D, (1 : ℚ) / (Q / d : ℕ)) =
          ∑ d ∈ D, (d : ℚ) / Q := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdQ := (hDpos d hd).2
            have hdpos := (hDpos d hd).1
            have hquotpos : 0 < Q / d :=
              Nat.div_pos (Nat.le_of_dvd hQpos hdQ) hdpos
            norm_num [div_eq_iff]
            field_simp
            exact_mod_cast (Nat.div_mul_cancel hdQ).symm
      _ = (D.sum id : ℕ) / Q := by
            rw [← Finset.sum_div]
            congr 2
            simp
      _ = (b : ℚ) / Q := by rw [hDsum]
  have hGsum : UnitFractions.rec_sum G = (r : ℚ) / (q * Q) := by
    rw [UnitFractions.rec_sum]
    rw [show G = R.image (fun d ↦ q * Q / d) by rfl,
      Finset.sum_image hqdivInj]
    calc
      (∑ d ∈ R, (1 : ℚ) / (q * Q / d : ℕ)) =
          ∑ d ∈ R, (d : ℚ) / (q * Q) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdvd : d ∣ q * Q :=
              (hRpos d hd).2.trans (Nat.dvd_mul_left Q q)
            have hdpos := (hRpos d hd).1
            have hquotpos : 0 < q * Q / d := Nat.div_pos
              (Nat.le_of_dvd (Nat.mul_pos hqpos hQpos) hdvd) hdpos
            norm_num [div_eq_iff]
            field_simp
            exact_mod_cast (Nat.div_mul_cancel hdvd).symm
      _ = (R.sum id : ℕ) / (q * Q) := by
            rw [← Finset.sum_div]
            congr 2
            simp
      _ = (r : ℚ) / (q * Q) := by rw [hRsum]
  refine ⟨F ∪ G, ?_, ?_, ?_⟩
  · intro hzero
    rw [Finset.mem_union] at hzero
    rcases hzero with hzero | hzero
    · exact (Nat.ne_of_gt (hFpos 0 hzero)) rfl
    · exact (Nat.ne_of_gt (hGpos 0 hzero)) rfl
  · rw [UnitFractions.rec_sum_disjoint hFG, hFsum, hGsum]
    have hdecomp : a * Q = q * b + r := by
      dsimp [b, r]
      exact (Nat.div_add_mod (a * Q) q).symm
    have hqQ : (q : ℚ) * Q ≠ 0 := mul_ne_zero (by exact_mod_cast hqpos.ne')
      (by exact_mod_cast hQpos.ne')
    have hdecompQ : (a : ℚ) * Q = q * b + r := by
      exact_mod_cast hdecomp
    field_simp
    calc
      (b : ℚ) * q + r = q * b + r := by ring
      _ = a * Q := hdecompQ.symm
      _ = Q * a := by ring
  · rw [Finset.card_union_of_disjoint hFG, hFcard, hGcard]
    omega

end

end Erdos284

#print axioms Erdos284.exists_divisor_sum_factorial
#print axioms Erdos284.exists_short_egyptian_of_le_factorial
