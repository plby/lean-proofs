import Mathlib

/-!
# Valuation and residue-fiber lemmas

These elementary facts support counting quadratic congruences without
introducing a local tree: exact valuation is stable under a deeper
congruence, and every reduction fiber has the expected prime-power size.
-/

namespace Erdos1148.DukeArithmetic

lemma padic_pow_dvd_iff_le_valuation (p : ℕ) [Fact p.Prime]
    (x : PadicInt p) (hx : x ≠ 0) (n : ℕ) :
    (p : PadicInt p) ^ n ∣ x ↔ n ≤ x.valuation := by
  rw [← Ideal.mem_span_singleton]
  exact PadicInt.mem_span_pow_iff_le_valuation x hx n

lemma padic_pow_valuation_dvd (p : ℕ) [Fact p.Prime] (x : PadicInt p) :
    (p : PadicInt p) ^ x.valuation ∣ x := by
  by_cases hx : x = 0
  · simp [hx]
  exact (padic_pow_dvd_iff_le_valuation p x hx _).mpr le_rfl

lemma padic_next_pow_not_dvd (p : ℕ) [Fact p.Prime] (x : PadicInt p) (hx : x ≠ 0) :
    ¬ (p : PadicInt p) ^ (x.valuation + 1) ∣ x := by
  rw [padic_pow_dvd_iff_le_valuation p x hx]
  omega

lemma padic_pow_dvd_natCast_iff (p : ℕ) [Fact p.Prime] (n m : ℕ) :
    (p : PadicInt p) ^ n ∣ (m : PadicInt p) ↔ p ^ n ∣ m := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_natCast, ZMod.natCast_eq_zero_iff]

lemma valuation_eq_of_deep_congruence (p : ℕ) [Fact p.Prime]
    (x y : PadicInt p) (hy : y ≠ 0) (n : ℕ) (hn : y.valuation < n)
    (hcongr : (p : PadicInt p) ^ n ∣ x - y) : x ≠ 0 ∧ x.valuation = y.valuation := by
  have hx : x ≠ 0 := by
    intro hx
    have hydiv : (p : PadicInt p) ^ n ∣ y := by simpa [hx] using hcongr
    exact (not_le.mpr hn) ((padic_pow_dvd_iff_le_valuation p y hy n).mp hydiv)
  have hlow : (p : PadicInt p) ^ y.valuation ∣ x := by
    have hd : (p : PadicInt p) ^ y.valuation ∣ x - y :=
      (pow_dvd_pow _ hn.le).trans hcongr
    simpa only [sub_add_cancel] using dvd_add hd (padic_pow_valuation_dvd p y)
  have hhigh : ¬ (p : PadicInt p) ^ (y.valuation + 1) ∣ x := by
    intro hhigh
    have hd : (p : PadicInt p) ^ (y.valuation + 1) ∣ x - y :=
      (pow_dvd_pow _ hn).trans hcongr
    apply padic_next_pow_not_dvd p y hy
    simpa only [sub_sub_cancel] using dvd_sub hhigh hd
  rw [padic_pow_dvd_iff_le_valuation p x hx] at hlow hhigh
  exact ⟨hx, by omega⟩

lemma valuation_two_le_one (p : ℕ) [Fact p.Prime] : (2 : PadicInt p).valuation ≤ 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have htwo : (2 : PadicInt p) ≠ 0 := by norm_num
  by_contra hn
  have hd : (p : PadicInt p) ^ 2 ∣ 2 :=
    (padic_pow_dvd_iff_le_valuation p 2 htwo 2).mpr (by omega)
  have hdn : p ^ 2 ∣ 2 := (padic_pow_dvd_natCast_iff p 2 2).mp hd
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdn
  nlinarith

/-- Two square roots modulo a prime power lie in at most two smaller residue classes. -/
lemma square_congruence_close_to_sign (p : ℕ) [Fact p.Prime]
    (x y : PadicInt p) (hy : y ≠ 0) (n : ℕ)
    (hcongr : (p : PadicInt p) ^ n ∣ x ^ 2 - y ^ 2) :
    (p : PadicInt p) ^ (n - (y.valuation + (2 : PadicInt p).valuation)) ∣ x - y ∨
    (p : PadicInt p) ^ (n - (y.valuation + (2 : PadicInt p).valuation)) ∣ x + y := by
  by_cases hminus : x - y = 0
  · exact Or.inl (hminus ▸ dvd_zero _)
  by_cases hplus : x + y = 0
  · exact Or.inr (hplus ▸ dvd_zero _)
  have htwo : (2 : PadicInt p) ≠ 0 := by norm_num
  have hprod : (p : PadicInt p) ^ n ∣ (x - y) * (x + y) := by
    convert hcongr using 1
    ring
  have hsum : n ≤ (x - y).valuation + (x + y).valuation := by
    have h := (padic_pow_dvd_iff_le_valuation p _ (mul_ne_zero hminus hplus) n).mp hprod
    rwa [PadicInt.valuation_mul hminus hplus] at h
  have hmin : min (x - y).valuation (x + y).valuation ≤
      y.valuation + (2 : PadicInt p).valuation := by
    have hm : (p : PadicInt p) ^ min (x - y).valuation (x + y).valuation ∣ x - y :=
      (pow_dvd_pow _ (min_le_left _ _)).trans (padic_pow_valuation_dvd p (x - y))
    have hp : (p : PadicInt p) ^ min (x - y).valuation (x + y).valuation ∣ x + y :=
      (pow_dvd_pow _ (min_le_right _ _)).trans (padic_pow_valuation_dvd p (x + y))
    have htwoY : (p : PadicInt p) ^ min (x - y).valuation (x + y).valuation ∣ 2 * y := by
      convert dvd_sub hp hm using 1
      ring
    have h := (padic_pow_dvd_iff_le_valuation p _ (mul_ne_zero htwo hy) _).mp htwoY
    simpa only [PadicInt.valuation_mul htwo hy, add_comm] using h
  rw [padic_pow_dvd_iff_le_valuation p _ hminus, padic_pow_dvd_iff_le_valuation p _ hplus]
  omega

lemma padic_pow_dvd_of_dvd_mul (p : ℕ) [Fact p.Prime]
    (a x : PadicInt p) (ha : a ≠ 0) (n : ℕ) (h : (p : PadicInt p) ^ n ∣ a * x) :
    (p : PadicInt p) ^ (n - a.valuation) ∣ x := by
  by_cases hx : x = 0
  · simp [hx]
  have hv := (padic_pow_dvd_iff_le_valuation p _ (mul_ne_zero ha hx) n).mp h
  rw [PadicInt.valuation_mul ha hx] at hv
  apply (padic_pow_dvd_iff_le_valuation p x hx _).mpr
  omega

end Erdos1148.DukeArithmetic
