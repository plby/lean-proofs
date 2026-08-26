/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The deterministic relation between simple roots and sign changes.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointCover

namespace Erdos521

noncomputable def signChange (u v : ℝ) : ℕ := if u * v < 0 then 1 else 0

theorem polynomial_exists_root_of_mul_nonpos (p : Polynomial ℝ) {a b : ℝ}
    (hab : a ≤ b) (hprod : p.eval a * p.eval b ≤ 0) :
    ∃ x ∈ Set.Icc a b, p.eval x = 0 := by
  rcases mul_nonpos_iff.mp hprod with h | h
  · exact intermediate_value_Icc' hab p.continuous.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Icc hab p.continuous.continuousOn h

theorem polynomial_unique_simple_root_sign_change (p : Polynomial ℝ) {a b r : ℝ}
    (hr : r ∈ Set.Ioo a b) (hroot : p.eval r = 0) (hderiv : p.derivative.eval r ≠ 0)
    (hunique : ∀ x ∈ Set.Icc a b, p.eval x = 0 → x = r) :
    p.eval a * p.eval b < 0 := by
  obtain ⟨q, hp⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hqr : q.eval r ≠ 0 := by
    have hid : p.derivative.eval r = q.eval r := by
      rw [hp, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
      simp
    exact hid ▸ hderiv
  have hqprod : 0 < q.eval a * q.eval b := by
    by_contra hh
    obtain ⟨x, hx, hxzero⟩ := polynomial_exists_root_of_mul_nonpos q (hr.1.trans hr.2).le
      (le_of_not_gt hh)
    have hpzero : p.eval x = 0 := by rw [hp, Polynomial.eval_mul, hxzero, mul_zero]
    have hxr := hunique x hx hpzero
    exact hqr (hxr ▸ hxzero)
  calc
    p.eval a * p.eval b = ((a - r) * (b - r)) * (q.eval a * q.eval b) := by
      rw [hp]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      ring
    _ < 0 := mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (sub_neg.mpr hr.1) (sub_pos.mpr hr.2)) hqprod

theorem intervalRootCount_eq_signChange (ε : ℕ → ℝ) (n : ℕ) (hε₀ : ε 0 ≠ 0)
    {a b : ℝ} (hab : a ≤ b) (ha : (polynomial ε n).eval a ≠ 0)
    (hb : (polynomial ε n).eval b ≠ 0) (hcount : intervalRootCount ε n a b ≤ 1)
    (hsimple : ∀ x ∈ Set.Icc a b, (polynomial ε n).eval x = 0 →
      (polynomial ε n).derivative.eval x ≠ 0) :
    intervalRootCount ε n a b = signChange ((polynomial ε n).eval a) ((polynomial ε n).eval b) := by
  classical
  let S := (realRoots ε n).filter fun x ↦ x ∈ Set.Icc a b
  have hmem (x : ℝ) : x ∈ realRoots ε n ↔ (polynomial ε n).eval x = 0 := by
    simpa only [← polynomial_eval] using mem_realRoots ε n hε₀ x
  by_cases hsign : (polynomial ε n).eval a * (polynomial ε n).eval b < 0
  · rw [signChange, if_pos hsign]
    obtain ⟨x, hx, hxzero⟩ := polynomial_exists_root_of_mul_nonpos (polynomial ε n) hab hsign.le
    have hnonempty : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨(hmem x).mpr hxzero, hx⟩⟩
    exact le_antisymm hcount (Finset.card_pos.mpr hnonempty)
  · rw [signChange, if_neg hsign]
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < S.card from hpos)
    obtain ⟨hrroot, hrI⟩ := Finset.mem_filter.mp hr
    have hrzero := (hmem r).mp hrroot
    have hra : r ≠ a := by intro h; exact ha (h ▸ hrzero)
    have hrb : r ≠ b := by intro h; exact hb (h ▸ hrzero)
    have hrIoo : r ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hrI.1 hra.symm, lt_of_le_of_ne hrI.2 hrb⟩
    apply hsign
    apply polynomial_unique_simple_root_sign_change (polynomial ε n) hrIoo hrzero (hsimple r hrI hrzero)
    intro x hx hxzero
    exact (Finset.card_le_one.mp hcount) x (Finset.mem_filter.mpr ⟨(hmem x).mpr hxzero, hx⟩) r hr

end Erdos521
