/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos48.External.Erdos822.Density

/-!
# Arithmetic core for Erdős Problem 822

Definitions and elementary range bounds for `n + Nat.totient n`.
-/

namespace Erdos822

open scoped BigOperators Finset

/-- The arithmetic map whose range occurs in Erdős Problem 822. -/
def shiftedTotient (n : ℕ) : ℕ := n + Nat.totient n

/-- The set of values of `n + φ(n)`. -/
def totientRange : Set ℕ := Set.range shiftedTotient

@[simp]
theorem totientRange_eq :
    totientRange = Set.range fun n => n + Nat.totient n := by
  rfl

/-- If `p` is a new prime factor of `m`, the shifted totient of `m * p`
is a linear function of `p`.  This is equation (5.7) in the published
energy argument. -/
theorem shiftedTotient_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m) :
    shiftedTotient (m * p) = (m + Nat.totient m) * p - Nat.totient m := by
  rw [shiftedTotient, Nat.mul_comm m p,
    Nat.totient_mul_of_prime_of_not_dvd hp hpm]
  have hp1 : 1 ≤ p := hp.one_le
  have hle : Nat.totient m ≤ (m + Nat.totient m) * p := by
    calc
      Nat.totient m ≤ m + Nat.totient m := Nat.le_add_left _ _
      _ = (m + Nat.totient m) * 1 := by simp
      _ ≤ (m + Nat.totient m) * p := Nat.mul_le_mul_left _ hp1
  rw [eq_comm, Nat.sub_eq_iff_eq_add hle]
  rw [show p = (p - 1) + 1 by omega]
  simp only [Nat.add_sub_cancel]
  ring

/-- Every shifted-totient value coming from an input at most `x` is at
most `2 * x`; this is the range bound used after Cauchy--Schwarz. -/
theorem shiftedTotient_le_two_mul (n : ℕ) : shiftedTotient n ≤ 2 * n := by
  simpa [shiftedTotient, two_mul] using Nat.add_le_add_left n.totient_le n

/-- If a modulus already divides `φ(m)`, then adjoining `φ(m)` does not
change divisibility by that modulus.  This is the elementary core of the
smooth-part preservation step in GIL. -/
theorem dvd_shiftedTotient_iff_of_dvd_totient {d m : ℕ}
    (hd : d ∣ Nat.totient m) :
    d ∣ shiftedTotient m ↔ d ∣ m := by
  simpa [shiftedTotient] using (Nat.dvd_add_iff_left hd).symm

/-- Prime-power specialization of `dvd_shiftedTotient_iff_of_dvd_totient`.
It is the form used when comparing exact smooth prime-power divisors. -/
theorem pow_dvd_shiftedTotient_iff_of_pow_dvd_totient {p a m : ℕ}
    (hpa : p ^ a ∣ Nat.totient m) :
    p ^ a ∣ shiftedTotient m ↔ p ^ a ∣ m :=
  dvd_shiftedTotient_iff_of_dvd_totient hpa

/-- Local valuation preservation in the form used by the smooth-part
partition: if every relevant power of `p` already divides `φ(m)`, then
`m` and `m + φ(m)` have the same `p`-adic exponent. -/
theorem factorization_shiftedTotient_eq_of_pow_dvd_totient
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hφ : ∀ a : ℕ, a ≤ m.factorization p + 1 →
      p ^ a ∣ Nat.totient m) :
    (shiftedTotient m).factorization p = m.factorization p := by
  have hshift_pos : 0 < shiftedTotient m := by
    exact hm.trans_le (Nat.le_add_right m (Nat.totient m))
  have hshift_ne : shiftedTotient m ≠ 0 := hshift_pos.ne'
  let e := m.factorization p
  have hm_pow : p ^ e ∣ m :=
    (hp.pow_dvd_iff_le_factorization hm.ne').2 (by simp [e])
  have hφe : p ^ e ∣ Nat.totient m := hφ e (by omega)
  have hshift_pow : p ^ e ∣ shiftedTotient m :=
    (pow_dvd_shiftedTotient_iff_of_pow_dvd_totient hφe).2 hm_pow
  have hle : e ≤ (shiftedTotient m).factorization p :=
    (hp.pow_dvd_iff_le_factorization hshift_ne).1 hshift_pow
  have hge : (shiftedTotient m).factorization p ≤ e := by
    by_contra hnot
    have hsucc : e + 1 ≤ (shiftedTotient m).factorization p := by omega
    have hshift_succ : p ^ (e + 1) ∣ shiftedTotient m :=
      (hp.pow_dvd_iff_le_factorization hshift_ne).2 hsucc
    have hφsucc : p ^ (e + 1) ∣ Nat.totient m := hφ (e + 1) (by simp [e])
    have hm_succ : p ^ (e + 1) ∣ m :=
      (pow_dvd_shiftedTotient_iff_of_pow_dvd_totient hφsucc).1 hshift_succ
    have : e + 1 ≤ m.factorization p :=
      (hp.pow_dvd_iff_le_factorization hm.ne').1 hm_succ
    simp [e] at this
  exact le_antisymm hge hle

/-- Finite-set form of the preceding range bound. -/
theorem image_shiftedTotient_subset_Iic {A : Finset ℕ} {x : ℕ}
    (hA : ∀ n ∈ A, n ≤ x) :
    ↑(A.image shiftedTotient) ⊆ Set.Iic (2 * x) := by
  intro t ht
  simp only [Finset.coe_image, Set.mem_image] at ht
  obtain ⟨n, hn, rfl⟩ := ht
  exact (shiftedTotient_le_two_mul n).trans (Nat.mul_le_mul_left 2 (hA n hn))

/-- Every value obtained from a finite input set belongs to the full range. -/
theorem image_shiftedTotient_subset_totientRange (A : Finset ℕ) :
    ↑(A.image shiftedTotient) ⊆ totientRange := by
  intro t ht
  simp only [Finset.coe_image, Set.mem_image] at ht
  obtain ⟨n, _, rfl⟩ := ht
  exact ⟨n, rfl⟩

/-- The image-cardinality lower bound produced by the energy argument
transfers to the range-counting function below `2*x+1`. -/
theorem image_card_le_totientRange_count {A : Finset ℕ} {x : ℕ}
    (hA : ∀ n ∈ A, n ≤ x) :
    (A.image shiftedTotient).card ≤
      (totientRange ∩ Set.Iio (2 * x + 1)).ncard := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ ((Set.finite_Iio _).subset Set.inter_subset_right)
  intro t ht
  refine ⟨image_shiftedTotient_subset_totientRange A ht, ?_⟩
  exact Nat.lt_succ_of_le (image_shiftedTotient_subset_Iic hA ht)

end Erdos822
