/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Matrix Function

namespace Erdos974

/-- Data associated with the problem. -/
structure ProblemData (n : ℕ) [NeZero n] where
  /-- The tuple of complex numbers `z` -/
  z : Fin n → ℂ
  /-- The starting indices of the zero runs -/
  (a b : ℤ)
  /-- z 0 = 1 -/
  z0 : z 0 = 1
  /-- The zero runs are distinct -/
  hab : a < b
  /-- A run of `n - 1` zero power sums starts from `a` -/
  sums_a : ∀ k < n - 1, ∑ i, z i ^ (a + k) = 0
  /-- A run of `n - 1` zero power sums starts from `b` -/
  sums_b : ∀ k < n - 1, ∑ i, z i ^ (b + k) = 0

variable {n : ℕ} [NeZero n]

lemma zpow_add_int_natCast {z : ℂ} {m : ℤ} {k : ℕ} (hmk : m + (k : ℤ) ≠ 0) :
    z ^ (m + k) = z ^ k * z ^ m := by
  rw [add_comm, zpow_add' (by lia), zpow_natCast]

lemma sum_zpow_ne_zero_exponent {z : Fin n → ℂ} {m : ℤ} {k : ℕ} (hsum : ∑ i, z i ^ (m + k) = 0) :
    m + k ≠ 0 := by
  by_contra h
  simp_all

/-- `n - 1` consecutive zero power sums starting at `m`, combined with `z 0 = 1`,
force `z` to be injective.

**Proof sketch.** Let `S = univ.image z` and `r = #S`. Suppose `r < n` (toward
contradiction). For each `y ∈ S`, define the *compressed weight*
`c(y) := |{i | z i = y}| * y ^ m`. Then
`∑_{y ∈ S} c(y) * y ^ k = ∑_i z_i^{m+k} = 0` for `k = 0, …, n − 2`.
Because `r ≤ n − 1`, the first `r` of these equations (for `k = 0, …, r − 1`) form
a Vandermonde system on the `r` distinct values in `S`.
By `eq_zero_of_forall_pow_sum_mul_pow_eq_zero` (Vandermonde invertibility), `c = 0`.
But `c(1) ≥ 1` since `z 0 = 1`, giving a contradiction. -/
lemma injective_of_power_sums {z : Fin n → ℂ} (hz0 : z 0 = 1) {m : ℤ}
    (hm : ∀ k < n - 1, ∑ i, z i ^ (m + k) = 0) : Injective z := by
  -- Let `S = univ.image z` and `r = #S`. Suppose `r < n` (toward contradiction).
  by_contra h_noninj
  obtain ⟨S, hS_card⟩ : ∃ S : Finset ℂ, #S < n ∧ ∀ i, z i ∈ S := by
    refine ⟨univ.image z, ?_, ?_⟩
    · refine (card_image_le.trans (by simp)).lt_of_ne fun h ↦ h_noninj ?_
      simpa using card_image_iff.mp (by simpa : #(univ.image z) = #univ)
    · simp
  -- For each `k < n - 1`, using `sum_fiberwise_of_maps_to`:
  have h_sum {k} (hk : k < n - 1) : ∑ y ∈ S, #{i | z i = y} * y ^ (m + k) = 0 := by
    convert hm k hk using 1; rw [← sum_congr rfl fun x hx ↦ by rw [card_filter]]
    simp only [Nat.cast_sum, sum_mul]
    simp_all [sum_comm]
  -- Choose an equiv `e : Fin r ≃ S` (via `equivFin S` or similar).
  let e : Fin #S ≃ S := Fintype.equivOfCardEq (by simp)
  -- Define `c : Fin r → ℂ` by `c t = #{i | z i = e t} * (e t).1 ^ m`.
  let c (t : Fin #S) := #{i | z i = e t} * (e t).1 ^ m
  have hc {k} (hk : k < #S) : ∑ t, c t * (e t).1 ^ k = 0 := by
    have h_sum_eq :
        ∑ y ∈ S, #{i | z i = y} * y ^ (m + k) = ∑ t, #{i | z i = e t} * (e t).1 ^ (m + k) := by
      rw [← sum_coe_sort]
      conv_lhs => rw [← e.sum_comp]
    replace h_sum_eq : ∑ y ∈ S, #{i | z i = y} * y ^ (m + k) = ∑ t, c t * (e t).1 ^ k := by
      convert h_sum_eq using 2
      rw [zpow_add'] <;> norm_num
      · ring
      · by_cases h : m + k = 0 <;> simp [h]
        specialize hm k (by lia)
        simp_all [add_eq_zero_iff_eq_neg]
    exact h_sum_eq ▸ h_sum (hk.trans_le (Nat.le_sub_one_of_lt hS_card.1))
  -- By `eq_zero_of_forall_pow_sum_mul_pow_eq_zero`, `c = 0`.
  have hc_zero : c = 0 :=
    eq_zero_of_forall_pow_sum_mul_pow_eq_zero (fun i j hij ↦ by simpa using hij) fun i ↦ hc i.2
  -- But `1 ∈ S` (since `z 0 = 1`), so for some `t₀`, `e t₀ = 1`.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, (e t₀).1 = 1 :=
    ⟨e.symm ⟨1, hS_card.2 0 |> fun h ↦ by simp_all⟩, by simp⟩
  replace hc_zero := congr_fun hc_zero t₀; simp_all [c, e]

/-- Given `z` injective, `z 0 = 1`, and `n - 1` consecutive zero power sums at `m`,
every `z i` is nonzero.

**Proof sketch.** Suppose `z j = 0` for some `j`. Since `z 0 = 1 ≠ 0`, we have `j ≠ 0`.
By injectivity, `z i ≠ 0` for `i ≠ j`. Since `m + k ≠ 0` for all relevant `k`
(by `sum_zpow_ne_zero_exponent`), `0 ^ (m + k) = 0`, so the zero term drops from each sum:
`∑_{i ≠ j} z_i^{m+k} = 0`.
After reindexing via `Fin.succAbove j`, the remaining `n − 1` nonzero distinct values
satisfy an `(n−1) × (n−1)` Vandermonde system, forcing all weights `z_i^m = 0`.
But `z_0^m = 1 ≠ 0`, contradiction. -/
lemma ne_zero_of_power_sums {z : Fin n → ℂ} (hz0 : z 0 = 1) {m : ℤ}
    (hm : ∀ k < n - 1, ∑ i, z i ^ (m + k) = 0) : ∀ i, z i ≠ 0 := fun i hi ↦ by
  have hInj := injective_of_power_sums hz0 hm
  replace hm {k} (hk : k < n - 1) : ∑ j ∈ univ.erase i, z j ^ m * z j ^ k = 0 := by
    specialize hm k hk
    by_cases hmk : m + k = 0
    · simp_all
    · conv_lhs at hm => enter [2, i]; rw [zpow_add' (by tauto), zpow_natCast]
      rw [sum_erase_eq_sub (mem_univ _), hm, ← zpow_natCast, ← zpow_add' (by tauto), hi,
        _root_.zero_zpow _ hmk, sub_zero]
  have ceq : #(univ.erase i) = n - 1 := by simp
  let g : Fin (n - 1) ↪o Fin n := (univ.erase i).orderEmbOfFin ceq
  replace hm (k : Fin (n - 1)) : ∑ j, z (g j) ^ m * z (g j) ^ k.1 = 0 := by
    specialize hm k.2
    rwa [← map_orderEmbOfFin_univ _ ceq, sum_map] at hm
  replace hm := eq_zero_of_forall_pow_sum_mul_pow_eq_zero (hInj.comp g.injective) hm
  replace hm (j) : z (g j) = 0 := eq_zero_of_zpow_eq_zero congr($hm j)
  rcases n with _ | _ | n
  · exact i.elim0
  · simp [i.fin_one_eq_zero, hz0] at hi
  · specialize hm ⟨0, by lia⟩
    rw [← hi, hInj.eq_iff] at hm
    have : g ⟨0, by lia⟩ ∈ univ.erase i := orderEmbOfFin_mem _ ceq _
    simp [← hm] at this

/-- Two kernel vectors of the `(n−1) × n` Vandermonde submatrix
`(z_i^k)_{k < n-1, i < n}` that agree at position `0` must be equal.

**Proof sketch.** Let `d = v − w`. Then `d 0 = 0` and
`∑_i z_i^k · d_i = 0` for every `k < n − 1`.
Split the sum using `Fin.cons`:
`z_0^k · d_0 + ∑_{j : Fin (n−1)} z_{j+1}^k · d_{j+1} = 0`.
Since `z_0^k · 0 = 0`, this gives
`∑_j (z ∘ Fin.succ) j ^ k · (d ∘ Fin.succ) j = 0` for `k < n − 1`.
The `(n−1) × (n−1)` Vandermonde matrix of `z ∘ Fin.succ` is invertible
(because `z` is injective implies `z ∘ Fin.succ` is injective).
By `eq_zero_of_forall_pow_sum_mul_pow_eq_zero`, `d ∘ Fin.succ = 0`.
Combined with `d 0 = 0`, `d = 0`, so `v = w`. -/
lemma eq_of_vandermonde_ker {z v w : Fin n → ℂ} (hInj : Injective z)
    (hv : ∀ k < n - 1, ∑ i, z i ^ k * v i = 0)
    (hw : ∀ k < n - 1, ∑ i, z i ^ k * w i = 0)
    (h0 : v 0 = w 0) : v = w := by
  rcases n with _ | _ | n
  · exact (NeZero.ne 0 rfl).elim
  · ext i; simp [i.fin_one_eq_zero, h0]
  · simp only [Fin.sum_univ_succ, add_tsub_cancel_right, Order.lt_add_one_iff,
      Fin.succ_zero_eq_one] at hv hw
    let d : Fin (n + 2) → ℂ := v - w
    have hd0 : d 0 = 0 := by simp [d, h0]
    have hd_sum {k} (hk : k ≤ n) : ∑ i, z i ^ k * d i = 0 := by
      specialize hv k hk; specialize hw k hk; simp_all [d, mul_sub, Fin.sum_univ_succ]
    have hd_split {k} (hk : k ≤ n) : ∑ j : Fin (n + 1), z j.succ ^ k * d j.succ = 0 := by
      specialize hd_sum hk; rw [Fin.sum_univ_succ] at hd_sum; simp_all
    have h_inj_succ : (z ∘ Fin.succ).Injective := hInj.comp (Fin.succ_injective _)
    have h_eq_zero (i : Fin (n + 1)) : ∑ j : Fin (n + 1), d j.succ * z j.succ ^ i.1 = 0 := by
      simpa only [mul_comm] using hd_split i.is_le
    have h_d_succ_zero : d ∘ Fin.succ = 0 :=
      eq_zero_of_forall_pow_sum_mul_pow_eq_zero h_inj_succ h_eq_zero
    ext i; exact sub_eq_zero.mp (i.cases hd0 (congr_fun h_d_succ_zero))

namespace ProblemData

variable (PD : ProblemData n)

lemma z_inj : PD.z.Injective :=
  injective_of_power_sums PD.z0 PD.sums_a

lemma z_ne_zero : ∀ i, PD.z i ≠ 0 :=
  ne_zero_of_power_sums PD.z0 PD.sums_a

/-- All elements of `z` raised to this power must give 1. -/
def q : ℕ := (PD.b - PD.a).toNat

lemma q_pos : PD.q ≠ 0 := by grind [q, PD.hab]

lemma z_qth_root (i : Fin n) : PD.z i ^ PD.q = 1 := by
  have hva (k) (hk : k < n - 1) : ∑ i, PD.z i ^ k * PD.z i ^ PD.a = 0 := by
    have h := PD.sums_a k hk
    simpa [zpow_add_int_natCast (sum_zpow_ne_zero_exponent h)] using h
  have hvb (k) (hk : k < n - 1) : ∑ i, PD.z i ^ k * PD.z i ^ PD.b = 0 := by
    have h := PD.sums_b k hk
    simpa [zpow_add_int_natCast (sum_zpow_ne_zero_exponent h)] using h
  have key := eq_of_vandermonde_ker PD.z_inj hva hvb (by simp [PD.z0])
  replace key : PD.z i ^ PD.a = PD.z i ^ PD.b := congr($key i)
  rw [q, ← zpow_natCast, Int.toNat_sub_of_le PD.hab.le,
    zpow_sub₀ (PD.z_ne_zero _), ← key, div_self (zpow_ne_zero _ (PD.z_ne_zero _))]

open scoped Classical in
/-- The least period of the power sum function applied to `PD.z`. -/
noncomputable def p : ℕ :=
  {p ∈ Icc 1 PD.q | (fun k ↦ ∑ i, PD.z i ^ k).Periodic p}.min'
    ⟨PD.q, mem_filter.mpr ⟨by grind [PD.q_pos], by simp [pow_add, PD.z_qth_root]⟩⟩

variable (PD : ProblemData (2 * n))

/-- The indices `i` such that `z_i^(p/2) = -1`. -/
noncomputable def oddIndices : Finset (Fin (2 * n)) :=
  {i | PD.z i ^ (PD.p / 2) = -1}

theorem erdos_974 {n : ℕ} [NeZero n] (PD : ProblemData (2 * n)) :
    univ.image PD.z = Polynomial.nthRootsFinset n 1 ∪
    Polynomial.nthRootsFinset n (-∏ i ∈ PD.oddIndices, -PD.z i) := by
  sorry

end ProblemData

end Erdos974
