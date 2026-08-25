import ErdosProblems.Erdos69.MinorArc
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The finite Vinogradov minor-arc sum

This file packages the elementary Diophantine estimate used after the
fourth-moment expansion in the Matomäki--Radziwiłł--Tao argument.  An initial
interval is enlarged to a whole number of residue blocks modulo `q`; on each
block coprimality permutes the residues, while a rational approximation with
small total drift costs only a factor two in the harmonic tails.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRTVinogradov

noncomputable section

open Erdos69.MinorArc

lemma approximateResidueWeight_nonneg {cap : ℝ} (hcap : 0 ≤ cap) (q r : ℕ) :
    0 ≤ approximateResidueWeight cap q r := by
  unfold approximateResidueWeight
  split_ifs
  · exact hcap
  · positivity

lemma approximateResidueWeight_le_two_reciprocals
    {cap : ℝ} {q r : ℕ} (hr : r ∈ Ico 1 q) :
    approximateResidueWeight cap q r ≤
      2 * (q : ℝ) * ((r : ℝ)⁻¹ + ((q - r : ℕ) : ℝ)⁻¹) := by
  have hr0 : r ≠ 0 := Nat.ne_of_gt (mem_Ico.mp hr).1
  have hrq : r < q := (mem_Ico.mp hr).2
  have hqr0 : q - r ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hrq)
  rw [approximateResidueWeight, if_neg hr0]
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 * q)
  rw [Nat.cast_min, min_def]
  split_ifs
  · exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact le_add_of_nonneg_left (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma sum_approximateResidueWeight_le_harmonic
    (cap : ℝ) (q : ℕ) [NeZero q] (hcap : 0 ≤ cap) :
    (∑ r : Fin q, approximateResidueWeight cap q r.val) ≤
      cap + 4 * q * harmonicBefore q := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hfin :
      (∑ r : Fin q, approximateResidueWeight cap q r.val) =
        ∑ r ∈ range q, approximateResidueWeight cap q r := by
    rw [Finset.sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro r hr
    rw [dif_pos (mem_range.mp hr)]
  rw [hfin]
  rw [sum_eq_add_sum_sdiff_singleton_of_mem (mem_range.mpr hqpos)]
  rw [show approximateResidueWeight cap q 0 = cap by
    simp [approximateResidueWeight]]
  have hdiff : range q \ {0} = Ico 1 q := by
    ext x
    simp only [mem_sdiff, mem_range, mem_singleton, mem_Ico]
    omega
  rw [hdiff]
  have hrest :
      (∑ x ∈ Ico 1 q, approximateResidueWeight cap q x) ≤
        ∑ x ∈ Ico 1 q,
          2 * (q : ℝ) * ((x : ℝ)⁻¹ + ((q - x : ℕ) : ℝ)⁻¹) := by
    exact sum_le_sum fun x hx ↦ approximateResidueWeight_le_two_reciprocals hx
  rw [add_comm cap (∑ x ∈ Ico 1 q, approximateResidueWeight cap q x)]
  refine add_le_add_left hrest cap |>.trans_eq ?_
  simp_rw [mul_add]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hreflect :
      (∑ x ∈ Ico 1 q, (((q - x : ℕ) : ℝ))⁻¹) = harmonicBefore q := by
    simpa [harmonicBefore] using
      (sum_Ico_reflect (fun x : ℕ ↦ ((x : ℝ))⁻¹) 1 (m := q) (n := q)
        (Nat.le_succ q))
  rw [hreflect]
  change
    2 * (q : ℝ) * harmonicBefore q +
          2 * (q : ℝ) * harmonicBefore q + cap =
      cap + 4 * (q : ℝ) * harmonicBefore q
  ring

lemma sum_approximateResidueWeight_coprime_le
    (cap : ℝ) (a q : ℕ) [NeZero q] (ha : a.Coprime q) (hcap : 0 ≤ cap) :
    (∑ n : Fin q, approximateResidueWeight cap q ((a * n.val) % q)) ≤
      cap + 4 * q * harmonicBefore q := by
  have heq :
      (∑ n : Fin q, approximateResidueWeight cap q ((a * n.val) % q)) =
        ∑ r : Fin q, approximateResidueWeight cap q r.val := by
    rw [← Equiv.sum_comp (coprimeResiduePerm a q ha)
      (fun r : Fin q ↦ approximateResidueWeight cap q r.val)]
    apply Fintype.sum_congr
    intro n
    rw [coprimeResiduePerm_val]
  rw [heq]
  exact sum_approximateResidueWeight_le_harmonic cap q hcap

/-- Exact decomposition of a sum whose summand depends only on `n % q`. -/
lemma sum_range_mul_mod (G : ℕ → ℝ) (q B : ℕ) :
    (∑ n ∈ range (B * q), G (n % q)) =
      (B : ℝ) * ∑ r ∈ range q, G r := by
  induction B with
  | zero => simp
  | succ B ih =>
      rw [Nat.succ_mul, sum_range_add, ih]
      have htail :
          (∑ x ∈ range q, G ((B * q + x) % q)) =
            ∑ x ∈ range q, G x := by
        apply sum_congr rfl
        intro x hx
        have hxq : x < q := mem_range.mp hx
        simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hxq]
      rw [htail]
      push_cast
      ring

/-- A nonnegative periodic sum over an arbitrary prefix is bounded by the
next whole number of residue blocks. -/
lemma sum_range_mod_le_next_blocks
    (G : ℕ → ℝ) (q K : ℕ) (hq : 0 < q) (hG : ∀ r, 0 ≤ G r) :
    (∑ n ∈ range K, G (n % q)) ≤
      (((K / q + 1 : ℕ) : ℝ) * ∑ r ∈ range q, G r) := by
  have hK : K ≤ (K / q + 1) * q := by
    have hmod : K % q < q := Nat.mod_lt K hq
    apply Nat.le_of_lt
    calc
      K = K % q + q * (K / q) := (Nat.mod_add_div K q).symm
      _ < q + q * (K / q) := Nat.add_lt_add_right hmod _
      _ = (K / q + 1) * q := by
        rw [Nat.add_mul]
        simp only [one_mul]
        calc
          q + q * (K / q) = q + (K / q) * q := by rw [Nat.mul_comm q]
          _ = (K / q) * q + q := Nat.add_comm _ _
  calc
    (∑ n ∈ range K, G (n % q)) ≤
        ∑ n ∈ range ((K / q + 1) * q), G (n % q) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact range_mono hK
      · intro i hi his
        exact hG _
    _ = (((K / q + 1 : ℕ) : ℝ) * ∑ r ∈ range q, G r) :=
      sum_range_mul_mod G q (K / q + 1)

/-- Fully finite Vinogradov estimate.  The right side is the number of
complete residue blocks needed to cover `0,…,N`, times one harmonic block. -/
theorem cappedInvDist_prefix_bound
    (α ε cap : ℝ) (a q N : ℕ) [NeZero q]
    (ha : a.Coprime q) (hcap : 0 ≤ cap)
    (hε : |α - (a : ℝ) / q| ≤ ε) (hε0 : 0 ≤ ε)
    (hdrift : (N : ℝ) * ε ≤ 1 / (2 * q)) :
    (∑ n ∈ range (N + 1), cappedInvDist cap (α * n)) ≤
      (((N + 1) / q + 1 : ℕ) : ℝ) *
        (cap + 4 * q * harmonicBefore q) := by
  have hpoint : ∀ n ∈ range (N + 1),
      cappedInvDist cap (α * n) ≤
        approximateResidueWeight cap q ((a * n) % q) := by
    intro n hn
    apply cappedInvDist_mul_le_approximateResidueWeight
      α ε cap a q n N (Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using hn))
        hε hε0 hdrift
  calc
    (∑ n ∈ range (N + 1), cappedInvDist cap (α * n)) ≤
        ∑ n ∈ range (N + 1),
          approximateResidueWeight cap q ((a * n) % q) :=
      sum_le_sum hpoint
    _ = ∑ n ∈ range (N + 1),
          approximateResidueWeight cap q ((a * (n % q)) % q) := by
      apply sum_congr rfl
      intro n hn
      simp only [Nat.mul_mod, Nat.mod_mod]
    _ ≤ (((N + 1) / q + 1 : ℕ) : ℝ) *
          ∑ r ∈ range q,
            approximateResidueWeight cap q ((a * r) % q) := by
      exact sum_range_mod_le_next_blocks
        (fun r ↦ approximateResidueWeight cap q ((a * r) % q)) q (N + 1)
        (Nat.pos_of_ne_zero (NeZero.ne q))
        (fun r ↦ approximateResidueWeight_nonneg hcap q ((a * r) % q))
    _ = (((N + 1) / q + 1 : ℕ) : ℝ) *
          ∑ r : Fin q, approximateResidueWeight cap q ((a * r.val) % q) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply congrArg (((((N + 1) / q + 1 : ℕ) : ℝ)) * ·)
      apply sum_congr rfl
      intro r hr
      rw [dif_pos (mem_range.mp hr)]
    _ ≤ (((N + 1) / q + 1 : ℕ) : ℝ) *
          (cap + 4 * q * harmonicBefore q) := by
      exact mul_le_mul_of_nonneg_left
        (sum_approximateResidueWeight_coprime_le cap a q ha hcap)
        (Nat.cast_nonneg _)

lemma harmonicBefore_le_one_add_log (q : ℕ) :
    harmonicBefore q ≤ 1 + Real.log q := by
  calc
    harmonicBefore q = ∑ k ∈ Ico 1 q, (k : ℝ)⁻¹ := rfl
    _ ≤ ∑ k ∈ Icc 1 q, (k : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Ico, mem_Icc] at hk ⊢
        exact ⟨hk.1, hk.2.le⟩
      · intro k hk hki
        positivity
    _ = (harmonic q : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log q := harmonic_le_one_add_log q

/-- The same finite estimate with the harmonic sum replaced by its elementary
logarithmic upper bound. -/
theorem cappedInvDist_prefix_bound_log
    (α ε cap : ℝ) (a q N : ℕ) [NeZero q]
    (ha : a.Coprime q) (hcap : 0 ≤ cap)
    (hε : |α - (a : ℝ) / q| ≤ ε) (hε0 : 0 ≤ ε)
    (hdrift : (N : ℝ) * ε ≤ 1 / (2 * q)) :
    (∑ n ∈ range (N + 1), cappedInvDist cap (α * n)) ≤
      (((N + 1) / q + 1 : ℕ) : ℝ) *
        (cap + 4 * q * (1 + Real.log q)) := by
  refine (cappedInvDist_prefix_bound α ε cap a q N ha hcap hε hε0 hdrift).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  gcongr
  exact harmonicBefore_le_one_add_log q

/-- The form used for the prime fourth moment.  The interval `0,…,4P` covers
all absolute values of differences of four primes at most `2P`.  Constants
are kept explicit; no asymptotic notation or limiting assertion is used. -/
theorem cappedInvDist_four_mul_le_minor_arc
    (H W P q a : ℕ) (α : ℝ)
    (hW : 3 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    (∑ n ∈ range (4 * P + 1),
        cappedInvDist ((H : ℝ) / P) (α * n)) ≤
      100 * Real.log H * ((H : ℝ) / W) := by
  have hWpos : 0 < W := by omega
  have hqpos : 0 < q := lt_of_lt_of_le hWpos hWq
  have hWpow : W ≤ W ^ 200 := Nat.le_pow (by norm_num)
  have hWP : W ≤ P := hWpow.trans hPlo
  have hPpos : 0 < P := lt_of_lt_of_le hWpos hWP
  have hPH : P ≤ H := hPhi.trans (Nat.div_le_self H (W ^ 3))
  have hHpos : 0 < H := lt_of_lt_of_le hPpos hPH
  have hqH' : q ≤ H := hqH.trans (Nat.div_le_self H W)
  have hqWmul : q * W ≤ H := (Nat.le_div_iff_mul_le hWpos).mp hqH
  have hW3pos : 0 < W ^ 3 := pow_pos hWpos 3
  have hPW3 : P * W ^ 3 ≤ H := (Nat.le_div_iff_mul_le hW3pos).mp hPhi
  have hWleW3 : W ≤ W ^ 3 := Nat.le_pow (by norm_num)
  have hPW : P * W ≤ H :=
    (Nat.mul_le_mul_left P hWleW3).trans hPW3
  have hWsq : 8 ≤ W ^ 2 := by nlinarith
  have h8PW : 8 * P * W ≤ H := by
    calc
      8 * P * W = 8 * (P * W) := by ring
      _ ≤ W ^ 2 * (P * W) := Nat.mul_le_mul_right (P * W) hWsq
      _ = P * W ^ 3 := by ring
      _ ≤ H := hPW3
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hcore :
      (((4 * P : ℕ) : ℝ) * (W : ℝ)) / (H : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hHr]
    have h8PWr : ((8 * P * W : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h8PW
    push_cast at h8PWr ⊢
    nlinarith
  have hdrift :
      ((4 * P : ℕ) : ℝ) * ((W : ℝ) / ((H : ℝ) * q)) ≤
        1 / (2 * (q : ℝ)) := by
    calc
      ((4 * P : ℕ) : ℝ) * ((W : ℝ) / ((H : ℝ) * q)) =
          ((((4 * P : ℕ) : ℝ) * (W : ℝ)) / (H : ℝ)) / (q : ℝ) := by
        field_simp
        <;> ring
      _ ≤ (1 / 2) / (q : ℝ) := div_le_div_of_nonneg_right hcore hqr.le
      _ = 1 / (2 * (q : ℝ)) := by ring
  have hraw := cappedInvDist_prefix_bound_log
    α ((W : ℝ) / ((H : ℝ) * q)) ((H : ℝ) / P) a q (4 * P)
    ha (by positivity) hα (by positivity) hdrift
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hinvq : (1 : ℝ) / (q : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hqr).2
    simpa using hqone
  have hblocks :
      ((((4 * P + 1) / q + 1 : ℕ) : ℝ)) ≤
        4 * (P : ℝ) / q + 2 := by
    have hdiv : ((((4 * P + 1) / q : ℕ) : ℝ)) ≤
        ((4 * P + 1 : ℕ) : ℝ) / (q : ℝ) := Nat.cast_div_le
    calc
      ((((4 * P + 1) / q + 1 : ℕ) : ℝ)) =
          ((((4 * P + 1) / q : ℕ) : ℝ)) + 1 := by push_cast; ring
      _ ≤ ((4 * P + 1 : ℕ) : ℝ) / (q : ℝ) + 1 := by linarith
      _ = 4 * (P : ℝ) / q + 1 / q + 1 := by
        push_cast
        field_simp
        <;> ring
      _ ≤ 4 * (P : ℝ) / q + 2 := by linarith
  have hqT : (q : ℝ) ≤ (H : ℝ) / W := by
    apply (le_div_iff₀ hWr).2
    exact_mod_cast hqWmul
  have hPT : (P : ℝ) ≤ (H : ℝ) / W := by
    apply (le_div_iff₀ hWr).2
    exact_mod_cast hPW
  have hHq : (H : ℝ) / q ≤ (H : ℝ) / W := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg H) hWr (by exact_mod_cast hWq)
  have hHP : (H : ℝ) / P ≤ (H : ℝ) / W := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg H) hWr (by exact_mod_cast hWP)
  have hlogq : Real.log q ≤ Real.log H :=
    Real.log_le_log hqr (by exact_mod_cast hqH')
  have hlogH0 : 0 ≤ Real.log H :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hHpos)))
  have hlogq0 : 0 ≤ Real.log q :=
    Real.log_nonneg hqone
  have hlogTwo : Real.log 2 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ H by omega))
  have hone_log : (1 : ℝ) ≤ 2 * Real.log H := by
    have htwo := Real.log_two_gt_d9
    linarith
  have hL : 1 + Real.log q ≤ 3 * Real.log H := by
    linarith
  have hT0 : 0 ≤ (H : ℝ) / W := by positivity
  have hL0 : 0 ≤ 1 + Real.log q := by positivity
  have hblock0 :
      0 ≤ (H : ℝ) / P + 4 * (q : ℝ) * (1 + Real.log q) := by positivity
  have hupper :
      (∑ n ∈ range (4 * P + 1),
          cappedInvDist ((H : ℝ) / P) (α * n)) ≤
        (4 * (P : ℝ) / q + 2) *
          ((H : ℝ) / P + 4 * (q : ℝ) * (1 + Real.log q)) := by
    exact hraw.trans (mul_le_mul_of_nonneg_right hblocks hblock0)
  have htermP :
      16 * (P : ℝ) * (1 + Real.log q) ≤
        48 * Real.log H * ((H : ℝ) / W) := by
    calc
      16 * (P : ℝ) * (1 + Real.log q) ≤
          16 * ((H : ℝ) / W) * (1 + Real.log q) := by
        gcongr
      _ ≤ 16 * ((H : ℝ) / W) * (3 * Real.log H) := by
        gcongr
      _ = 48 * Real.log H * ((H : ℝ) / W) := by ring
  have htermq :
      8 * (q : ℝ) * (1 + Real.log q) ≤
        24 * Real.log H * ((H : ℝ) / W) := by
    calc
      8 * (q : ℝ) * (1 + Real.log q) ≤
          8 * ((H : ℝ) / W) * (1 + Real.log q) := by
        gcongr
      _ ≤ 8 * ((H : ℝ) / W) * (3 * Real.log H) := by
        gcongr
      _ = 24 * Real.log H * ((H : ℝ) / W) := by ring
  have hTlog : (H : ℝ) / W ≤ 2 * Real.log H * ((H : ℝ) / W) := by
    nlinarith
  have hexpand :
      (4 * (P : ℝ) / q + 2) *
          ((H : ℝ) / P + 4 * (q : ℝ) * (1 + Real.log q)) =
        4 * ((H : ℝ) / q) +
          16 * (P : ℝ) * (1 + Real.log q) +
          2 * ((H : ℝ) / P) +
          8 * (q : ℝ) * (1 + Real.log q) := by
    field_simp
    <;> ring
  rw [hexpand] at hupper
  calc
    (∑ n ∈ range (4 * P + 1),
        cappedInvDist ((H : ℝ) / P) (α * n)) ≤
        4 * ((H : ℝ) / q) +
          16 * (P : ℝ) * (1 + Real.log q) +
          2 * ((H : ℝ) / P) +
          8 * (q : ℝ) * (1 + Real.log q) := hupper
    _ ≤ 6 * ((H : ℝ) / W) +
          72 * Real.log H * ((H : ℝ) / W) := by
      linarith
    _ ≤ 100 * Real.log H * ((H : ℝ) / W) := by
      linarith

/-- The sharp range needed for a difference of two sums of two primes from a
single dyadic interval.  Unlike the slightly stronger `4P` version above,
this statement is valid already from `W = 2`. -/
theorem cappedInvDist_two_mul_le_minor_arc
    (H W P q a : ℕ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    (∑ n ∈ range (2 * P + 1),
        cappedInvDist ((H : ℝ) / P) (α * n)) ≤
      100 * Real.log H * ((H : ℝ) / W) := by
  by_cases hWtwo : W = 2
  · subst W
    have hPpos : 0 < P := by
      have : 0 < 2 ^ 200 := pow_pos (by norm_num) 200
      omega
    have hPH : P ≤ H := hPhi.trans (Nat.div_le_self H (2 ^ 3))
    have hHpos : 0 < H := lt_of_lt_of_le hPpos hPH
    have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
    have hsumcap :
        (∑ n ∈ range (2 * P + 1),
            cappedInvDist ((H : ℝ) / P) (α * n)) ≤
          ∑ n ∈ range (2 * P + 1), (H : ℝ) / P := by
      apply sum_le_sum
      intro n hn
      exact cappedInvDist_le_cap _
    have hcount :
        ((2 * P + 1 : ℕ) : ℝ) * ((H : ℝ) / P) ≤ 3 * (H : ℝ) := by
      have hPone : (1 : ℝ) ≤ P := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hPpos))
      field_simp
      push_cast
      nlinarith [show (0 : ℝ) ≤ H from Nat.cast_nonneg H]
    have hlogTwo : Real.log 2 ≤ Real.log H :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ H by omega))
    have hlogLarge : (3 : ℝ) ≤ 50 * Real.log H := by
      have htwo := Real.log_two_gt_d9
      linarith
    calc
      (∑ n ∈ range (2 * P + 1),
          cappedInvDist ((H : ℝ) / P) (α * n)) ≤
          ∑ n ∈ range (2 * P + 1), (H : ℝ) / P := hsumcap
      _ = ((2 * P + 1 : ℕ) : ℝ) * ((H : ℝ) / P) := by simp
      _ ≤ 3 * (H : ℝ) := hcount
      _ ≤ 50 * Real.log H * (H : ℝ) := by
        exact mul_le_mul_of_nonneg_right hlogLarge (Nat.cast_nonneg H)
      _ = 100 * Real.log H * ((H : ℝ) / 2) := by ring
  · have hWthree : 3 ≤ W := by omega
    have hmajor := cappedInvDist_four_mul_le_minor_arc
      H W P q a α hWthree hWq hqH hPlo hPhi ha hα
    have hPpos : 0 < P := by
      have hWpos : 0 < W := by omega
      have hWpow : W ≤ W ^ 200 := Nat.le_pow (by norm_num)
      exact lt_of_lt_of_le hWpos (hWpow.trans hPlo)
    calc
      (∑ n ∈ range (2 * P + 1),
          cappedInvDist ((H : ℝ) / P) (α * n)) ≤
          ∑ n ∈ range (4 * P + 1),
            cappedInvDist ((H : ℝ) / P) (α * n) := by
        apply sum_le_sum_of_subset_of_nonneg
        · apply range_mono
          omega
        · intro n hn hnot
          exact cappedInvDist_nonneg (by positivity) _
      _ ≤ 100 * Real.log H * ((H : ℝ) / W) := hmajor

/-- Floor-safe variant matched to `exists_reducedRationalApproximation_shortInterval`.
The extra endpoint `H / W + 1` costs at most a factor two in the `q`-terms;
using the sharp `2P` difference range leaves the same numerical constant. -/
theorem cappedInvDist_two_mul_le_minor_arc_succ
    (H W P q a : ℕ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W + 1)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    (∑ n ∈ range (2 * P + 1),
        cappedInvDist ((H : ℝ) / P) (α * n)) ≤
      100 * Real.log H * ((H : ℝ) / W) := by
  have hWpos : 0 < W := by omega
  have hqpos : 0 < q := lt_of_lt_of_le hWpos hWq
  have hWpow : W ≤ W ^ 200 := Nat.le_pow (by norm_num)
  have hWP : W ≤ P := hWpow.trans hPlo
  have hPpos : 0 < P := lt_of_lt_of_le hWpos hWP
  have hPH : P ≤ H := hPhi.trans (Nat.div_le_self H (W ^ 3))
  have hHpos : 0 < H := lt_of_lt_of_le hPpos hPH
  have hWH : W ≤ H := hWP.trans hPH
  have hW3pos : 0 < W ^ 3 := pow_pos hWpos 3
  have hPW3 : P * W ^ 3 ≤ H :=
    (Nat.le_div_iff_mul_le hW3pos).mp hPhi
  have hWsq : 4 ≤ W ^ 2 := by nlinarith
  have h4PW : 4 * P * W ≤ H := by
    calc
      4 * P * W = 4 * (P * W) := by ring
      _ ≤ W ^ 2 * (P * W) := Nat.mul_le_mul_right (P * W) hWsq
      _ = P * W ^ 3 := by ring
      _ ≤ H := hPW3
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hcore :
      (((2 * P : ℕ) : ℝ) * (W : ℝ)) / (H : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hHr]
    have h4PWr : ((4 * P * W : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast h4PW
    push_cast at h4PWr ⊢
    nlinarith
  have hdrift :
      ((2 * P : ℕ) : ℝ) * ((W : ℝ) / ((H : ℝ) * q)) ≤
        1 / (2 * (q : ℝ)) := by
    calc
      ((2 * P : ℕ) : ℝ) * ((W : ℝ) / ((H : ℝ) * q)) =
          ((((2 * P : ℕ) : ℝ) * (W : ℝ)) / (H : ℝ)) /
            (q : ℝ) := by
        field_simp
        <;> ring
      _ ≤ (1 / 2) / (q : ℝ) :=
        div_le_div_of_nonneg_right hcore hqr.le
      _ = 1 / (2 * (q : ℝ)) := by ring
  have hraw := cappedInvDist_prefix_bound_log
    α ((W : ℝ) / ((H : ℝ) * q)) ((H : ℝ) / P) a q (2 * P)
    ha (by positivity) hα (by positivity) hdrift
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
  have hinvq : (1 : ℝ) / (q : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hqr).2
    simpa using hqone
  have hblocks :
      ((((2 * P + 1) / q + 1 : ℕ) : ℝ)) ≤
        2 * (P : ℝ) / q + 2 := by
    have hdiv : ((((2 * P + 1) / q : ℕ) : ℝ)) ≤
        ((2 * P + 1 : ℕ) : ℝ) / (q : ℝ) := Nat.cast_div_le
    calc
      ((((2 * P + 1) / q + 1 : ℕ) : ℝ)) =
          ((((2 * P + 1) / q : ℕ) : ℝ)) + 1 := by push_cast; ring
      _ ≤ ((2 * P + 1 : ℕ) : ℝ) / (q : ℝ) + 1 := by linarith
      _ = 2 * (P : ℝ) / q + 1 / q + 1 := by
        push_cast
        field_simp
        <;> ring
      _ ≤ 2 * (P : ℝ) / q + 2 := by linarith
  have hdivFloor : ((H / W : ℕ) : ℝ) ≤ (H : ℝ) / W :=
    Nat.cast_div_le
  have hTone : (1 : ℝ) ≤ (H : ℝ) / W := by
    apply (le_div_iff₀ hWr).2
    simpa using (show (W : ℝ) ≤ H by exact_mod_cast hWH)
  have hqT : (q : ℝ) ≤ 2 * ((H : ℝ) / W) := by
    have hqcast : (q : ℝ) ≤ (H / W + 1 : ℕ) := by
      exact_mod_cast hqH
    push_cast at hqcast
    calc
      (q : ℝ) ≤ (H / W : ℕ) + 1 := hqcast
      _ ≤ (H : ℝ) / W + 1 := by linarith
      _ ≤ 2 * ((H : ℝ) / W) := by linarith
  have hqH' : (q : ℝ) ≤ H := by
    calc
      (q : ℝ) ≤ 2 * ((H : ℝ) / W) := hqT
      _ ≤ H := by
        rw [show 2 * ((H : ℝ) / W) = (2 * H) / W by ring]
        apply (div_le_iff₀ hWr).2
        have hWtwo : (2 : ℝ) ≤ W := by exact_mod_cast hW
        nlinarith
  have hPW : P * W ≤ H := by
    have hWleW3 : W ≤ W ^ 3 := Nat.le_pow (by norm_num)
    exact (Nat.mul_le_mul_left P hWleW3).trans hPW3
  have hPT : (P : ℝ) ≤ (H : ℝ) / W := by
    apply (le_div_iff₀ hWr).2
    exact_mod_cast hPW
  have hHq : (H : ℝ) / q ≤ (H : ℝ) / W := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg H) hWr
      (by exact_mod_cast hWq)
  have hHP : (H : ℝ) / P ≤ (H : ℝ) / W := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg H) hWr
      (by exact_mod_cast hWP)
  have hlogq : Real.log q ≤ Real.log H :=
    Real.log_le_log hqr hqH'
  have hlogH0 : 0 ≤ Real.log H :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H by omega))
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hqone
  have hlogTwo : Real.log 2 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ H by omega))
  have hone_log : (1 : ℝ) ≤ 2 * Real.log H := by
    have htwo := Real.log_two_gt_d9
    linarith
  have hL : 1 + Real.log q ≤ 3 * Real.log H := by linarith
  have hblock0 :
      0 ≤ (H : ℝ) / P + 4 * (q : ℝ) * (1 + Real.log q) := by
    positivity
  have hupper :
      (∑ n ∈ range (2 * P + 1),
          cappedInvDist ((H : ℝ) / P) (α * n)) ≤
        (2 * (P : ℝ) / q + 2) *
          ((H : ℝ) / P + 4 * (q : ℝ) * (1 + Real.log q)) := by
    exact hraw.trans (mul_le_mul_of_nonneg_right hblocks hblock0)
  have htermP :
      8 * (P : ℝ) * (1 + Real.log q) ≤
        24 * Real.log H * ((H : ℝ) / W) := by
    calc
      8 * (P : ℝ) * (1 + Real.log q) ≤
          8 * ((H : ℝ) / W) * (1 + Real.log q) := by gcongr
      _ ≤ 8 * ((H : ℝ) / W) * (3 * Real.log H) := by gcongr
      _ = 24 * Real.log H * ((H : ℝ) / W) := by ring
  have htermq :
      8 * (q : ℝ) * (1 + Real.log q) ≤
        48 * Real.log H * ((H : ℝ) / W) := by
    calc
      8 * (q : ℝ) * (1 + Real.log q) ≤
          8 * (2 * ((H : ℝ) / W)) * (1 + Real.log q) := by gcongr
      _ ≤ 8 * (2 * ((H : ℝ) / W)) * (3 * Real.log H) := by gcongr
      _ = 48 * Real.log H * ((H : ℝ) / W) := by ring
  have hTlog : 4 * ((H : ℝ) / W) ≤
      8 * Real.log H * ((H : ℝ) / W) := by
    have hT : 0 ≤ (H : ℝ) / W := by positivity
    nlinarith
  have hexpand :
      (2 * (P : ℝ) / q + 2) *
          ((H : ℝ) / P + 4 * (q : ℝ) * (1 + Real.log q)) =
        2 * ((H : ℝ) / q) +
          8 * (P : ℝ) * (1 + Real.log q) +
          2 * ((H : ℝ) / P) +
          8 * (q : ℝ) * (1 + Real.log q) := by
    field_simp
    <;> ring
  rw [hexpand] at hupper
  calc
    (∑ n ∈ range (2 * P + 1),
        cappedInvDist ((H : ℝ) / P) (α * n)) ≤
      2 * ((H : ℝ) / q) +
        8 * (P : ℝ) * (1 + Real.log q) +
        2 * ((H : ℝ) / P) +
        8 * (q : ℝ) * (1 + Real.log q) := hupper
    _ ≤ 4 * ((H : ℝ) / W) +
        72 * Real.log H * ((H : ℝ) / W) := by linarith
    _ ≤ 100 * Real.log H * ((H : ℝ) / W) := by linarith

end

end Erdos67.MRTVinogradov
