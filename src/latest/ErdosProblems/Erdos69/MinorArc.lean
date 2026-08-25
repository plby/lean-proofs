import Mathlib
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Interval
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Finite minor-arc estimates

This file records the elementary Diophantine part of the minor-arc argument in
Tao--Teräväinen, Section 3.5.  Their fourth-moment expansion leads to sums of

`min (M / P) (1 / ‖α * n‖)`.

Here `‖x‖` denotes distance to the nearest integer.  At an integer the usual
geometric-sum estimate is the interval length, rather than Lean's value of
`0⁻¹`; `cappedInvDist` therefore treats distance zero separately.

The main estimates below are deliberately finite.  In particular, multiplication
by a numerator coprime to `q` merely permutes the `q` rational phases, and one
complete block costs at most the cap plus twice `q` times a harmonic sum.
-/

open scoped BigOperators
open Finset

namespace Erdos69.MinorArc

noncomputable section

/-- Distance of a real number to its nearest integer. -/
def nearestIntDist (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- The reciprocal nearest-integer distance, capped by `cap`.

At distance zero this is defined to be `cap`, as required by the geometric
sum estimate. -/
def cappedInvDist (cap x : ℝ) : ℝ :=
  if nearestIntDist x = 0 then cap else min cap (nearestIntDist x)⁻¹

lemma nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x := abs_nonneg _

lemma nearestIntDist_le_half (x : ℝ) : nearestIntDist x ≤ 1 / 2 := by
  simpa [nearestIntDist] using (abs_sub_round x)

@[simp] lemma nearestIntDist_intCast (z : ℤ) : nearestIntDist (z : ℝ) = 0 := by
  simp [nearestIntDist]

lemma nearestIntDist_add_intCast (x : ℝ) (z : ℤ) :
    nearestIntDist (x + z) = nearestIntDist x := by
  rw [nearestIntDist, nearestIntDist, round_add_intCast]
  push_cast
  ring_nf

/-- Distance to the nearest integer is `1`-Lipschitz. -/
lemma nearestIntDist_le_add_abs_sub (x y : ℝ) :
    nearestIntDist x ≤ nearestIntDist y + |x - y| := by
  have hround : |x - (round x : ℝ)| ≤ |x - (round y : ℝ)| := round_le x (round y)
  have htri : |x - (round y : ℝ)| ≤ |x - y| + |y - (round y : ℝ)| := by
    calc
      |x - (round y : ℝ)| = |(x - y) + (y - (round y : ℝ))| := by ring_nf
      _ ≤ |x - y| + |y - (round y : ℝ)| := abs_add_le _ _
  unfold nearestIntDist
  linarith

lemma nearestIntDist_sub_abs_sub_le (x y : ℝ) :
    nearestIntDist y - |x - y| ≤ nearestIntDist x := by
  have := nearestIntDist_le_add_abs_sub y x
  rw [abs_sub_comm] at this
  linarith

lemma nearestIntDist_neg (x : ℝ) : nearestIntDist (-x) = nearestIntDist x := by
  unfold nearestIntDist
  apply le_antisymm
  · calc
      |-x - (round (-x) : ℝ)| ≤ |-x - (-round x : ℤ)| := round_le (-x) (-round x)
      _ = |x - (round x : ℝ)| := by
        push_cast
        rw [show -x - -(round x : ℝ) = -(x - (round x : ℝ)) by ring, abs_neg]
  · calc
      |x - (round x : ℝ)| ≤ |x - (-round (-x) : ℤ)| := round_le x (-round (-x))
      _ = |-x - (round (-x) : ℝ)| := by
        push_cast
        rw [show x - -(round (-x) : ℝ) = -(-x - (round (-x) : ℝ)) by ring, abs_neg]

lemma cappedInvDist_nonneg {cap : ℝ} (hcap : 0 ≤ cap) (x : ℝ) :
    0 ≤ cappedInvDist cap x := by
  simp only [cappedInvDist]
  split_ifs
  · exact hcap
  · exact le_min hcap (inv_nonneg.mpr (nearestIntDist_nonneg x))

lemma cappedInvDist_le_cap {cap : ℝ} (x : ℝ) : cappedInvDist cap x ≤ cap := by
  simp only [cappedInvDist]
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma cappedInvDist_add_intCast (cap x : ℝ) (z : ℤ) :
    cappedInvDist cap (x + z) = cappedInvDist cap x := by
  simp [cappedInvDist, nearestIntDist_add_intCast]

lemma cappedInvDist_neg (cap x : ℝ) : cappedInvDist cap (-x) = cappedInvDist cap x := by
  simp [cappedInvDist, nearestIntDist_neg]

/-- The distance formula for a rational phase. -/
lemma nearestIntDist_nat_div (m q : ℕ) :
    nearestIntDist ((m : ℝ) / q) =
      (min (m % q) (q - m % q) : ℕ) / (q : ℝ) := by
  simpa [nearestIntDist] using
    (abs_sub_round_div_natCast_eq (α := ℝ) (m := m) (n := q))

/-- Multiplication by a numerator coprime to `q`, viewed as a permutation of
the standard representatives `Fin q`. -/
noncomputable def coprimeResiduePerm (a q : ℕ) [NeZero q] (ha : a.Coprime q) :
    Equiv.Perm (Fin q) :=
  (ZMod.finEquiv q).toEquiv.trans <|
    (ZMod.unitOfCoprime a ha).mulLeft.trans (ZMod.finEquiv q).symm.toEquiv

lemma coprimeResiduePerm_val (a q : ℕ) [NeZero q] (ha : a.Coprime q) (n : Fin q) :
    (coprimeResiduePerm a q ha n).val = (a * n.val) % q := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      change
        ((⟨a % (q + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (q + 1)) * n).val =
          (a * n.val) % (q + 1)
      simp [Fin.val_mul, Nat.mul_mod]

/-- The weight attached to a standard residue modulo `q`. -/
def residueWeight (cap : ℝ) (q r : ℕ) : ℝ :=
  if r = 0 then cap else min cap ((q : ℝ) / min r (q - r))

/-- Residue majorant stable under an error of at most `1 / (2q)` in phase.
The factor two is the loss from perturbing an exact rational phase. -/
def approximateResidueWeight (cap : ℝ) (q r : ℕ) : ℝ :=
  if r = 0 then cap else 2 * (q : ℝ) / min r (q - r)

lemma cappedInvDist_rational_eq_residueWeight
    (cap : ℝ) (a q : ℕ) [NeZero q] (n : Fin q) :
    cappedInvDist cap (((a * n.val : ℕ) : ℝ) / q) =
      residueWeight cap q ((a * n.val) % q) := by
  rw [cappedInvDist, nearestIntDist_nat_div]
  unfold residueWeight
  by_cases hr : (a * n.val) % q = 0
  · simp [hr]
  · rw [if_neg hr]
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    have hdNat : min ((a * n.val) % q) (q - (a * n.val) % q) ≠ 0 := by
      have hsub : q - (a * n.val) % q ≠ 0 :=
        Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))))
      omega
    have hd : ((min ((a * n.val) % q) (q - (a * n.val) % q) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hdNat
    have hdist :
        ((min ((a * n.val) % q) (q - (a * n.val) % q) : ℕ) : ℝ) / q ≠ 0 :=
      div_ne_zero hd hq
    rw [if_neg hdist, inv_div]

/-- Multiplying a frequency approximation by an index multiplies its error by
that index. -/
lemma abs_phase_sub_rational_phase (α : ℝ) (a q n : ℕ) :
    |α * n - ((a * n : ℕ) : ℝ) / q| =
      (n : ℝ) * |α - (a : ℝ) / q| := by
  rw [Nat.cast_mul]
  have h : α * (n : ℝ) - (a : ℝ) * n / q = (n : ℝ) * (α - (a : ℝ) / q) := by ring
  rw [h, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]

lemma nearestIntDist_mul_lower_of_approx
    (α ε : ℝ) (a q n N : ℕ) (hn : n ≤ N)
    (hε : |α - (a : ℝ) / q| ≤ ε) (hε0 : 0 ≤ ε) :
    nearestIntDist (((a * n : ℕ) : ℝ) / q) - (N : ℝ) * ε ≤
      nearestIntDist (α * n) := by
  have hlip := nearestIntDist_sub_abs_sub_le (α * n) (((a * n : ℕ) : ℝ) / q)
  rw [abs_phase_sub_rational_phase] at hlip
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul : (n : ℝ) * |α - (a : ℝ) / q| ≤ (N : ℝ) * ε :=
    mul_le_mul hnR hε (abs_nonneg _) (Nat.cast_nonneg N)
  linarith

/-- Pointwise Diophantine estimate underlying the minor-arc sum.  If the total
phase drift on the index range is at most `1/(2q)`, every nonzero rational
residue retains at least half of its exact distance from the integers. -/
lemma cappedInvDist_mul_le_approximateResidueWeight
    (α ε cap : ℝ) (a q n N : ℕ) [NeZero q]
    (hn : n ≤ N) (hε : |α - (a : ℝ) / q| ≤ ε) (hε0 : 0 ≤ ε)
    (hdrift : (N : ℝ) * ε ≤ 1 / (2 * q)) :
    cappedInvDist cap (α * n) ≤ approximateResidueWeight cap q ((a * n) % q) := by
  let r := (a * n) % q
  let d := min r (q - r)
  change cappedInvDist cap (α * n) ≤ approximateResidueWeight cap q r
  by_cases hr : r = 0
  · rw [approximateResidueWeight, if_pos hr]
    exact cappedInvDist_le_cap _
  · have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hrlt : r < q := Nat.mod_lt _ hqpos
    have hsub : q - r ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hrlt)
    have hdNat : d ≠ 0 := by
      dsimp [d]
      omega
    have hdNatPos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hdNat
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hdR : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hdNat)
    have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast hdNatPos
    have hrat : nearestIntDist (((a * n : ℕ) : ℝ) / q) = (d : ℝ) / q := by
      rw [nearestIntDist_nat_div]
    have hhalf : 1 / (2 * (q : ℝ)) ≤ (d : ℝ) / (2 * q) := by
      rw [div_le_div_iff_of_pos_right (mul_pos two_pos hqR)]
      exact hd_one
    have hlower : (d : ℝ) / (2 * q) ≤ nearestIntDist (α * n) := by
      have hbase := nearestIntDist_mul_lower_of_approx α ε a q n N hn hε hε0
      rw [hrat] at hbase
      have : (N : ℝ) * ε ≤ (d : ℝ) / (2 * q) := hdrift.trans hhalf
      have hsplit : (d : ℝ) / q - (d : ℝ) / (2 * q) = (d : ℝ) / (2 * q) := by
        field_simp
        ring
      linarith
    have hdistPos : 0 < nearestIntDist (α * n) :=
      lt_of_lt_of_le (div_pos hdR (mul_pos two_pos hqR)) hlower
    rw [cappedInvDist, if_neg hdistPos.ne']
    refine (min_le_right _ _).trans ?_
    have hinv :=
      (inv_le_inv₀ hdistPos (div_pos hdR (mul_pos two_pos hqR))).2 hlower
    rw [inv_div] at hinv
    simpa [approximateResidueWeight, hr, r, d, div_eq_mul_inv, mul_assoc] using hinv

/-- A coprime numerator does not affect a complete block of rational phases. -/
lemma sum_cappedInvDist_rational_block_eq
    (cap : ℝ) (a q : ℕ) [NeZero q] (ha : a.Coprime q) :
    (∑ n : Fin q, cappedInvDist cap (((a * n.val : ℕ) : ℝ) / q)) =
      ∑ r : Fin q, residueWeight cap q r.val := by
  simp_rw [cappedInvDist_rational_eq_residueWeight]
  rw [← Equiv.sum_comp (coprimeResiduePerm a q ha) (fun r : Fin q ↦ residueWeight cap q r.val)]
  apply Fintype.sum_congr
  intro n
  rw [coprimeResiduePerm_val]

/-- The finite harmonic sum `1 + 1/2 + ... + 1/(q-1)`. -/
def harmonicBefore (q : ℕ) : ℝ := ∑ k ∈ Ico 1 q, (k : ℝ)⁻¹

lemma harmonicBefore_nonneg (q : ℕ) : 0 ≤ harmonicBefore q := by
  exact sum_nonneg fun k _ ↦ inv_nonneg.mpr (Nat.cast_nonneg k)

lemma harmonicBefore_le_harmonic (q : ℕ) :
    harmonicBefore q ≤ (harmonic q : ℝ) := by
  simp only [harmonicBefore, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [mem_Ico, mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.le⟩
  · intro x _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg x)

theorem harmonicBefore_le_one_add_log (q : ℕ) :
    harmonicBefore q ≤ 1 + Real.log q :=
  (harmonicBefore_le_harmonic q).trans (harmonic_le_one_add_log q)

lemma residueWeight_nonneg {cap : ℝ} (hcap : 0 ≤ cap) (q r : ℕ) :
    0 ≤ residueWeight cap q r := by
  unfold residueWeight
  split_ifs
  · exact hcap
  · exact le_min hcap (div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg _))

lemma residueWeight_le_cap (cap : ℝ) (q r : ℕ) : residueWeight cap q r ≤ cap := by
  simp only [residueWeight]
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma residueWeight_le_two_reciprocals
    {cap : ℝ} {q r : ℕ} (hr : r ∈ Ico 1 q) (hcap : 0 ≤ cap) :
    residueWeight cap q r ≤ (q : ℝ) * ((r : ℝ)⁻¹ + ((q - r : ℕ) : ℝ)⁻¹) := by
  have hr0 : r ≠ 0 := Nat.ne_of_gt (mem_Ico.mp hr).1
  have hrq : r < q := (mem_Ico.mp hr).2
  have hqr0 : q - r ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hrq)
  rw [residueWeight, if_neg hr0]
  refine (min_le_right _ _).trans ?_
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  rw [Nat.cast_min, min_def]
  split_ifs
  · exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact le_add_of_nonneg_left (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma approximateResidueWeight_le_two_reciprocals
    {cap : ℝ} {q r : ℕ} (hr : r ∈ Ico 1 q) :
    approximateResidueWeight cap q r ≤
      2 * (q : ℝ) * ((r : ℝ)⁻¹ + ((q - r : ℕ) : ℝ)⁻¹) := by
  have hr0 : r ≠ 0 := Nat.ne_of_gt (mem_Ico.mp hr).1
  rw [approximateResidueWeight, if_neg hr0, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (Nat.cast_nonneg q))
  rw [Nat.cast_min, min_def]
  split_ifs
  · exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact le_add_of_nonneg_left (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma sum_approximateResidueWeight_le_harmonic
    (cap : ℝ) (q : ℕ) [NeZero q] :
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
  rw [show approximateResidueWeight cap q 0 = cap by simp [approximateResidueWeight]]
  have hdiff : range q \ {0} = Ico 1 q := by
    ext x
    simp only [mem_sdiff, mem_range, mem_singleton, mem_Ico]
    omega
  rw [hdiff]
  have hrest :
      (∑ x ∈ Ico 1 q, approximateResidueWeight cap q x) ≤
        ∑ x ∈ Ico 1 q,
          2 * (q : ℝ) * ((x : ℝ)⁻¹ + ((q - x : ℕ) : ℝ)⁻¹) := by
    exact sum_le_sum fun _ hx ↦ approximateResidueWeight_le_two_reciprocals hx
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
    (2 * (q : ℝ)) * harmonicBefore q + (2 * (q : ℝ)) * harmonicBefore q + cap =
      cap + 4 * (q : ℝ) * harmonicBefore q
  ring

lemma sum_approximateResidueWeight_coprime_eq
    (cap : ℝ) (a q : ℕ) [NeZero q] (ha : a.Coprime q) :
    (∑ n : Fin q, approximateResidueWeight cap q ((a * n.val) % q)) =
      ∑ r : Fin q, approximateResidueWeight cap q r.val := by
  rw [← Equiv.sum_comp (coprimeResiduePerm a q ha)
    (fun r : Fin q ↦ approximateResidueWeight cap q r.val)]
  apply Fintype.sum_congr
  intro n
  rw [coprimeResiduePerm_val]

/-- Quantitative one-block rational-approximation estimate. -/
theorem approximate_rational_block_bound
    (α ε cap : ℝ) (a q : ℕ) [NeZero q] (ha : a.Coprime q)
    (hε : |α - (a : ℝ) / q| ≤ ε) (hε0 : 0 ≤ ε)
    (hdrift : (q : ℝ) * ε ≤ 1 / (2 * q)) :
    (∑ n : Fin q, cappedInvDist cap (α * n.val)) ≤
      cap + 4 * q * harmonicBefore q := by
  calc
    (∑ n : Fin q, cappedInvDist cap (α * n.val)) ≤
        ∑ n : Fin q, approximateResidueWeight cap q ((a * n.val) % q) := by
      exact Finset.sum_le_sum fun n _ ↦
        cappedInvDist_mul_le_approximateResidueWeight α ε cap a q n.val q n.isLt.le
          hε hε0 hdrift
    _ = ∑ r : Fin q, approximateResidueWeight cap q r.val :=
      sum_approximateResidueWeight_coprime_eq cap a q ha
    _ ≤ cap + 4 * q * harmonicBefore q :=
      sum_approximateResidueWeight_le_harmonic cap q

/-- Decompose a finite sum into residue-class fibers. -/
lemma sum_eq_sum_mod_fibers (q : ℕ) (hq : 0 < q) (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ s, f n) =
      ∑ r ∈ range q, ∑ n ∈ s.filter (fun n ↦ n % q = r), f n := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  have hnmod : n % q ∈ range q := mem_range.mpr (Nat.mod_lt n hq)
  rw [sum_eq_single (n % q)]
  · simp
  · intro r hr hrne
    simp [hrne.symm]
  · exact fun hnot ↦ (hnot hnmod).elim

/-- At most `N / q + 1` numbers in `[0,N]` lie in one residue class modulo
`q`. -/
lemma card_filter_mod_eq_range_le (q N r : ℕ) (hq : 0 < q) :
    #(range (N + 1) |>.filter fun n ↦ n % q = r) ≤ N / q + 1 := by
  have hle := card_le_card_of_injOn
    (s := range (N + 1) |>.filter fun n ↦ n % q = r)
    (t := range (N / q + 1)) (fun n ↦ n / q)
    (by
      intro n hn
      change n ∈ (range (N + 1) |>.filter fun n ↦ n % q = r) at hn
      simp only [mem_filter, mem_range] at hn
      apply mem_range.mpr
      apply Nat.lt_succ_of_le
      exact Nat.div_le_div_right (Nat.lt_succ_iff.mp hn.1))
    (by
      intro x hx y hy hdiv
      change x ∈ (range (N + 1) |>.filter fun n ↦ n % q = r) at hx
      change y ∈ (range (N + 1) |>.filter fun n ↦ n % q = r) at hy
      simp only [mem_filter] at hx hy
      change x / q = y / q at hdiv
      calc
        x = x % q + q * (x / q) := (Nat.mod_add_div x q).symm
        _ = y % q + q * (y / q) := by rw [hx.2, hy.2, hdiv]
        _ = y := Nat.mod_add_div y q)
  simpa using hle

/-- Summation lemma for a nonnegative majorant depending only on a residue
class. -/
lemma sum_le_mul_sum_mod_of_fiber_card_le
    (q B : ℕ) (hq : 0 < q) (s : Finset ℕ) (f g : ℕ → ℝ)
    (hg : ∀ r ∈ range q, 0 ≤ g r)
    (hfg : ∀ n ∈ s, f n ≤ g (n % q))
    (hcard : ∀ r ∈ range q, #(s.filter fun n ↦ n % q = r) ≤ B) :
    (∑ n ∈ s, f n) ≤ (B : ℝ) * ∑ r ∈ range q, g r := by
  rw [sum_eq_sum_mod_fibers q hq s f]
  calc
    (∑ r ∈ range q, ∑ n ∈ s.filter (fun n ↦ n % q = r), f n) ≤
        ∑ r ∈ range q, (B : ℝ) * g r := by
      apply sum_le_sum
      intro r hr
      calc
        (∑ n ∈ s.filter (fun n ↦ n % q = r), f n) ≤
            ∑ _n ∈ s.filter (fun n ↦ n % q = r), g r := by
          apply sum_le_sum
          intro n hn
          have hns : n ∈ s := (mem_filter.mp hn).1
          have hnmod : n % q = r := (mem_filter.mp hn).2
          simpa [hnmod] using hfg n hns
        _ = (#(s.filter fun n ↦ n % q = r) : ℝ) * g r := by simp
        _ ≤ (B : ℝ) * g r := by
          apply mul_le_mul_of_nonneg_right _ (hg r hr)
          exact_mod_cast hcard r hr
    _ = (B : ℝ) * ∑ r ∈ range q, g r := by rw [mul_sum]

/-- Finite Iwaniec--Kowalski rational-approximation bound on `[0,N]`.

The quotient `N / q + 1` counts the possible complete residue blocks.  This is
the finite estimate inserted after Dirichlet approximation in the TT minor-arc
argument. -/
theorem approximate_rational_range_bound
    (α ε cap : ℝ) (a q N : ℕ) [NeZero q] (ha : a.Coprime q)
    (hε : |α - (a : ℝ) / q| ≤ ε) (hε0 : 0 ≤ ε) (hcap : 0 ≤ cap)
    (hdrift : (N : ℝ) * ε ≤ 1 / (2 * q)) :
    (∑ n ∈ range (N + 1), cappedInvDist cap (α * n)) ≤
      (N / q + 1 : ℕ) * (cap + 4 * q * harmonicBefore q) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    (∑ n ∈ range (N + 1), cappedInvDist cap (α * n)) ≤
        ((N / q + 1 : ℕ) : ℝ) *
          ∑ r ∈ range q, approximateResidueWeight cap q ((a * r) % q) := by
      apply sum_le_mul_sum_mod_of_fiber_card_le q (N / q + 1) hq
      · intro r _
        unfold approximateResidueWeight
        split_ifs
        · exact hcap
        · exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg q))
            (Nat.cast_nonneg _)
      · intro n hn
        have hpoint := cappedInvDist_mul_le_approximateResidueWeight α ε cap a q n N
          (Nat.lt_succ_iff.mp (mem_range.mp hn)) hε hε0 hdrift
        simpa [Nat.mul_mod] using hpoint
      · intro r _
        exact card_filter_mod_eq_range_le q N r hq
    _ ≤ ((N / q + 1 : ℕ) : ℝ) * (cap + 4 * q * harmonicBefore q) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hfin :
          (∑ r ∈ range q, approximateResidueWeight cap q ((a * r) % q)) =
            ∑ r : Fin q, approximateResidueWeight cap q ((a * r.val) % q) := by
        rw [Finset.sum_fin_eq_sum_range]
        symm
        apply sum_congr rfl
        intro r hr
        rw [dif_pos (mem_range.mp hr)]
      rw [hfin, sum_approximateResidueWeight_coprime_eq cap a q ha]
      exact sum_approximateResidueWeight_le_harmonic cap q
    _ = (N / q + 1 : ℕ) * (cap + 4 * q * harmonicBefore q) := by
      norm_cast

/-- The specialization with the scales appearing in TT Section 3.5.  The
condition `8P ≤ Q` guarantees that the Dirichlet-approximation error remains
below half the spacing of rational phases throughout `0 ≤ n ≤ 4P`. -/
theorem tt_minor_arc_positive_sum_bound
    (α : ℝ) (M P Q a q : ℕ) [NeZero q] (ha : a.Coprime q)
    (hP : 0 < P) (hQ : 0 < Q) (hscale : 8 * P ≤ Q)
    (happrox : |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q)) :
    (∑ n ∈ range (4 * P + 1), cappedInvDist ((M : ℝ) / P) (α * n)) ≤
      (4 * P / q + 1 : ℕ) *
        ((M : ℝ) / P + 4 * q * harmonicBefore q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hscaleR : (8 : ℝ) * P ≤ Q := by exact_mod_cast hscale
  have hdrift :
      ((4 * P : ℕ) : ℝ) * (1 / ((q : ℝ) * Q)) ≤ 1 / (2 * q) := by
    have hfour : (4 : ℝ) * P / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ hQR]
      nlinarith
    calc
      ((4 * P : ℕ) : ℝ) * (1 / ((q : ℝ) * Q)) = ((4 : ℝ) * P / Q) / q := by
        push_cast
        field_simp
      _ ≤ ((1 : ℝ) / 2) / q := (div_le_div_iff_of_pos_right hqR).2 hfour
      _ = 1 / (2 * q) := by field_simp
  apply approximate_rational_range_bound α (1 / ((q : ℝ) * Q)) ((M : ℝ) / P)
    a q (4 * P) ha happrox
  · exact one_div_nonneg.mpr (mul_nonneg hqR.le hQR.le)
  · exact div_nonneg (Nat.cast_nonneg M) hPR.le
  · exact hdrift

lemma sum_residueWeight_le_harmonic
    (cap : ℝ) (q : ℕ) [NeZero q] (hcap : 0 ≤ cap) :
    (∑ r : Fin q, residueWeight cap q r.val) ≤
      cap + 2 * q * harmonicBefore q := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hfin :
      (∑ r : Fin q, residueWeight cap q r.val) =
        ∑ r ∈ range q, residueWeight cap q r := by
    rw [Finset.sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro r hr
    rw [dif_pos (mem_range.mp hr)]
  rw [hfin]
  rw [sum_eq_add_sum_sdiff_singleton_of_mem (mem_range.mpr hqpos)]
  rw [show residueWeight cap q 0 = cap by simp [residueWeight]]
  have hdiff : range q \ {0} = Ico 1 q := by
    ext x
    simp only [mem_sdiff, mem_range, mem_singleton, mem_Ico]
    omega
  rw [hdiff]
  have hrest :
      (∑ x ∈ Ico 1 q, residueWeight cap q x) ≤
        ∑ x ∈ Ico 1 q, (q : ℝ) * ((x : ℝ)⁻¹ + ((q - x : ℕ) : ℝ)⁻¹) := by
    exact sum_le_sum fun x hx ↦ residueWeight_le_two_reciprocals hx hcap
  rw [add_comm cap (∑ x ∈ Ico 1 q, residueWeight cap q x)]
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
    (q : ℝ) * harmonicBefore q + (q : ℝ) * harmonicBefore q + cap =
      cap + 2 * (q : ℝ) * harmonicBefore q
  ring

/-- Complete rational block estimate: a coprime rational phase costs a cap at
the zero residue, plus two harmonic tails. -/
theorem rational_block_bound
    (cap : ℝ) (a q : ℕ) [NeZero q] (ha : a.Coprime q) (hcap : 0 ≤ cap) :
    (∑ n : Fin q, cappedInvDist cap (((a * n.val : ℕ) : ℝ) / q)) ≤
      cap + 2 * q * harmonicBefore q := by
  rw [sum_cappedInvDist_rational_block_eq cap a q ha]
  exact sum_residueWeight_le_harmonic cap q hcap

end

end Erdos69.MinorArc
