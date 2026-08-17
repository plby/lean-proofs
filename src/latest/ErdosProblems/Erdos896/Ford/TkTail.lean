/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.PrimeBins
import ErdosProblems.Erdos896.Ford.Measure
import ErdosProblems.Erdos896.Ford.PrimeEstimates
import ErdosProblems.Erdos896.Ford.StirlingScale

/-!
# The large-`k` tail of Ford's `T_k`

The prime-bin argument controls `T_k` up to `k = 10v`.  Beyond that point
the elementary estimate `L(a) ≤ 2^k log 2`, together with the usual bound
for an elementary symmetric function, gives a rapidly convergent factorial
tail.  This file packages that complementary estimate.
-/

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators

private noncomputable def elementaryMass {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard k, ∏ x ∈ t, w x

private lemma elementaryMass_succ_identity {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (k : ℕ) :
    (k + 1 : ℝ) * elementaryMass s w (k + 1) =
      ∑ t ∈ s.powersetCard k,
        (∏ x ∈ t, w x) * (∑ x ∈ s \ t, w x) := by
  classical
  let source := ((s.powersetCard k).product s).filter fun z ↦ z.2 ∉ z.1
  let target := ((s.powersetCard (k + 1)).product s).filter fun z ↦ z.2 ∈ z.1
  have hbij :
      (∑ z ∈ source, (∏ x ∈ z.1, w x) * w z.2) =
        ∑ z ∈ target, ∏ x ∈ z.1, w x := by
    refine Finset.sum_bij'
      (fun z _ ↦ (insert z.2 z.1, z.2))
      (fun z _ ↦ (z.1.erase z.2, z.2)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨t, x⟩ htx
      simp only [source, Finset.mem_filter] at htx
      obtain ⟨ht, hx⟩ := Finset.mem_product.mp htx.1
      have hxt := htx.2
      have ht' := Finset.mem_powersetCard.mp ht
      simp only [target, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset hx ht'.1, ?_⟩, hx⟩, Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hxt, ht'.2]
    · rintro ⟨u, x⟩ hux
      simp only [target, Finset.mem_filter] at hux
      obtain ⟨hu, hx⟩ := Finset.mem_product.mp hux.1
      have hxu := hux.2
      have hu' := Finset.mem_powersetCard.mp hu
      simp only [source, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, hx⟩,
        Finset.notMem_erase _ _⟩
      · exact fun y hy ↦ hu'.1 (Finset.mem_of_mem_erase hy)
      · rw [Finset.card_erase_of_mem hxu, hu'.2]
        omega
    · rintro ⟨t, x⟩ htx
      simp only [source, Finset.mem_filter] at htx
      apply Prod.ext
      · simp [Finset.erase_insert htx.2]
      · rfl
    · rintro ⟨u, x⟩ hux
      simp only [target, Finset.mem_filter] at hux
      apply Prod.ext
      · simp [Finset.insert_erase hux.2]
      · rfl
    · rintro ⟨t, x⟩ htx
      simp only [source, Finset.mem_filter] at htx
      change (∏ y ∈ t, w y) * w x = ∏ y ∈ insert x t, w y
      calc
        (∏ y ∈ t, w y) * w x = w x * ∏ y ∈ t, w y := mul_comm _ _
        _ = ∏ y ∈ insert x t, w y := (Finset.prod_insert htx.2).symm
  calc
    (k + 1 : ℝ) * elementaryMass s w (k + 1) =
        ∑ u ∈ s.powersetCard (k + 1), ∑ _x ∈ u, ∏ x ∈ u, w x := by
          simp only [elementaryMass, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          have hcard := (Finset.mem_powersetCard.mp hu).2
          rw [hcard]
          push_cast
          ring
    _ = ∑ z ∈ target, ∏ x ∈ z.1, w x := by
      rw [Finset.sum_finset_product target (s.powersetCard (k + 1))
        (fun u ↦ u) (by
          intro z
          simp only [target, Finset.mem_filter]
          constructor
          · rintro ⟨hprod, hmem⟩
            exact ⟨(Finset.mem_product.mp hprod).1, hmem⟩
          · rintro ⟨hu, hmem⟩
            have husub := (Finset.mem_powersetCard.mp hu).1
            exact ⟨Finset.mem_product.mpr ⟨hu, husub hmem⟩, hmem⟩)]
    _ = ∑ z ∈ source, (∏ x ∈ z.1, w x) * w z.2 := hbij.symm
    _ = ∑ t ∈ s.powersetCard k,
        (∏ x ∈ t, w x) * (∑ x ∈ s \ t, w x) := by
      rw [Finset.sum_finset_product source (s.powersetCard k)
        (fun t ↦ s \ t) (by
          intro z
          simp only [source, Finset.mem_filter]
          constructor
          · rintro ⟨hprod, hnot⟩
            exact ⟨(Finset.mem_product.mp hprod).1,
              Finset.mem_sdiff.mpr ⟨(Finset.mem_product.mp hprod).2, hnot⟩⟩
          · rintro ⟨ht, hx⟩
            exact ⟨Finset.mem_product.mpr ⟨ht, (Finset.mem_sdiff.mp hx).1⟩,
              (Finset.mem_sdiff.mp hx).2⟩)]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]

private lemma elementaryMass_succ_upper {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (k : ℕ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    (k + 1 : ℝ) * elementaryMass s w (k + 1) ≤
      elementaryMass s w k * ∑ x ∈ s, w x := by
  rw [elementaryMass_succ_identity, elementaryMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t ht
  have ht' := Finset.mem_powersetCard.mp ht
  have hcomp : (∑ x ∈ s \ t, w x) ≤ ∑ x ∈ s, w x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.sdiff_subset
    · intro x hx hnot
      exact hw x hx
  exact mul_le_mul_of_nonneg_left hcomp (by
    apply Finset.prod_nonneg
    intro x hx
    exact hw x (ht'.1 hx))

private lemma factorial_mul_elementaryMass_le_pow {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (k : ℕ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    (k.factorial : ℝ) * elementaryMass s w k ≤ (∑ x ∈ s, w x) ^ k := by
  induction k with
  | zero => simp [elementaryMass]
  | succ k ih =>
      have hrec := elementaryMass_succ_upper s w k hw
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      calc
        ((↑k + 1) * ↑k.factorial) * elementaryMass s w (k + 1) =
            (k.factorial : ℝ) * ((↑k + 1) * elementaryMass s w (k + 1)) := by ring
        _ ≤ (k.factorial : ℝ) *
            (elementaryMass s w k * ∑ x ∈ s, w x) :=
          mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _)
        _ = ((k.factorial : ℝ) * elementaryMass s w k) * ∑ x ∈ s, w x := by ring
        _ ≤ (∑ x ∈ s, w x) ^ k * ∑ x ∈ s, w x :=
          mul_le_mul_of_nonneg_right ih (Finset.sum_nonneg fun x hx ↦ hw x hx)

private lemma elementaryMass_le_pow_div_factorial {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (k : ℕ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    elementaryMass s w k ≤ (∑ x ∈ s, w x) ^ k / (k.factorial : ℝ) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)).2
  simpa [mul_comm] using factorial_mul_elementaryMass_le_pow s w k hw

/-- The elementary factorial bound used for the large-`k` range. -/
theorem Tk_le_factorial_tail (y k : ℕ) :
    Tk y k ≤ Real.log 2 *
      (2 * primeReciprocalSum (2 * y)) ^ k / (k.factorial : ℝ) := by
  classical
  let P := Nat.primesLE (2 * y)
  let w : ℕ → ℝ := fun p ↦ (1 : ℝ) / p
  have hw : ∀ p ∈ P, 0 ≤ w p := by intro p hp; positivity
  have hpoint : ∀ s ∈ P.powerset, s.card = k →
      L (s.prod fun p : ℕ ↦ p) (Real.log 2) /
          ((s.prod (fun p : ℕ ↦ p) : ℕ) : ℝ) ≤
        Real.log 2 * (2 : ℝ) ^ k * ∏ p ∈ s, w p := by
    intro s hs hcard
    have hprime : ∀ p ∈ s.toList, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primesLE (Finset.mem_powerset.mp hs (by simpa using hp))
    have hdiv := card_divisors_list_prod_primes s.toList hprime s.nodup_toList
    have hL := L_le_card_divisors_mul (a := s.prod fun p : ℕ ↦ p)
      (show 0 ≤ Real.log 2 from Real.log_nonneg (by norm_num))
    have hcardDiv : (s.prod fun p : ℕ ↦ p).divisors.card = 2 ^ k := by
      simpa [hcard] using hdiv
    rw [hcardDiv] at hL
    have hprodPos : (0 : ℝ) < (s.prod fun p : ℕ ↦ p) := by
      exact_mod_cast Finset.prod_pos fun p hp ↦
        (hprime p (by simpa using hp)).pos
    calc
      L (s.prod fun p : ℕ ↦ p) (Real.log 2) /
            ((s.prod (fun p : ℕ ↦ p) : ℕ) : ℝ) ≤
          ((2 ^ k : ℕ) : ℝ) * Real.log 2 /
            ((s.prod (fun p : ℕ ↦ p) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hL hprodPos.le
      _ = Real.log 2 * (2 : ℝ) ^ k * ∏ p ∈ s, w p := by
        simp only [w, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, Nat.cast_prod]
        simp only [one_mul]
        rw [← Finset.prod_inv_distrib]
        ring
  rw [Tk]
  calc
    ∑ s ∈ P.powerset with s.card = k,
        L (s.prod fun p : ℕ ↦ p) (Real.log 2) /
          ((s.prod (fun p : ℕ ↦ p) : ℕ) : ℝ) ≤
      ∑ s ∈ P.powerset with s.card = k,
        Real.log 2 * (2 : ℝ) ^ k * ∏ p ∈ s, w p := by
          apply Finset.sum_le_sum
          intro s hs
          have hs' := Finset.mem_filter.mp hs
          exact hpoint s hs'.1 hs'.2
    _ = Real.log 2 * (2 : ℝ) ^ k * elementaryMass P w k := by
      rw [elementaryMass]
      rw [Finset.powersetCard_eq_filter, Finset.mul_sum]
    _ ≤ Real.log 2 * (2 : ℝ) ^ k *
        ((∑ p ∈ P, w p) ^ k / (k.factorial : ℝ)) := by
      gcongr
      exact elementaryMass_le_pow_div_factorial P w k hw
    _ = Real.log 2 *
        (2 * primeReciprocalSum (2 * y)) ^ k / (k.factorial : ℝ) := by
      simp only [P, w, primeReciprocalSum, mul_pow]
      ring

private lemma primeReciprocalSum_two_mul_le_two_loglog {y : ℕ}
    (hv : 14 ≤ fordBinIndex y) :
    primeReciprocalSum (2 * y) ≤ 2 * Real.log (Real.log (2 * y)) := by
  let v := fordBinIndex y
  let x := 2 * y
  let t := Real.log (Real.log x)
  have hv1 : 1 ≤ v := by dsimp [v]; omega
  have htBounds := fordBinIndex_log_log_bounds (y := y) hv1
  have htLower : (v : ℝ) * Real.log 2 ≤ t := by simpa [v, x, t] using htBounds.1
  have htUpper : t < ((v : ℝ) + 1) * Real.log 2 := by
    simpa [v, x, t] using htBounds.2
  have hvR : (14 : ℝ) ≤ v := by exact_mod_cast hv
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht6 : (6 : ℝ) < t := by nlinarith [Real.log_two_gt_d9]
  have htpos : 0 < t := by linarith
  have hypos : 0 < y := by
    by_contra h
    have : y = 0 := Nat.eq_zero_of_not_pos h
    subst y
    norm_num [x, t] at ht6
  have hx : 2 ≤ x := by dsimp [x]; omega
  have hlogxpos : 0 < Real.log x := Real.log_pos (by
    exact_mod_cast (show 1 < x by omega))
  have hlogx : (64 : ℝ) ≤ Real.log x := by
    have hemono : Real.exp 6 ≤ Real.exp t := Real.exp_monotone ht6.le
    have he6 : (64 : ℝ) ≤ Real.exp 6 := by
      rw [show Real.exp 6 = (Real.exp 1) ^ 6 by rw [← Real.exp_nat_mul]; norm_num]
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) he1 6
    have hexpt : Real.exp t = Real.log x := by
      dsimp [t]
      exact Real.exp_log hlogxpos
    linarith
  have hM : Mertens.M ≤ t - 1 / 4 := by
    have hneglog : -Real.log (Real.log 2) ≤ (Real.log 2)⁻¹ - 1 := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hlog2pos)
      rw [Real.log_inv] at h
      exact h
    have hinv : (Real.log 2)⁻¹ ≤ (100 : ℝ) / 69 := by
      apply (inv_le_iff_one_le_mul₀ hlog2pos).2
      nlinarith [Real.log_two_gt_d9]
    have hbound := Mertens.M.le
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul] <;> norm_num
      ring
    rw [hlog4] at hbound
    have ht14 : (14 : ℝ) * Real.log 2 ≤ t := by
      calc
        (14 : ℝ) * Real.log 2 ≤ (v : ℝ) * Real.log 2 := by gcongr
        _ ≤ t := htLower
    rw [div_eq_mul_inv] at hbound
    nlinarith [Real.log_two_gt_d9]
  have herror :
      (Real.log 4 + 6 + Mertens.E₁) / Real.log x ≤ (1 : ℝ) / 4 := by
    have hnum : Real.log 4 + 6 + Mertens.E₁ ≤ (10 : ℝ) := by
      have hE := Mertens.E₁.le
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul] <;> norm_num
        ring
      rw [hlog4]
      nlinarith [Real.log_two_lt_d9]
    apply (div_le_iff₀ hlogxpos).2
    nlinarith
  have herr := primeReciprocalSum_mertens_error_le (x := x) hx
  have hu := (abs_le.mp herr).2
  dsimp [x, t] at hM hu herror ⊢
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hM hu herror ⊢
  linarith

private lemma self_pow_div_factorial_le_exp_one_pow (k : ℕ) :
    (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp 1 ^ k := by
  rw [← Real.exp_nat_mul, mul_one, Real.exp_eq_exp_ℝ,
    NormedSpace.exp_eq_tsum_div]
  exact Summable.le_tsum
    (show Summable (fun n : ℕ ↦ (k : ℝ) ^ n / (n.factorial : ℝ)) from
      Real.summable_pow_div_factorial (k : ℝ))
    k (fun _ _ ↦ by positivity)

/-- Past `10v`, the factorial estimate is dominated by a fixed geometric
sequence. -/
theorem Tk_le_geometric_tail {y k : ℕ}
    (hv : 14 ≤ fordBinIndex y) (hk : 10 * fordBinIndex y < k) :
    Tk y k ≤ Real.log 2 * (9 / 10 : ℝ) ^ k := by
  let v := fordBinIndex y
  let t := Real.log (Real.log (2 * y))
  let R := primeReciprocalSum (2 * y)
  have hv1 : 1 ≤ v := by dsimp [v]; omega
  have hvR : (14 : ℝ) ≤ v := by exact_mod_cast hv
  have hkNat : 10 * v < k := by simpa [v] using hk
  have hkpos : 0 < k := by omega
  have hkR : (10 : ℝ) * v < k := by exact_mod_cast hkNat
  have htBounds := fordBinIndex_log_log_bounds (y := y) hv1
  have htUpper : t < ((v : ℝ) + 1) * Real.log 2 := by simpa [v, t] using htBounds.2
  have hR : R ≤ 2 * t := by
    simpa [R, t] using primeReciprocalSum_two_mul_le_two_loglog hv
  have hR0 : 0 ≤ R := primeReciprocalSum_nonneg _
  have ht0 : 0 ≤ t := by
    have htLower := htBounds.1
    have hv0 : (0 : ℝ) ≤ (fordBinIndex y : ℝ) := by positivity
    have hlog20 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
    dsimp [t]
    nlinarith [mul_nonneg hv0 hlog20]
  have hratio : Real.exp 1 * (2 * R) / k ≤ (9 : ℝ) / 10 := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hlog : Real.log 2 < (7 : ℝ) / 10 :=
      Real.log_two_lt_d9.trans (by norm_num)
    have hnum : Real.exp 1 * (2 * R) ≤
        (42 : ℝ) / 5 * ((v : ℝ) + 1) := by
      calc
        Real.exp 1 * (2 * R) ≤ 3 * (4 * t) := by nlinarith
        _ ≤ 3 * (4 * (((v : ℝ) + 1) * ((7 : ℝ) / 10))) := by
          gcongr
          exact htUpper.le.trans (mul_le_mul_of_nonneg_left hlog.le (by positivity))
        _ = (42 : ℝ) / 5 * ((v : ℝ) + 1) := by ring
    have hnumk : Real.exp 1 * (2 * R) ≤ (9 : ℝ) / 10 * k := by
      calc
        Real.exp 1 * (2 * R) ≤ (42 : ℝ) / 5 * ((v : ℝ) + 1) := hnum
        _ ≤ 9 * (v : ℝ) := by nlinarith
        _ ≤ (9 : ℝ) / 10 * k := by nlinarith
    exact (div_le_iff₀ (by exact_mod_cast hkpos : (0 : ℝ) < k)).2 hnumk
  have hfac := self_pow_div_factorial_le_exp_one_pow k
  have hbase :
      (2 * R) ^ k / (k.factorial : ℝ) ≤
        (Real.exp 1 * (2 * R) / k) ^ k := by
    have hkR0 : (0 : ℝ) < k := by exact_mod_cast hkpos
    calc
      (2 * R) ^ k / (k.factorial : ℝ) =
          ((2 * R) / k) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by
            rw [div_pow]
            field_simp
      _ ≤ ((2 * R) / k) ^ k * Real.exp 1 ^ k := by
        gcongr
      _ = (Real.exp 1 * (2 * R) / k) ^ k := by
        rw [← mul_pow]
        congr 1
        field_simp
  calc
    Tk y k ≤ Real.log 2 * (2 * R) ^ k / (k.factorial : ℝ) := by
      simpa [R] using Tk_le_factorial_tail y k
    _ = Real.log 2 * ((2 * R) ^ k / (k.factorial : ℝ)) := by ring
    _ ≤ Real.log 2 * (Real.exp 1 * (2 * R) / k) ^ k := by gcongr
    _ ≤ Real.log 2 * (9 / 10 : ℝ) ^ k := by
      gcongr

/-- There are no squarefree prime sets of cardinality larger than the
number of available primes. -/
theorem Tk_eq_zero_of_prime_card_lt {y k : ℕ}
    (hk : (Nat.primesLE (2 * y)).card < k) : Tk y k = 0 := by
  classical
  unfold Tk
  apply Finset.sum_eq_zero
  intro s hs
  have hs' := Finset.mem_filter.mp hs
  have hsub := Finset.mem_powerset.mp hs'.1
  have := Finset.card_le_card hsub
  exfalso
  omega

/-- For fixed `y`, only finitely many `T_k(y)` are nonzero. -/
theorem summable_Tk (y : ℕ) : Summable (Tk y) := by
  apply summable_of_ne_finset_zero
    (s := Finset.range ((Nat.primesLE (2 * y)).card + 1))
  intro k hk
  apply Tk_eq_zero_of_prime_card_lt
  have : (Nat.primesLE (2 * y)).card + 1 ≤ k := by
    simpa only [Finset.mem_range, not_lt] using hk
  omega

/-- The infinite sum of the `T_k` is exactly its natural finite sum. -/
theorem tsum_Tk_eq_sum_range (y : ℕ) :
    ∑' k : ℕ, Tk y k =
      ∑ k ∈ Finset.range ((Nat.primesLE (2 * y)).card + 1), Tk y k := by
  apply tsum_eq_sum
  intro k hk
  apply Tk_eq_zero_of_prime_card_lt
  have : (Nat.primesLE (2 * y)).card + 1 ≤ k := by
    simpa only [Finset.mem_range, not_lt] using hk
  omega

/-- The full infinite tail beyond `10v` is the finite `Icc` tail used in
`ford_sum_Tk_tail`. -/
theorem tsum_Tk_tail_eq (y : ℕ) :
    (∑' k : ℕ, if 10 * fordBinIndex y < k then Tk y k else 0) =
      ∑ k ∈ Finset.Icc (10 * fordBinIndex y + 1)
        (Nat.primesLE (2 * y)).card, Tk y k := by
  calc
    (∑' k : ℕ, if 10 * fordBinIndex y < k then Tk y k else 0) =
        ∑ k ∈ Finset.Icc (10 * fordBinIndex y + 1)
          (Nat.primesLE (2 * y)).card,
            (if 10 * fordBinIndex y < k then Tk y k else 0) := by
      apply tsum_eq_sum
      intro k hk
      by_cases htail : 10 * fordBinIndex y < k
      · have hcard : (Nat.primesLE (2 * y)).card < k := by
          by_contra h
          have hkIcc : k ∈ Finset.Icc (10 * fordBinIndex y + 1)
              (Nat.primesLE (2 * y)).card := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          exact hk hkIcc
        simp [htail, Tk_eq_zero_of_prime_card_lt hcard]
      · simp [htail]
    _ = ∑ k ∈ Finset.Icc (10 * fordBinIndex y + 1)
          (Nat.primesLE (2 * y)).card, Tk y k := by
      apply Finset.sum_congr rfl
      intro k hk
      have := (Finset.mem_Icc.mp hk).1
      simp [show 10 * fordBinIndex y < k by omega]

private lemma sum_Icc_geometric_tail (K N : ℕ) :
    ∑ k ∈ Finset.Icc K N, (9 / 10 : ℝ) ^ k ≤
      10 * (9 / 10 : ℝ) ^ K := by
  let s := Finset.Icc K N
  have hsummable : Summable (fun d : ℕ ↦ (9 / 10 : ℝ) ^ d) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hnonneg : ∀ d : ℕ, 0 ≤ (9 / 10 : ℝ) ^ d := fun d ↦ by positivity
  have hinj : Set.InjOn (fun k ↦ k - K) s := by
    intro a ha b hb hab
    change a ∈ Finset.Icc K N at ha
    change b ∈ Finset.Icc K N at hb
    have haK := (Finset.mem_Icc.mp ha).1
    have hbK := (Finset.mem_Icc.mp hb).1
    calc
      a = K + (a - K) := (Nat.add_sub_of_le haK).symm
      _ = K + (b - K) := congrArg (K + ·) hab
      _ = b := Nat.add_sub_of_le hbK
  calc
    ∑ k ∈ Finset.Icc K N, (9 / 10 : ℝ) ^ k =
        (9 / 10 : ℝ) ^ K * ∑ k ∈ s, (9 / 10 : ℝ) ^ (k - K) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hKk := (Finset.mem_Icc.mp hk).1
      rw [← pow_add, Nat.add_sub_of_le hKk]
    _ ≤ (9 / 10 : ℝ) ^ K * ∑' d : ℕ, (9 / 10 : ℝ) ^ d := by
      gcongr
      let image := s.image (fun k ↦ k - K)
      have heq : ∑ k ∈ s, (9 / 10 : ℝ) ^ (k - K) =
          ∑ d ∈ image, (9 / 10 : ℝ) ^ d := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hinj ha hb hab
      rw [heq]
      exact hsummable.sum_le_tsum image (fun _ _ ↦ by positivity)
    _ = 10 * (9 / 10 : ℝ) ^ K := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

private lemma geometric_tail_le_inv_succ (v : ℕ) :
    (9 / 10 : ℝ) ^ (10 * v + 1) ≤ 1 / (v + 1 : ℝ) := by
  have hsucc : (v + 1 : ℕ) ≤ 2 ^ v := by
    induction v with
    | zero => simp
    | succ v ih =>
      calc
        v.succ + 1 ≤ 2 ^ v + 2 ^ v := by
          exact Nat.add_le_add ih Nat.one_le_two_pow
        _ = 2 ^ v.succ := by rw [pow_succ]; omega
  have hpow : (9 / 10 : ℝ) ^ 10 ≤ (1 : ℝ) / 2 := by norm_num
  have hvpow : ((9 / 10 : ℝ) ^ 10) ^ v ≤ ((1 : ℝ) / 2) ^ v := by
    exact pow_le_pow_left₀ (by positivity) hpow v
  have hsuccR : (v + 1 : ℝ) ≤ (2 : ℝ) ^ v := by exact_mod_cast hsucc
  have hmain : (v + 1 : ℝ) * (9 / 10 : ℝ) ^ (10 * v + 1) ≤ 1 := by
    rw [pow_add, pow_mul]
    simp only [pow_one]
    calc
      (v + 1 : ℝ) * (((9 / 10 : ℝ) ^ 10) ^ v * (9 / 10 : ℝ)) ≤
          (2 : ℝ) ^ v * (((1 : ℝ) / 2) ^ v * 1) := by gcongr <;> norm_num
      _ = 1 := by
        rw [mul_one, ← mul_pow]
        norm_num
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < v + 1)).2 (by simpa [mul_comm] using hmain)

private lemma inv_succ_le_stirlingTerm {y : ℕ}
    (hv : 14 ≤ fordBinIndex y) :
    1 / ((fordBinIndex y + 1 : ℕ) : ℝ) ≤
      stirlingTerm ((2 * y : ℕ) : ℝ) := by
  let v := fordBinIndex y
  let t := Real.log (Real.log (2 * y))
  have hv1 : 1 ≤ v := by dsimp [v]; omega
  have htBounds := fordBinIndex_log_log_bounds (y := y) hv1
  have htLower : (v : ℝ) * Real.log 2 ≤ t := by simpa [v, t] using htBounds.1
  have hbase : (v + 1 : ℝ) ≤ 2 * t := by
    have hvR : (14 : ℝ) ≤ v := by exact_mod_cast hv
    nlinarith [Real.log_two_gt_d9]
  have hfac : ((v + 1).factorial : ℝ) ≤ (v + 1 : ℝ) ^ (v + 1) := by
    exact_mod_cast Nat.factorial_le_pow (v + 1)
  have hpow : (v + 1 : ℝ) ^ v ≤ (2 * t) ^ v :=
    pow_le_pow_left₀ (by positivity) hbase v
  have hindex : stirlingIndex ((2 * y : ℕ) : ℝ) = v := by
    simp [stirlingIndex, v, fordBinIndex]
  have hden : (0 : ℝ) < (v + 1).factorial := by positivity
  have hcrit : 1 / (v + 1 : ℝ) ≤
      (2 * t) ^ v / ((v + 1).factorial : ℝ) := by
    apply (le_div_iff₀ hden).2
    calc
      1 / (v + 1 : ℝ) * ((v + 1).factorial : ℝ) ≤
          1 / (v + 1 : ℝ) * (v + 1 : ℝ) ^ (v + 1) := by gcongr
      _ = (v + 1 : ℝ) ^ v := by
        rw [pow_succ]
        field_simp
      _ ≤ (2 * t) ^ v := hpow
  rw [stirlingTerm, hindex]
  simpa [v, t] using hcrit

/-- The entire finite range beyond `10v` is bounded by an absolute constant
times the critical factorial term. -/
theorem ford_sum_Tk_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      ∑ k ∈ Finset.Icc (10 * fordBinIndex y + 1)
          (Nat.primesLE (2 * y)).card, Tk y k ≤
        C * stirlingTerm ((2 * y : ℕ) : ℝ) := by
  refine ⟨10 * Real.log 2, by positivity, ?_⟩
  intro y hv
  let v := fordBinIndex y
  have hpoint : ∀ k ∈ Finset.Icc (10 * v + 1) (Nat.primesLE (2 * y)).card,
      Tk y k ≤ Real.log 2 * (9 / 10 : ℝ) ^ k := by
    intro k hk
    apply Tk_le_geometric_tail hv
    have := (Finset.mem_Icc.mp hk).1
    dsimp [v] at this ⊢
    omega
  calc
    ∑ k ∈ Finset.Icc (10 * fordBinIndex y + 1)
          (Nat.primesLE (2 * y)).card, Tk y k ≤
        Real.log 2 * ∑ k ∈ Finset.Icc (10 * v + 1)
          (Nat.primesLE (2 * y)).card, (9 / 10 : ℝ) ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ ≤ Real.log 2 * (10 * (9 / 10 : ℝ) ^ (10 * v + 1)) := by
      gcongr
      exact sum_Icc_geometric_tail (10 * v + 1) (Nat.primesLE (2 * y)).card
    _ ≤ Real.log 2 * (10 * (1 / (v + 1 : ℝ))) := by
      gcongr
      exact geometric_tail_le_inv_succ v
    _ ≤ Real.log 2 * (10 * stirlingTerm ((2 * y : ℕ) : ℝ)) := by
      gcongr
      simpa [v] using inv_succ_le_stirlingTerm hv
    _ = (10 * Real.log 2) * stirlingTerm ((2 * y : ℕ) : ℝ) := by ring

/-- Infinite-sum form of `ford_sum_Tk_tail`.  The equality with the finite
tail is supplied by `tsum_Tk_tail_eq`, so no limiting convention is hidden
in this statement. -/
theorem ford_tsum_Tk_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 14 ≤ fordBinIndex y →
      (∑' k : ℕ, if 10 * fordBinIndex y < k then Tk y k else 0) ≤
        C * stirlingTerm ((2 * y : ℕ) : ℝ) := by
  obtain ⟨C, hC, htail⟩ := ford_sum_Tk_tail
  refine ⟨C, hC, ?_⟩
  intro y hv
  rw [tsum_Tk_tail_eq]
  exact htail y hv

end Erdos896.Ford
