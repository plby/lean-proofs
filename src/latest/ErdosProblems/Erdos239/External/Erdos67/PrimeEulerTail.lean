import ErdosProblems.Erdos239.External.Erdos67.Pretentious
import BoundedGaps.Maynard.PrimeMertensInterval
import BoundedGaps.BombieriVinogradov.Analytic.Dyadic

open scoped BigOperators
open Finset Nat Real

namespace Erdos67

noncomputable section

open BoundedGaps.Maynard

noncomputable def primeLogIntervalMertensConstant : ℝ :=
  Classical.choose exists_uniform_abs_primeLogIntervalSum_sub_log_div

theorem primeLogIntervalMertensConstant_spec {w z : ℕ}
    (hw : 2 ≤ w) (hwz : w ≤ z) :
    |primeLogIntervalSum w z - Real.log ((z : ℝ) / (w : ℝ))| ≤
      primeLogIntervalMertensConstant :=
  Classical.choose_spec exists_uniform_abs_primeLogIntervalSum_sub_log_div hw hwz

theorem primeLogIntervalMertensConstant_nonneg :
    0 ≤ primeLogIntervalMertensConstant := by
  have h := primeLogIntervalMertensConstant_spec (w := 2) (z := 2) le_rfl le_rfl
  exact (abs_nonneg _).trans h

theorem primeLogMass_dyadicBlock_le (alpha : ℕ) :
    (∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
      Real.log p / (p : ℝ)) ≤
      Real.log 2 + primeLogIntervalMertensConstant := by
  have hpowPos : 0 < 2 ^ alpha := pow_pos (by omega) _
  have hw : 2 ≤ 2 ^ alpha + 1 := by omega
  have hwz : 2 ^ alpha + 1 ≤ 2 ^ (alpha + 1) := by
    rw [pow_succ]
    omega
  have hspec := primeLogIntervalMertensConstant_spec hw hwz
  have hmain :
      Real.log (((2 ^ (alpha + 1) : ℕ) : ℝ) /
        ((2 ^ alpha + 1 : ℕ) : ℝ)) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by positivity)]
    push_cast
    rw [pow_succ]
    nlinarith
  have heq :
      (∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
        Real.log p / (p : ℝ)) =
        primeLogIntervalSum (2 ^ alpha + 1) (2 ^ (alpha + 1)) := by
    unfold dyadicBlock primeLogIntervalSum
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Nat.mem_primesLE, Nat.add_sub_cancel]
      aesop
    · intro p hp
      rfl
  rw [heq]
  linarith [le_abs_self
    (primeLogIntervalSum (2 ^ alpha + 1) (2 ^ (alpha + 1)) -
      Real.log (((2 ^ (alpha + 1) : ℕ) : ℝ) /
        ((2 ^ alpha + 1 : ℕ) : ℝ)))]

theorem primeRpowMass_dyadicBlock_le {delta : ℝ} (hdelta : 0 ≤ delta)
    {alpha : ℕ} (halpha : 1 ≤ alpha) :
    (∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
      (p : ℝ) ^ (-(1 + delta))) ≤
      ((2 ^ alpha : ℕ) : ℝ) ^ (-delta) /
          ((alpha : ℝ) * Real.log 2) *
        (Real.log 2 + primeLogIntervalMertensConstant) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hCnonneg := primeLogIntervalMertensConstant_nonneg
  have hpoint : ∀ p ∈ (dyadicBlock alpha).filter Nat.Prime,
      (p : ℝ) ^ (-(1 + delta)) ≤
        (Real.log p / (p : ℝ)) *
          (((2 ^ alpha : ℕ) : ℝ) ^ (-delta) /
            ((alpha : ℝ) * Real.log 2)) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpBlock := Finset.mem_Ioc.mp hp'.1
    have hpPrime := hp'.2
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hpLower : (((2 ^ alpha : ℕ) : ℝ)) ≤ p := by
      exact_mod_cast hpBlock.1.le
    have hpowPos : (0 : ℝ) < (2 ^ alpha : ℕ) := by positivity
    have hpowDamp :
        (p : ℝ) ^ (-delta) ≤ ((2 ^ alpha : ℕ) : ℝ) ^ (-delta) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hpowPos) hpLower
        (neg_nonpos.mpr hdelta)
    have hlogLower :
        (alpha : ℝ) * Real.log 2 ≤ Real.log p := by
      calc
        (alpha : ℝ) * Real.log 2 = Real.log (((2 : ℝ) ^ alpha)) := by
          rw [Real.log_pow]
        _ ≤ Real.log p := Real.log_le_log (by positivity)
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpLower)
    have halphaPos : (0 : ℝ) < alpha := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one halpha)
    have hdenPos : 0 < (alpha : ℝ) * Real.log 2 := mul_pos halphaPos hlogTwo
    have hlogpPos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpPrime.one_lt)
    have hfactor :
        (p : ℝ) ^ (-delta) / Real.log p ≤
          ((2 ^ alpha : ℕ) : ℝ) ^ (-delta) /
            ((alpha : ℝ) * Real.log 2) := by
      exact div_le_div₀ (Real.rpow_nonneg (by positivity) _) hpowDamp
        hdenPos hlogLower
    have hidentity :
        (p : ℝ) ^ (-(1 + delta)) =
          (Real.log p / (p : ℝ)) *
            ((p : ℝ) ^ (-delta) / Real.log p) := by
      rw [show -(1 + delta) = (-1 : ℝ) + (-delta) by ring,
        Real.rpow_add hpPos, Real.rpow_neg (by positivity), Real.rpow_one]
      field_simp
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left hfactor
      (div_nonneg hlogpPos.le hpPos.le)
  calc
    (∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
      (p : ℝ) ^ (-(1 + delta))) ≤
        ∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
          (Real.log p / (p : ℝ)) *
            (((2 ^ alpha : ℕ) : ℝ) ^ (-delta) /
              ((alpha : ℝ) * Real.log 2)) := Finset.sum_le_sum hpoint
    _ = (((2 ^ alpha : ℕ) : ℝ) ^ (-delta) /
              ((alpha : ℝ) * Real.log 2)) *
          (∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
            Real.log p / (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (((2 ^ alpha : ℕ) : ℝ) ^ (-delta) /
              ((alpha : ℝ) * Real.log 2)) *
          (Real.log 2 + primeLogIntervalMertensConstant) := by
      gcongr
      exact primeLogMass_dyadicBlock_le alpha
    _ = _ := by ring

theorem dyadic_rpow_eq_geometric (delta : ℝ) (alpha : ℕ) :
    ((2 ^ alpha : ℕ) : ℝ) ^ (-delta) =
      ((2 : ℝ) ^ (-delta)) ^ alpha := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow,
    Real.rpow_def_of_pos (by positivity), ← Real.exp_nat_mul]
  congr 1
  ring

theorem reciprocalLog_primeRpow_tail_le {Y Z : ℕ} (hY : 4 ≤ Y) :
    (∑ p ∈ primesBetween Y Z,
      (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))) ≤
      4 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2 := by
  let delta : ℝ := (Real.log (Y : ℝ))⁻¹
  let a : ℕ := Nat.log 2 Y
  let r : ℝ := (2 : ℝ) ^ (-delta)
  let M : ℝ := Real.log 2 + primeLogIntervalMertensConstant
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hdelta : 0 < delta := inv_pos.mpr hlogY
  have ha : 1 ≤ a := by
    dsimp only [a]
    apply (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr
    exact (show 2 ≤ Y by omega)
  have haPos : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact add_nonneg hlogTwo.le primeLogIntervalMertensConstant_nonneg
  have hrNonneg : 0 ≤ r := by
    dsimp only [r]
    exact Real.rpow_nonneg (by norm_num) _
  have hrLt : r < 1 := by
    dsimp only [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hdelta)
  have hdecomp :
      (∑ p ∈ primesBetween Y Z,
        (p : ℝ) ^ (-(1 + delta))) =
      ∑ alpha ∈ dyadicExponentRange Z,
        ∑ p ∈ (primesBetween Y Z).filter
          (fun p ↦ p ∈ dyadicBlock alpha),
          (p : ℝ) ^ (-(1 + delta)) := by
    apply sum_eq_sum_dyadicBlocks
    intro p hp
    have hp' := mem_primesBetween.mp hp
    exact ⟨hp'.1.two_le, hp'.2.2⟩
  have hblock : ∀ alpha ∈ dyadicExponentRange Z,
      (∑ p ∈ (primesBetween Y Z).filter
          (fun p ↦ p ∈ dyadicBlock alpha),
          (p : ℝ) ^ (-(1 + delta))) ≤
        M / ((a : ℝ) * Real.log 2) * r ^ alpha := by
    intro alpha halpha
    by_cases hsmall : alpha < a
    · have hempty : (primesBetween Y Z).filter
          (fun p ↦ p ∈ dyadicBlock alpha) = ∅ := by
        ext p
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hpBetween hpBlock
        have hpB := mem_primesBetween.mp hpBetween
        have hpTwo := hpB.1.two_le
        have hlog := (mem_dyadicBlock_iff_log_pred_eq hpTwo).mp hpBlock
        have hYpred : Y ≤ p - 1 := by omega
        have hmono : Nat.log 2 Y ≤ Nat.log 2 (p - 1) :=
          Nat.log_mono_right hYpred
        dsimp only [a] at hsmall
        omega
      rw [hempty]
      simp only [Finset.sum_empty]
      positivity
    · have haa : a ≤ alpha := le_of_not_gt hsmall
      have halphaOne : 1 ≤ alpha := ha.trans haa
      have hsubset : (primesBetween Y Z).filter
            (fun p ↦ p ∈ dyadicBlock alpha) ⊆
          (dyadicBlock alpha).filter Nat.Prime := by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hp'.2, (mem_primesBetween.mp hp'.1).1⟩
      have hsubsum :
          (∑ p ∈ (primesBetween Y Z).filter
              (fun p ↦ p ∈ dyadicBlock alpha),
              (p : ℝ) ^ (-(1 + delta))) ≤
            ∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
              (p : ℝ) ^ (-(1 + delta)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro p hp hpnot
        exact Real.rpow_nonneg (by positivity) _
      have hdyadic := primeRpowMass_dyadicBlock_le hdelta.le halphaOne
      rw [dyadic_rpow_eq_geometric delta alpha] at hdyadic
      dsimp only [r, M]
      calc
        (∑ p ∈ (primesBetween Y Z).filter
            (fun p ↦ p ∈ dyadicBlock alpha),
            (p : ℝ) ^ (-(1 + delta))) ≤
              ∑ p ∈ (dyadicBlock alpha).filter Nat.Prime,
                (p : ℝ) ^ (-(1 + delta)) := hsubsum
        _ ≤ ((2 : ℝ) ^ (-delta)) ^ alpha /
              ((alpha : ℝ) * Real.log 2) * M := hdyadic
        _ ≤ M / ((a : ℝ) * Real.log 2) *
              ((2 : ℝ) ^ (-delta)) ^ alpha := by
          have hden : (a : ℝ) * Real.log 2 ≤
              (alpha : ℝ) * Real.log 2 := by gcongr
          have hdiv : 1 / ((alpha : ℝ) * Real.log 2) ≤
              1 / ((a : ℝ) * Real.log 2) :=
            one_div_le_one_div_of_le (mul_pos haPos hlogTwo) hden
          have hrpow : 0 ≤ ((2 : ℝ) ^ (-delta)) ^ alpha := by positivity
          calc
            ((2 : ℝ) ^ (-delta)) ^ alpha /
                ((alpha : ℝ) * Real.log 2) * M =
              (((2 : ℝ) ^ (-delta)) ^ alpha * M) *
                (1 / ((alpha : ℝ) * Real.log 2)) := by ring
            _ ≤ (((2 : ℝ) ^ (-delta)) ^ alpha * M) *
                (1 / ((a : ℝ) * Real.log 2)) :=
              mul_le_mul_of_nonneg_left hdiv (mul_nonneg hrpow hM)
            _ = M / ((a : ℝ) * Real.log 2) *
                ((2 : ℝ) ^ (-delta)) ^ alpha := by ring
  rw [show (Real.log (Y : ℝ))⁻¹ = delta by rfl]
  rw [hdecomp]
  calc
    (∑ alpha ∈ dyadicExponentRange Z,
        ∑ p ∈ (primesBetween Y Z).filter
          (fun p ↦ p ∈ dyadicBlock alpha),
          (p : ℝ) ^ (-(1 + delta))) ≤
        ∑ alpha ∈ dyadicExponentRange Z,
          (M / ((a : ℝ) * Real.log 2) * r ^ alpha) :=
      Finset.sum_le_sum hblock
    _ ≤ ∑' alpha : ℕ,
          (M / ((a : ℝ) * Real.log 2) * r ^ alpha) := by
      have hnorm : ‖r‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hrNonneg]
        exact hrLt
      have hgeom : Summable (fun alpha : ℕ ↦ r ^ alpha) :=
        summable_geometric_of_norm_lt_one hnorm
      have hsum : Summable (fun alpha : ℕ ↦
          M / ((a : ℝ) * Real.log 2) * r ^ alpha) :=
        Summable.mul_left (M / ((a : ℝ) * Real.log 2)) hgeom
      exact hsum.sum_le_tsum (dyadicExponentRange Z) (fun _ _ ↦ by positivity)
    _ = M / ((a : ℝ) * Real.log 2) * (1 - r)⁻¹ := by
      have hnorm : ‖r‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hrNonneg]
        exact hrLt
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
    _ ≤ 4 * M / Real.log 2 := by
      have hxPos : 0 < Real.log 2 / Real.log (Y : ℝ) := div_pos hlogTwo hlogY
      have hxLe : Real.log 2 / Real.log (Y : ℝ) ≤ 1 := by
        rw [div_le_one hlogY]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ Y by omega))
      have hrExp : r = Real.exp (-(Real.log 2 / Real.log (Y : ℝ))) := by
        dsimp only [r, delta]
        rw [Real.rpow_def_of_pos (by norm_num)]
        congr 1
        field_simp
      have hexpLower := Real.add_one_le_exp
        (Real.log 2 / Real.log (Y : ℝ))
      have hexpInv : Real.exp (-(Real.log 2 / Real.log (Y : ℝ))) ≤
          (1 + Real.log 2 / Real.log (Y : ℝ))⁻¹ := by
        rw [Real.exp_neg]
        rw [inv_le_inv₀ (Real.exp_pos _) (by linarith)]
        simpa [add_comm] using hexpLower
      have honeSub : Real.log 2 / (2 * Real.log (Y : ℝ)) ≤ 1 - r := by
        rw [hrExp]
        have heqhalf : Real.log 2 / (2 * Real.log (Y : ℝ)) =
            (Real.log 2 / Real.log (Y : ℝ)) / 2 := by field_simp
        have hxhalf : Real.log 2 / (2 * Real.log (Y : ℝ)) ≤
            (Real.log 2 / Real.log (Y : ℝ)) /
              (1 + Real.log 2 / Real.log (Y : ℝ)) := by
          rw [heqhalf]
          exact div_le_div_of_nonneg_left hxPos.le (by linarith) (by linarith)
        calc
          Real.log 2 / (2 * Real.log (Y : ℝ)) ≤
              (Real.log 2 / Real.log (Y : ℝ)) /
                (1 + Real.log 2 / Real.log (Y : ℝ)) := hxhalf
          _ = 1 - (1 + Real.log 2 / Real.log (Y : ℝ))⁻¹ := by
            field_simp
            ring
          _ ≤ 1 - Real.exp (-(Real.log 2 / Real.log (Y : ℝ))) :=
            sub_le_sub_left hexpInv 1
      have honeSubPos : 0 < 1 - r := sub_pos.mpr hrLt
      have hinvBound : (1 - r)⁻¹ ≤
          2 * Real.log (Y : ℝ) / Real.log 2 := by
        have hBpos : 0 < 2 * Real.log (Y : ℝ) / Real.log 2 := by positivity
        rw [inv_le_comm₀ honeSubPos hBpos]
        have heq : (2 * Real.log (Y : ℝ) / Real.log 2)⁻¹ =
            Real.log 2 / (2 * Real.log (Y : ℝ)) := by field_simp
        rw [heq]
        exact honeSub
      have hYpow : Y < 2 ^ (a + 1) := by
        dsimp only [a]
        simpa only [Nat.succ_eq_add_one] using
          (Nat.lt_pow_succ_log_self (by omega : 1 < 2) Y)
      have hlogUpper : Real.log (Y : ℝ) ≤
          ((a : ℝ) + 1) * Real.log 2 := by
        have hcast : (Y : ℝ) ≤ ((2 ^ (a + 1) : ℕ) : ℝ) := by
          exact_mod_cast hYpow.le
        calc
          Real.log (Y : ℝ) ≤ Real.log (((2 ^ (a + 1) : ℕ) : ℝ)) :=
            Real.log_le_log (by positivity) hcast
          _ = ((a : ℝ) + 1) * Real.log 2 := by
            push_cast
            rw [Real.log_pow]
            norm_num
      have hlogUpper' : Real.log (Y : ℝ) ≤ 2 * (a : ℝ) * Real.log 2 := by
        have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
        nlinarith [hlogTwo]
      have hfactorNonneg : 0 ≤ M / ((a : ℝ) * Real.log 2) := by positivity
      calc
        M / ((a : ℝ) * Real.log 2) * (1 - r)⁻¹ ≤
            M / ((a : ℝ) * Real.log 2) *
              (2 * Real.log (Y : ℝ) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hinvBound hfactorNonneg
        _ ≤ 4 * M / Real.log 2 := by
          field_simp
          nlinarith
    _ = 4 * (Real.log 2 + primeLogIntervalMertensConstant) /
        Real.log 2 := rfl

/-- Infinite form of `reciprocalLog_primeRpow_tail_le`.  The limit passage is
made through arbitrary finite sets of prime subtypes, so this theorem can be
used directly in an absolutely convergent Euler-product tail. -/
theorem tsum_primeSubtype_reciprocalLog_rpow_tail_le {Y : ℕ} (hY : 4 ≤ Y) :
    (∑' p : {p : Nat.Primes // Y < p.1},
      (p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))) ≤
      4 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2 := by
  classical
  let f : {p : Nat.Primes // Y < p.1} → ℝ := fun p ↦
    (p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))
  let C : ℝ :=
    4 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2
  have hfin : ∀ s : Finset {p : Nat.Primes // Y < p.1},
      ∑ p ∈ s, f p ≤ C := by
    intro s
    let Z : ℕ := s.sup (fun p ↦ p.1.1)
    let sNat : Finset ℕ := s.image (fun p ↦ p.1.1)
    have hinj : Set.InjOn
        (fun p : {p : Nat.Primes // Y < p.1} ↦ p.1.1) s := by
      intro p hp q hq hpq
      exact Subtype.ext (Subtype.ext hpq)
    have hsum : (∑ p ∈ s, f p) =
        ∑ p ∈ sNat,
          (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
      rw [show (∑ p ∈ s, f p) = ∑ p ∈ s,
          ((p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))) by rfl]
      exact (Finset.sum_image
        (f := fun p : ℕ ↦
          (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)))
        (g := fun p : {p : Nat.Primes // Y < p.1} ↦ p.1.1) hinj).symm
    have hsub : sNat ⊆ primesBetween Y Z := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact mem_primesBetween.mpr ⟨a.1.2, a.2,
        (Finset.le_sup
          (f := fun p : {p : Nat.Primes // Y < p.1} ↦ p.1.1) ha)⟩
    calc
      ∑ p ∈ s, f p = ∑ p ∈ sNat,
          (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := hsum
      _ ≤ ∑ p ∈ primesBetween Y Z,
          (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp hpnot
        exact Real.rpow_nonneg (by positivity) _
      _ ≤ C := reciprocalLog_primeRpow_tail_le hY
  have hf : Summable f :=
    summable_of_sum_le (fun p ↦ Real.rpow_nonneg (by positivity) _) hfin
  change (∑' p, f p) ≤ C
  exact hasSum_le_of_sum_le hf.hasSum hfin

end
end Erdos67
