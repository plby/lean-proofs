import BoundedGaps.Maynard.ImprovedGPY.CongruenceCount
import Mathlib.Data.Nat.Squarefree

/-!
# Prime-power events on squarefree arithmetic progressions

Expanding a squarefree Selberg weight gives a signed sum of residue-class
indicators.  On each residue class, divisibility by `p^j` has the same main
term as divisibility by `p`, divided by `p^(j-1)`.  The counting errors are
bounded independently of the prime and its exponent.
-/

open BoundedGaps.Maynard
open scoped BigOperators

namespace Erdos258b

def progressionDivisorCount (N L c k q : ℕ) : ℕ :=
  ((Finset.Ico N (2 * N)).filter fun n => n ≡ c [MOD L] ∧ q ∣ n + k).card

theorem exists_progression_divisor_residue {L c k q : ℕ}
    (hq : 0 < q) (hcompat : Nat.gcd L q ∣ c + k) :
    ∃ r : ℕ, ∀ n : ℕ,
      (n ≡ c [MOD L] ∧ q ∣ n + k) ↔ n ≡ r [MOD Nat.lcm L q] := by
  have hres : Nat.gcd L q ∣ negativeShiftResidue q k + k :=
    (Nat.gcd_dvd_right L q).trans (negativeShiftResidue_add_dvd q k hq)
  have hcrt : c ≡ negativeShiftResidue q k [MOD Nat.gcd L q] := by
    apply Nat.ModEq.add_right_cancel' k
    exact (Nat.modEq_zero_iff_dvd.mpr hcompat).trans
      (Nat.modEq_zero_iff_dvd.mpr hres).symm
  let r := Nat.chineseRemainder' hcrt
  refine ⟨r, fun n => ?_⟩
  constructor
  · rintro ⟨hn, hqdiv⟩
    exact Nat.mod_lcm (hn.trans r.property.1.symm)
      (((modEq_negativeShiftResidue_iff_dvd_add q k n hq).mpr hqdiv).trans
        r.property.2.symm)
  · intro hn
    refine ⟨(hn.of_dvd (Nat.dvd_lcm_left L q)).trans r.property.1, ?_⟩
    apply (modEq_negativeShiftResidue_iff_dvd_add q k n hq).mp
    exact (hn.of_dvd (Nat.dvd_lcm_right L q)).trans r.property.2

theorem progressionDivisorCount_eq_zero {N L c k q : ℕ}
    (hcompat : ¬Nat.gcd L q ∣ c + k) :
    progressionDivisorCount N L c k q = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_, hnL, hnq⟩ := Finset.mem_filter.mp hn
  apply hcompat
  have hnG : n + k ≡ c + k [MOD Nat.gcd L q] :=
    (hnL.of_dvd (Nat.gcd_dvd_left L q)).add_right k
  exact Nat.modEq_zero_iff_dvd.mp
    (hnG.symm.trans (Nat.modEq_zero_iff_dvd.mpr
      ((Nat.gcd_dvd_right L q).trans hnq)))

theorem progressionDivisorCount_error {N L c k q : ℕ}
    (hL : 0 < L) (hq : 0 < q) :
    |(progressionDivisorCount N L c k q : ℝ) -
      (if Nat.gcd L q ∣ c + k then (N : ℝ) / Nat.lcm L q else 0)| ≤ 1 := by
  by_cases hc : Nat.gcd L q ∣ c + k
  · rw [if_pos hc]
    obtain ⟨r, hr⟩ := exists_progression_divisor_residue hq hc
    have hcount : progressionDivisorCount N L c k q =
        ((Finset.Ico N (2 * N)).filter fun n => n ≡ r [MOD Nat.lcm L q]).card := by
      unfold progressionDivisorCount
      apply congrArg Finset.card
      ext n
      simp only [Finset.mem_filter, hr n]
    rw [hcount]
    have h := intervalModEqCardError_abs_le_one N (2 * N) (Nat.lcm L q) r
      (by omega) (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hL.ne' hq.ne'))
    have hlen : (2 : ℝ) * N - N = N := by ring
    simpa [intervalModEqCardError, Nat.cast_mul, hlen] using h
  · rw [if_neg hc, progressionDivisorCount_eq_zero hc]
    norm_num

theorem gcd_prime_pow_of_squarefree {L p j : ℕ}
    (hL : Squarefree L) (hj : 0 < j) :
    Nat.gcd L (p ^ j) = Nat.gcd L p := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left L (p ^ j))
    exact ((hL.squarefree_of_dvd (Nat.gcd_dvd_left L (p ^ j))).dvd_pow_iff_dvd hj.ne').mp
      (Nat.gcd_dvd_right L (p ^ j))
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left L p)
      ((Nat.gcd_dvd_right L p).trans (dvd_pow_self p hj.ne'))

theorem lcm_prime_pow_of_squarefree {L p j : ℕ}
    (hL : Squarefree L) (hp : 0 < p) (hj : 0 < j) :
    Nat.lcm L (p ^ j) = Nat.lcm L p * p ^ (j - 1) := by
  have hg : 0 < Nat.gcd L p := Nat.gcd_pos_of_pos_right L hp
  apply Nat.eq_of_mul_eq_mul_left hg
  rw [← gcd_prime_pow_of_squarefree hL hj, Nat.gcd_mul_lcm]
  rw [gcd_prime_pow_of_squarefree hL hj, ← mul_assoc, Nat.gcd_mul_lcm]
  rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hj]

theorem progressionDivisorCount_prime_pow_error {N L c k p j : ℕ}
    (hL : Squarefree L) (hp : p.Prime) (hj : 0 < j) :
    |(progressionDivisorCount N L c k (p ^ j) : ℝ) -
      (progressionDivisorCount N L c k p : ℝ) / p ^ (j - 1)| ≤ 2 := by
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL.ne_zero
  have hq : (0 : ℝ) < (p : ℝ) ^ (j - 1) :=
    pow_pos (Nat.cast_pos.mpr hp.pos) _
  have hqone : (1 : ℝ) ≤ (p : ℝ) ^ (j - 1) :=
    one_le_pow₀ (by exact_mod_cast hp.one_le)
  have hpow := progressionDivisorCount_error (N := N) (c := c) (k := k)
    hLpos (pow_pos hp.pos j)
  have hprime := progressionDivisorCount_error (N := N) (c := c) (k := k)
    hLpos hp.pos
  rw [gcd_prime_pow_of_squarefree hL hj,
    lcm_prime_pow_of_squarefree hL hp.pos hj, Nat.cast_mul, Nat.cast_pow,
    ← div_div] at hpow
  by_cases hc : Nat.gcd L p ∣ c + k
  · rw [if_pos hc] at hpow hprime
    have hscaled :
        |((progressionDivisorCount N L c k p : ℝ) -
          (N : ℝ) / Nat.lcm L p) / (p : ℝ) ^ (j - 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos hq]
      exact (div_le_iff₀ hq).mpr (by nlinarith)
    have htriangle := abs_sub_le
      (progressionDivisorCount N L c k (p ^ j) : ℝ)
      ((N : ℝ) / Nat.lcm L p / (p : ℝ) ^ (j - 1))
      ((progressionDivisorCount N L c k p : ℝ) / (p : ℝ) ^ (j - 1))
    rw [sub_div] at hscaled
    rw [abs_sub_comm ((N : ℝ) / Nat.lcm L p / (p : ℝ) ^ (j - 1))] at htriangle
    linarith
  · rw [progressionDivisorCount_eq_zero hc]
    have hc' : ¬ Nat.gcd L (p ^ j) ∣ c + k := by
      simpa [gcd_prime_pow_of_squarefree hL hj] using hc
    rw [progressionDivisorCount_eq_zero hc']
    norm_num

noncomputable def divisorEventMass (N k q : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N), if q ∣ n + k then w n else 0

theorem divisorEventMass_le_total (N k q : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) :
    divisorEventMass N k q w ≤ ∑ n ∈ Finset.Ico N (2 * N), w n := by
  apply Finset.sum_le_sum
  intro n hn
  split_ifs
  · exact le_rfl
  · exact hw n

theorem divisorEventMass_expansion {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (L r : ι → ℕ) (N k q : ℕ) {w : ℕ → ℝ}
    (hexpand : ∀ n, w n = ∑ i ∈ S, if n ≡ r i [MOD L i] then c i else 0) :
    divisorEventMass N k q w =
      ∑ i ∈ S, c i * (progressionDivisorCount N (L i) (r i) k q : ℝ) := by
  classical
  unfold divisorEventMass
  simp_rw [hexpand]
  have hpoint (n : ℕ) :
      (if q ∣ n + k then ∑ i ∈ S, if n ≡ r i [MOD L i] then c i else 0 else 0) =
        ∑ i ∈ S, if q ∣ n + k then (if n ≡ r i [MOD L i] then c i else 0) else 0 := by
    by_cases hd : q ∣ n + k <;> simp [hd]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [progressionDivisorCount, Finset.natCast_card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : q ∣ n + k <;> by_cases hr : n ≡ r i [MOD L i] <;> simp [hd, hr]

/-- No positivity is needed for the coefficients of the progression expansion.
The error is controlled by their absolute mass. -/
theorem divisorEventMass_prime_pow_error {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (L r : ι → ℕ) (N k : ℕ) {w : ℕ → ℝ}
    (hexpand : ∀ n, w n = ∑ i ∈ S, if n ≡ r i [MOD L i] then c i else 0)
    (hL : ∀ i ∈ S, Squarefree (L i)) {p j : ℕ}
    (hp : p.Prime) (hj : 0 < j) :
    |divisorEventMass N k (p ^ j) w - divisorEventMass N k p w / p ^ (j - 1)| ≤
      2 * ∑ i ∈ S, |c i| := by
  rw [divisorEventMass_expansion S c L r N k (p ^ j) hexpand,
    divisorEventMass_expansion S c L r N k p hexpand]
  have hdiv (f : ι → ℝ) (q : ℝ) : (∑ i ∈ S, f i) / q = ∑ i ∈ S, f i / q := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [hdiv, ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ S, (c i * ↑(progressionDivisorCount N (L i) (r i) k (p ^ j)) -
        c i * ↑(progressionDivisorCount N (L i) (r i) k p) / (p : ℝ) ^ (j - 1))| ≤
        ∑ i ∈ S, |c i * ↑(progressionDivisorCount N (L i) (r i) k (p ^ j)) -
          c i * ↑(progressionDivisorCount N (L i) (r i) k p) / (p : ℝ) ^ (j - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, 2 * |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_div_assoc, ← mul_sub, abs_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (progressionDivisorCount_prime_pow_error (N := N) (c := r i) (k := k)
          (hL i hi) hp hj) (abs_nonneg (c i))
    _ = 2 * ∑ i ∈ S, |c i| := (Finset.mul_sum _ _ _).symm

theorem divisorEventMass_prime_pow_le {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (L r : ι → ℕ) (N k : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hexpand : ∀ n, w n = ∑ i ∈ S, if n ≡ r i [MOD L i] then c i else 0)
    (hL : ∀ i ∈ S, Squarefree (L i)) {p j : ℕ}
    (hp : p.Prime) (hj : 0 < j) :
    divisorEventMass N k (p ^ j) w ≤
      (∑ n ∈ Finset.Ico N (2 * N), w n) / p ^ (j - 1) +
        2 * ∑ i ∈ S, |c i| := by
  have herr := (abs_le.mp (divisorEventMass_prime_pow_error S c L r N k
    hexpand hL hp hj)).2
  have htotal := div_le_div_of_nonneg_right (divisorEventMass_le_total N k p hw)
    (show (0 : ℝ) ≤ (p : ℝ) ^ (j - 1) by positivity)
  linarith

end Erdos258b
