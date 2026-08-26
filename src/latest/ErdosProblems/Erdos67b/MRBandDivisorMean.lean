import ErdosProblems.Erdos448.MeanValueSpecial448
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Uniform second moments of divisors supported on a prime band

The source moment lemma uses a divisor-count majorant. We prove its
global second moment by lcm counting and an injective gcd decomposition,
using only finite Euler products and geometric series.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

/-- Positive integers through `N` with all prime factors in `P`. -/
def bandFactoredPrefix (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n ↦ n ∈ Nat.factoredNumbers P

/-- Divisors supported on the selected prime set. -/
def bandDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.divisors.filter fun d ↦ d ∈ Nat.factoredNumbers P).card

/-- The finite reciprocal Euler product for a prime band. -/
def bandReciprocalEuler (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹

/-- The reciprocal series of integers supported on a finite prime set
converges, with exactly the finite Euler product as its value. -/
theorem hasSum_bandFactored_reciprocal (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P ↦ (n.1 : ℝ)⁻¹) (bandReciprocalEuler P) := by
  have hlocal (p : ℕ) (hp : p.Prime) :
      HasSum (fun k : ℕ ↦ ((p ^ k : ℕ) : ℝ)⁻¹) (1 - (p : ℝ)⁻¹)⁻¹ := by
    have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    simpa only [Nat.cast_pow, inv_pow] using hasSum_geometric_of_lt_one hr0 hr1
  have hEuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ ↦ (n : ℝ)⁻¹) (by simp)
    (by intro m n _; simp only [Nat.cast_mul, mul_inv])
    (by
      intro p hp
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((p ^ _ : ℕ) : ℝ)⁻¹)]
        using (hlocal p hp).summable) P
  have hfilter : P.filter Nat.Prime = P := Finset.filter_eq_self.mpr hP
  have hval : (∏ p ∈ P with p.Prime, ∑' k : ℕ, ((p ^ k : ℕ) : ℝ)⁻¹) =
      bandReciprocalEuler P := by
    rw [hfilter]
    apply Finset.prod_congr rfl
    intro p hp
    exact (hlocal p (hP p hp)).tsum_eq
  rw [hval] at hEuler
  exact hEuler.2

/-- Every finite supported reciprocal sum is at most its convergent
Euler product. -/
theorem sum_bandFactoredPrefix_reciprocal_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ bandFactoredPrefix P N, (n : ℝ)⁻¹) ≤ bandReciprocalEuler P := by
  classical
  let S := bandFactoredPrefix P N
  let e : S → Nat.factoredNumbers P := fun n ↦ ⟨n.1, (Finset.mem_filter.mp n.2).2⟩
  have he : Function.Injective e := by
    intro m n hmn
    exact Subtype.ext (congrArg (fun z : Nat.factoredNumbers P ↦ z.1) hmn)
  have hsum := (hasSum_bandFactored_reciprocal P hP).summable
  have hle := Summable.sum_le_tsum (s := Finset.univ.image e)
    (f := fun n : Nat.factoredNumbers P ↦ (n.1 : ℝ)⁻¹)
    (fun n _ ↦ by positivity) hsum
  rw [Finset.sum_image (fun _ _ _ _ h ↦ he h),
    (hasSum_bandFactored_reciprocal P hP).tsum_eq] at hle
  change (∑ n : S, (n.1 : ℝ)⁻¹) ≤ bandReciprocalEuler P at hle
  rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl) (fun n : ℕ ↦ (n : ℝ)⁻¹)]
  exact hle

/-- The gcd decomposition of a positive pair records its lcm as a
triple product and recovers both original coordinates. -/
theorem gcd_div_triple_identities {d e : ℕ} (hd : 0 < d) (_he : 0 < e) :
    d.gcd e * (d / d.gcd e) = d ∧
      d.gcd e * (e / d.gcd e) = e ∧
      d.gcd e * (d / d.gcd e) * (e / d.gcd e) = d.lcm e := by
  have ha : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e hd
  have hleft := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have hright := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  refine ⟨hleft, hright, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left ha
  calc
    d.gcd e * (d.gcd e * (d / d.gcd e) * (e / d.gcd e)) =
        (d.gcd e * (d / d.gcd e)) * (d.gcd e * (e / d.gcd e)) := by ring
    _ = d * e := by rw [hleft, hright]
    _ = d.gcd e * d.lcm e := (Nat.gcd_mul_lcm d e).symm

/-- Finite supported prefixes are closed under taking positive divisors. -/
theorem mem_bandFactoredPrefix_of_dvd {P : Finset ℕ} {N d n : ℕ}
    (hn : n ∈ bandFactoredPrefix P N) (hd : d ∣ n) : d ∈ bandFactoredPrefix P N := by
  obtain ⟨hnI, hnP⟩ := Finset.mem_filter.mp hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hnI).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hnpos
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos,
    (Nat.le_of_dvd hnpos hd).trans (Finset.mem_Icc.mp hnI).2⟩,
    Nat.mem_factoredNumbers_of_dvd hnP hd⟩

/-- The reciprocal lcm sum is bounded by three independent supported
reciprocal sums, with no loss depending on the prefix length. -/
theorem sum_bandFactoredPrefix_lcm_inv_le_cube (P : Finset ℕ) (N : ℕ) :
    (∑ d ∈ bandFactoredPrefix P N, ∑ e ∈ bandFactoredPrefix P N,
      (d.lcm e : ℝ)⁻¹) ≤ (∑ n ∈ bandFactoredPrefix P N, (n : ℝ)⁻¹) ^ 3 := by
  classical
  let S := bandFactoredPrefix P N
  let F : ℕ × ℕ → (ℕ × ℕ) × ℕ := fun x ↦
    ((x.1.gcd x.2, x.1 / x.1.gcd x.2), x.2 / x.1.gcd x.2)
  let w : (ℕ × ℕ) × ℕ → ℝ := fun x ↦ ((x.1.1 * x.1.2 * x.2 : ℕ) : ℝ)⁻¹
  have hmaps : (S ×ˢ S).image F ⊆ (S ×ˢ S) ×ˢ S := by
    intro z hz
    obtain ⟨⟨d, e⟩, hde, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_bandFactoredPrefix_of_dvd hd (Nat.gcd_dvd_left d e)
    · exact mem_bandFactoredPrefix_of_dvd hd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d e))
    · exact mem_bandFactoredPrefix_of_dvd he (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right d e))
  have hinj : Set.InjOn F (↑(S ×ˢ S) : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hxpos : 0 < x.1 ∧ 0 < x.2 := by
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
      exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hx1).1).1,
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hx2).1).1⟩
    have hypos : 0 < y.1 ∧ 0 < y.2 := by
      obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
      exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hy1).1).1,
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hy2).1).1⟩
    have hxid := gcd_div_triple_identities hxpos.1 hxpos.2
    have hyid := gcd_div_triple_identities hypos.1 hypos.2
    have h1 := congrArg (fun z : (ℕ × ℕ) × ℕ ↦ z.1.1 * z.1.2) hxy
    have h2 := congrArg (fun z : (ℕ × ℕ) × ℕ ↦ z.1.1 * z.2) hxy
    exact Prod.ext (hxid.1.symm.trans (h1.trans hyid.1))
      (hxid.2.1.symm.trans (h2.trans hyid.2.1))
  calc
    _ = ∑ x ∈ S ×ˢ S, w (F x) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      have hdpos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hepos : 0 < e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
      dsimp [w, F]
      rw [(gcd_div_triple_identities hdpos hepos).2.2]
    _ = ∑ z ∈ (S ×ˢ S).image F, w z := (Finset.sum_image hinj).symm
    _ ≤ ∑ z ∈ (S ×ˢ S) ×ˢ S, w z :=
      Finset.sum_le_sum_of_subset_of_nonneg hmaps (fun z _ _ ↦ by dsimp [w]; positivity)
    _ = (∑ n ∈ S, (n : ℝ)⁻¹) ^ 3 := by
      simp only [Finset.sum_product, w, Nat.cast_mul, mul_inv, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Counting simultaneous divisibility gives a uniform divisor second
moment with an explicit finite Euler-product constant. -/
theorem sum_bandDivisorCount_sq_le_euler (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (bandDivisorCount P n : ℝ) ^ 2) ≤
      (N : ℝ) * bandReciprocalEuler P ^ 3 := by
  classical
  let W : ℕ → ℕ → ℝ := fun d e ↦
    (if d ∈ Nat.factoredNumbers P then 1 else 0) *
      (if e ∈ Nat.factoredNumbers P then 1 else 0)
  have hW : ∀ d e, 0 ≤ W d e := by intro d e; dsimp [W]; positivity
  have hbase := Erdos448Scratch.pair_divisor_first_moment W N hW
  have hleft (n : ℕ) : (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, W d e) =
      (bandDivisorCount P n : ℝ) ^ 2 := by
    simp only [W, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_boole, bandDivisorCount]
    ring
  have hright : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      W d e / (d.lcm e : ℝ)) =
      ∑ d ∈ bandFactoredPrefix P N, ∑ e ∈ bandFactoredPrefix P N, (d.lcm e : ℝ)⁻¹ := by
    simp only [bandFactoredPrefix, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdP : d ∈ Nat.factoredNumbers P
    · simp only [W, hdP, if_true, one_mul]
      apply Finset.sum_congr rfl
      intro e he
      by_cases heP : e ∈ Nat.factoredNumbers P <;> simp [heP]
    · simp [W, hdP]
  simp_rw [hleft] at hbase
  rw [hright] at hbase
  have hrecip := sum_bandFactoredPrefix_reciprocal_le P hP N
  have hnonneg : 0 ≤ ∑ n ∈ bandFactoredPrefix P N, (n : ℝ)⁻¹ := by positivity
  have hcube := (sum_bandFactoredPrefix_lcm_inv_le_cube P N).trans
    (pow_le_pow_left₀ hnonneg hrecip 3)
  exact hbase.trans (mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg N))

/-- A local Euler factor is at most `exp(2/p)`, uniformly for primes. -/
theorem bandReciprocalEuler_local_le_exp {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * (p : ℝ)⁻¹) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hr : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
  have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith
  have hlocal : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 1 + 2 * (p : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [inv_nonneg.mpr hp0.le]
  exact hlocal.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * (p : ℝ)⁻¹))

theorem bandReciprocalEuler_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    bandReciprocalEuler P ≤ Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  calc
    _ ≤ ∏ p ∈ P, Real.exp (2 * (p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
        have hr : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
        positivity
      · intro p hp
        exact bandReciprocalEuler_local_le_exp (hP p hp)
    _ = Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) := by rw [← Real.exp_sum, ← Finset.mul_sum]

/-- The reciprocal mass of any subset of a dyadic integer block is at
most two; no prime-distribution estimate is needed. -/
theorem reciprocal_sum_le_two_of_dyadic_subset {P : Finset ℕ} {Y : ℕ}
    (hY : 2 ≤ Y) (hP : P ⊆ Finset.Icc Y (2 * Y)) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 2 := by
  have hYr : (0 : ℝ) < Y := by positivity
  have hcard : P.card ≤ Y + 1 := by
    have hc := Finset.card_le_card hP
    simpa only [Nat.card_Icc, show 2 * Y + 1 - Y = Y + 1 by omega] using hc
  calc
    _ ≤ ∑ _p ∈ P, (Y : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_anti₀ hYr (by exact_mod_cast (Finset.mem_Icc.mp (hP hp)).1)
    _ = (P.card : ℝ) / Y := by rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ ((Y + 1 : ℕ) : ℝ) / Y := by gcongr
    _ ≤ 2 := by
      apply (div_le_iff₀ hYr).mpr
      push_cast
      have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
      linarith

/-- A uniform dyadic prime-band divisor square mean. This supplies the
global divisor estimate used in the multiscale product-moment lemma. -/
theorem sum_bandDivisorCount_sq_le_exp_twelve
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {Y : ℕ}
    (hY : 2 ≤ Y) (hP : P ⊆ Finset.Icc Y (2 * Y)) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (bandDivisorCount P n : ℝ) ^ 2) ≤ Real.exp 12 * N := by
  have hmass := reciprocal_sum_le_two_of_dyadic_subset hY hP
  have hE : bandReciprocalEuler P ≤ Real.exp 4 :=
    (bandReciprocalEuler_le_exp P hprime).trans (Real.exp_le_exp.mpr (by linarith))
  have hE0 : 0 ≤ bandReciprocalEuler P := by
    have hsum := sum_bandFactoredPrefix_reciprocal_le P hprime 0
    simpa [bandFactoredPrefix] using hsum
  have hcube := pow_le_pow_left₀ hE0 hE 3
  have hexp : Real.exp 4 ^ 3 = Real.exp 12 := by rw [← Real.exp_nat_mul]; norm_num
  rw [hexp] at hcube
  exact (sum_bandDivisorCount_sq_le_euler P hprime N).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg N))

end

end Erdos67b
