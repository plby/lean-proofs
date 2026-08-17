import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Polynomial

noncomputable section

namespace Erdos1215

open Complex Metric Set
open Filter
open Polynomial

/-- Conjugate reciprocal with respect to an ambient degree `N`. -/
def conjReflect (N : ℕ) (p : ℂ[X]) : ℂ[X] :=
  (p.map (starRingEnd ℂ)).reflect N

lemma norm_conjReflect_eval_of_norm_eq_one (p : ℂ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(conjReflect p.natDegree p).eval z‖ = ‖p.eval z‖ := by
  have hz0 : star z ≠ 0 := by
    simpa using (norm_ne_zero_iff.mp (by simp [hz] : ‖star z‖ ≠ 0))
  letI : Invertible (star z) := invertibleOfNonzero hz0
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) (star z) p.natDegree
    (p.map (starRingEnd ℂ)) (natDegree_map_le.trans le_rfl)
  have hinv : (star z)⁻¹ = z := by
    rw [inv_eq_iff_eq_inv]
    simpa [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  rw [invOf_eq_inv, hinv] at h
  have hn := congrArg norm h
  simpa [conjReflect, norm_mul, norm_pow, hz] using hn

/-- The conjugate reciprocal is no larger than the original polynomial on the closed unit disk,
provided that the original polynomial has no zero there.  This is the finite Blaschke-product
estimate, proved here directly by the maximum-modulus principle. -/
lemma norm_conjReflect_eval_le (p : ℂ[X])
    (hp : ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(conjReflect p.natDegree p).eval z‖ ≤ ‖p.eval z‖ := by
  let q := conjReflect p.natDegree p
  let f : ℂ → ℂ := fun w ↦ q.eval w / p.eval w
  have hdiff : DifferentiableOn ℂ f (closedBall 0 1) := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hw
    exact (q.differentiableAt.div p.differentiableAt (hp w hw')).differentiableWithinAt
  have hf : DiffContOnCl ℂ f (ball 0 1) := hdiff.diffContOnCl_ball subset_rfl
  have hboundary : ∀ w ∈ frontier (ball (0 : ℂ) 1), ‖f w‖ ≤ 1 := by
    intro w hw
    have hw' : ‖w‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp (frontier_ball_subset_sphere hw)
    have hpw : p.eval w ≠ 0 := hp w hw'.le
    rw [show f w = q.eval w / p.eval w by rfl, norm_div]
    rw [show ‖q.eval w‖ = ‖p.eval w‖ by
      simpa [q] using norm_conjReflect_eval_of_norm_eq_one p hw']
    exact (div_self (norm_ne_zero_iff.mpr hpw)).le
  have hzcl : z ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball 0 one_ne_zero]
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hratio : ‖f z‖ ≤ 1 :=
    norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf hboundary hzcl
  have hpz : 0 < ‖p.eval z‖ := norm_pos_iff.mpr (hp z hz)
  rw [show f z = q.eval z / p.eval z by rfl, norm_div] at hratio
  exact (div_le_one hpz).mp (by simpa [q] using hratio)

@[simp] lemma conjReflect_conjReflect (N : ℕ) (p : ℂ[X]) :
    conjReflect N (conjReflect N p) = p := by
  ext i
  simp [conjReflect, coeff_reflect, coeff_map]

lemma conjReflect_mul (F G : ℕ) (p q : ℂ[X])
    (hp : p.natDegree ≤ F) (hq : q.natDegree ≤ G) :
    conjReflect (F + G) (p * q) = conjReflect F p * conjReflect G q := by
  unfold conjReflect
  rw [Polynomial.map_mul]
  exact reflect_mul (p.map (starRingEnd ℂ)) (q.map (starRingEnd ℂ))
    (natDegree_map_le.trans hp) (natDegree_map_le.trans hq)

lemma conjReflect_sub (N : ℕ) (p q : ℂ[X]) :
    conjReflect N (p - q) = conjReflect N p - conjReflect N q := by
  simp [conjReflect]

lemma natDegree_conjReflect (p : ℂ[X]) (hp0 : p.eval 0 = 1) :
    (conjReflect p.natDegree p).natDegree = p.natDegree := by
  have hpcoeff : p.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, hp0]
    exact one_ne_zero
  have hmapdeg : (p.map (starRingEnd ℂ)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective (starRingEnd ℂ).injective p
  have htrail : (p.map (starRingEnd ℂ)).natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero]
    exact Or.inr (by simpa [coeff_map] using hpcoeff)
  rw [conjReflect, ← hmapdeg]
  change (p.map (starRingEnd ℂ)).reverse.natDegree = _
  rw [reverse_natDegree, htrail, Nat.sub_zero, hmapdeg]

/-- Mac Lane's reciprocal perturbation `p - X^(n-deg p) p⁺`. -/
def macLanePolynomial (p : ℂ[X]) (n : ℕ) : ℂ[X] :=
  p - X ^ (n - p.natDegree) * conjReflect p.natDegree p

lemma macLanePolynomial_natDegree (p : ℂ[X]) (hp0 : p.eval 0 = 1) {n : ℕ}
    (hn : p.natDegree < n) : (macLanePolynomial p n).natDegree = n := by
  let q := conjReflect p.natDegree p
  have hqdeg : q.natDegree = p.natDegree := by
    simpa [q] using natDegree_conjReflect p hp0
  have hq0 : q ≠ 0 := by
    intro hq
    have hp : p = 0 := by
      rw [← conjReflect_conjReflect p.natDegree p, show conjReflect p.natDegree p = 0 by
        simpa [q] using hq]
      simp [conjReflect]
    rw [hp] at hp0
    simp at hp0
  have htermdeg : (X ^ (n - p.natDegree) * q).natDegree = n := by
    rw [natDegree_X_pow_mul (n - p.natDegree) hq0, hqdeg, Nat.add_sub_of_le hn.le]
  have hlt : p.natDegree < (X ^ (n - p.natDegree) * q).natDegree := by
    rw [htermdeg]
    exact hn
  rw [macLanePolynomial]
  change (p - X ^ (n - p.natDegree) * q).natDegree = n
  rw [natDegree_sub_eq_right_of_natDegree_lt hlt, htermdeg]

lemma macLanePolynomial_eval_zero (p : ℂ[X]) (hp0 : p.eval 0 = 1) {n : ℕ}
    (hn : p.natDegree < n) : (macLanePolynomial p n).eval 0 = 1 := by
  have hk : n - p.natDegree ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr hn)
  simp [macLanePolynomial, hp0, hk]

@[simp] lemma conjReflect_one (N : ℕ) : conjReflect N (1 : ℂ[X]) = X ^ N := by
  simp [conjReflect]

@[simp] lemma conjReflect_X_pow (N : ℕ) : conjReflect N (X ^ N : ℂ[X]) = 1 := by
  simp [conjReflect, reflect_monomial, revAt_le]

lemma conjReflect_macLanePolynomial (p : ℂ[X]) (hp0 : p.eval 0 = 1) {n : ℕ}
    (hn : p.natDegree < n) :
    conjReflect n (macLanePolynomial p n) = -macLanePolynomial p n := by
  let m := p.natDegree
  let k := n - m
  let q := conjReflect m p
  have hmk : m + k = n := Nat.add_sub_of_le hn.le
  have hkm : k + m = n := by simpa [Nat.add_comm] using hmk
  have hqdeg : q.natDegree = m := by
    simpa [q, m] using natDegree_conjReflect p hp0
  have hstarP : conjReflect n p = q * X ^ k := by
    rw [← hmk]
    simpa [q, m] using conjReflect_mul m k p 1 le_rfl (by simp)
  have hstarTerm : conjReflect n (X ^ k * q) = p := by
    rw [← hkm]
    simpa [q] using conjReflect_mul k m (X ^ k) q (by simp) hqdeg.le
  rw [macLanePolynomial]
  change conjReflect n (p - X ^ k * q) = -(p - X ^ k * q)
  rw [conjReflect_sub, hstarP, hstarTerm]
  ring

lemma macLanePolynomial_no_root_in_unitBall (p : ℂ[X])
    (hp : ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) {n : ℕ} (hn : p.natDegree < n)
    {z : ℂ} (hz : ‖z‖ < 1) : ¬(macLanePolynomial p n).IsRoot z := by
  intro hroot
  let q := conjReflect p.natDegree p
  let k := n - p.natDegree
  have hk : k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr hn)
  have heq : p.eval z = z ^ k * q.eval z := by
    rw [IsRoot, macLanePolynomial, eval_sub, eval_mul, eval_pow, eval_X, sub_eq_zero] at hroot
    simpa [q, k] using hroot
  have hqle : ‖q.eval z‖ ≤ ‖p.eval z‖ := by
    simpa [q] using norm_conjReflect_eval_le p hp hz.le
  have hpz : 0 < ‖p.eval z‖ := norm_pos_iff.mpr (hp z hz.le)
  have hzpow : ‖z‖ ^ k < 1 := pow_lt_one₀ (norm_nonneg z) hz hk
  have hfalse : ‖p.eval z‖ < ‖p.eval z‖ := calc
    ‖p.eval z‖ = ‖z‖ ^ k * ‖q.eval z‖ := by rw [heq, norm_mul, norm_pow]
    _ ≤ ‖z‖ ^ k * ‖p.eval z‖ :=
      mul_le_mul_of_nonneg_left hqle (pow_nonneg (norm_nonneg z) k)
    _ < 1 * ‖p.eval z‖ := mul_lt_mul_of_pos_right hzpow hpz
    _ = ‖p.eval z‖ := one_mul _
  exact (lt_irrefl _ hfalse)

lemma isRoot_conj_inv_of_conjReflect_eq_neg {P : ℂ[X]} {N : ℕ}
    (hdeg : P.natDegree ≤ N) (hself : conjReflect N P = -P) {z : ℂ}
    (hz0 : z ≠ 0) (hz : P.IsRoot z) : P.IsRoot (star z)⁻¹ := by
  have hstarz0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz0
  letI : Invertible (star z) := invertibleOfNonzero hstarz0
  have hmapzero : (P.map (starRingEnd ℂ)).eval (star z) = 0 := by
    simpa using congrArg (starRingEnd ℂ) hz.eq_zero
  have hreflect : (conjReflect N P).eval (star z)⁻¹ = 0 := by
    have hiff := eval₂_reflect_eq_zero_iff (RingHom.id ℂ) (star z) N
      (P.map (starRingEnd ℂ)) (natDegree_map_le.trans hdeg)
    rw [invOf_eq_inv] at hiff
    exact hiff.mpr hmapzero
  rw [hself, eval_neg, neg_eq_zero] at hreflect
  exact hreflect

lemma macLanePolynomial_roots_on_unitCircle (p : ℂ[X]) (hp0 : p.eval 0 = 1)
    (hp : ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) {n : ℕ} (hn : p.natDegree < n)
    {z : ℂ} (hz : (macLanePolynomial p n).IsRoot z) : ‖z‖ = 1 := by
  have hnotin : ¬ ‖z‖ < 1 := fun hlt ↦
    macLanePolynomial_no_root_in_unitBall p hp hn hlt hz
  have hge : 1 ≤ ‖z‖ := le_of_not_gt hnotin
  apply le_antisymm ?_ hge
  by_contra hnotle
  have hout : 1 < ‖z‖ := lt_of_not_ge hnotle
  have hz0 : z ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hout))
  have hreflect : (macLanePolynomial p n).IsRoot (star z)⁻¹ :=
    isRoot_conj_inv_of_conjReflect_eq_neg (macLanePolynomial_natDegree p hp0 hn).le
      (conjReflect_macLanePolynomial p hp0 hn) hz0 hz
  have hin : ‖(star z)⁻¹‖ < 1 := by
    rw [norm_inv, norm_star]
    exact inv_lt_one_of_one_lt₀ hout
  exact macLanePolynomial_no_root_in_unitBall p hp hn hin hreflect

/-- Checked form of Mac Lane's reciprocal-polynomial step.  Once `p` is normalized, zero-free on
the closed unit disk, and larger than `5/2` on a compact subset `K` of the open disk, every
sufficiently large target degree is obtained by a normalized polynomial whose roots all lie on the
unit circle and whose norm is larger than `2` on `K`. -/
theorem exists_macLanePolynomial_for_all_large_degrees (p : ℂ[X]) (K : Set ℂ)
    (hp0 : p.eval 0 = 1)
    (hp : ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0)
    (hK : IsCompact K) (hKdisk : ∀ z ∈ K, ‖z‖ < 1)
    (hplarge : ∀ z ∈ K, (5 : ℝ) / 2 < ‖p.eval z‖) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ P : ℂ[X],
      P.natDegree = n ∧ P.eval 0 = 1 ∧
      (∀ z : ℂ, P.IsRoot z → ‖z‖ = 1) ∧
      ∀ z ∈ K, 2 < ‖P.eval z‖ := by
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨p.natDegree + 1, fun n hn ↦ ⟨macLanePolynomial p n, ?_, ?_, ?_, ?_⟩⟩
    · exact macLanePolynomial_natDegree p hp0 (by omega)
    · exact macLanePolynomial_eval_zero p hp0 (by omega)
    · intro z hz
      exact macLanePolynomial_roots_on_unitCircle p hp0 hp (by omega) hz
    · intro z hz
      simp [hKempty] at hz
  · let q := conjReflect p.natDegree p
    obtain ⟨a, haK, haMax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
    let r := ‖a‖
    have hr0 : 0 ≤ r := norm_nonneg a
    have hr1 : r < 1 := hKdisk a haK
    have hnorm_le : ∀ z ∈ K, ‖z‖ ≤ r := by
      intro z hz
      exact haMax hz
    obtain ⟨b, hbK, hbMax⟩ := hK.exists_isMaxOn hKne
      (q.differentiable.continuous.norm.continuousOn)
    let B := ‖q.eval b‖
    have hq_le : ∀ z ∈ K, ‖q.eval z‖ ≤ B := by
      intro z hz
      exact hbMax hz
    have htend : Tendsto (fun k : ℕ ↦ r ^ k * B) atTop (nhds 0) :=
      by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const B
    have hevent : ∀ᶠ k : ℕ in atTop, r ^ k * B < (1 : ℝ) / 2 :=
      htend.eventually_lt_const (by norm_num)
    obtain ⟨k₀, hk₀⟩ := (eventually_atTop.1 hevent)
    refine ⟨p.natDegree + k₀ + 1, fun n hn ↦ ⟨macLanePolynomial p n, ?_, ?_, ?_, ?_⟩⟩
    · exact macLanePolynomial_natDegree p hp0 (by omega)
    · exact macLanePolynomial_eval_zero p hp0 (by omega)
    · intro z hz
      exact macLanePolynomial_roots_on_unitCircle p hp0 hp (by omega) hz
    · intro z hzK
      let k := n - p.natDegree
      have hk₀le : k₀ ≤ k := by omega
      have hsmall : r ^ k * B < (1 : ℝ) / 2 := hk₀ k hk₀le
      have hpow : ‖z‖ ^ k ≤ r ^ k :=
        pow_le_pow_left₀ (norm_nonneg z) (hnorm_le z hzK) k
      have hterm : ‖z ^ k * q.eval z‖ < (1 : ℝ) / 2 := by
        rw [norm_mul, norm_pow]
        exact (mul_le_mul hpow (hq_le z hzK) (norm_nonneg _)
          (pow_nonneg hr0 k)).trans_lt hsmall
      have hlower : ‖p.eval z‖ - ‖z ^ k * q.eval z‖ ≤
          ‖(macLanePolynomial p n).eval z‖ := by
        simpa [macLanePolynomial, q, k] using
          (norm_sub_norm_le (p.eval z) (z ^ k * q.eval z))
      exact lt_of_lt_of_le (by linarith [hplarge z hzK]) hlower

#print axioms exists_macLanePolynomial_for_all_large_degrees

end Erdos1215
