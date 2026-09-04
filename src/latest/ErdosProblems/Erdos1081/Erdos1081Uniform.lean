import ErdosProblems.Erdos1081.Erdos1081LValue
import ErdosProblems.Erdos164
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace Erdos1081

open Filter Finset Set
open scoped Topology ComplexConjugate LSeries.notation

noncomputable section

noncomputable def primeLogRpowSum (s : ℝ) : ℝ :=
  ∑' q : ℕ, if q.Prime then
    Real.log (q : ℝ) / Real.rpow (q : ℝ) s else 0

noncomputable def primeRpowTail (Q : ℕ) (s : ℝ) : ℝ :=
  ∑' q : ℕ,
    if Q < q ∧ q.Prime then (Real.rpow (q : ℝ) s)⁻¹ else 0

noncomputable def eulerLogNat {M : ℕ}
    (chi : DirichletCharacter ℂ M) (s : ℝ) (q : ℕ) : ℂ := by
  classical
  exact if q.Prime then
    -Complex.log (1 - chi q * (q : ℂ) ^ (-(s : ℂ))) else 0

theorem norm_eulerLogNat_le {M : ℕ}
    (chi : DirichletCharacter ℂ M) {s : ℝ} (hs : 1 < s) (q : ℕ) :
    ‖eulerLogNat chi s q‖ ≤
      (3 / 2 : ℝ) *
        (if q.Prime then (Real.rpow (q : ℝ) s)⁻¹ else 0) := by
  classical
  by_cases hq : q.Prime
  · let z : ℂ := -(chi q * (q : ℂ) ^ (-(s : ℂ)))
    have hpowHalf : ‖(q : ℂ) ^ (-(s : ℂ))‖ ≤ (1 : ℝ) / 2 := by
      exact Complex.norm_prime_cpow_le_one_half ⟨q, hq⟩ (by simpa using hs)
    have hzHalf : ‖z‖ ≤ (1 : ℝ) / 2 := by
      rw [show ‖z‖ = ‖chi q‖ * ‖(q : ℂ) ^ (-(s : ℂ))‖ by
        simp [z]]
      exact (mul_le_mul (chi.norm_le_one q) hpowHalf
        (norm_nonneg _) zero_le_one).trans (by norm_num)
    have hlog := Complex.norm_log_one_add_half_le_self hzHalf
    have hpowNorm : ‖(q : ℂ) ^ (-(s : ℂ))‖ =
        (Real.rpow (q : ℝ) s)⁻¹ := by
      rw [Complex.norm_natCast_cpow_of_pos hq.pos]
      simp only [Complex.neg_re, Complex.ofReal_re]
      rw [Real.rpow_neg (by positivity)]
      rfl
    simp only [eulerLogNat, if_pos hq, norm_neg]
    rw [show 1 - chi q * (q : ℂ) ^ (-(s : ℂ)) = 1 + z by
      simp [z]
      ring]
    calc
      ‖Complex.log (1 + z)‖ ≤ (3 / 2 : ℝ) * ‖z‖ := hlog
      _ ≤ (3 / 2 : ℝ) * (Real.rpow (q : ℝ) s)⁻¹ := by
        rw [show ‖z‖ = ‖chi q‖ * ‖(q : ℂ) ^ (-(s : ℂ))‖ by
          simp [z], hpowNorm]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_of_le_one_left
          (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
          (chi.norm_le_one q)
  · simp [eulerLogNat, hq]

noncomputable def quadraticCharReal (p q : ℕ) [Fact p.Prime] : ℝ :=
  (quadraticChar (ZMod p) (q : ZMod p) : ℤ)

theorem complexQuadraticChar_nat_eq_ofReal
    (p q : ℕ) [Fact p.Prime] :
    complexQuadraticChar p q = (quadraticCharReal p q : ℂ) := by
  simp [quadraticCharReal, complexQuadraticChar_apply]

noncomputable def quadraticCharRpowSum
    (p Q : ℕ) [Fact p.Prime] (s : ℝ) : ℝ :=
  ∑ q ∈ Nat.primesLE Q,
    quadraticCharReal p q * (Real.rpow (q : ℝ) s)⁻¹

theorem norm_eulerLogNat_sub_quadraticMain_le
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    {s : ℝ} (hs : 1 < s) :
    ‖eulerLogNat (complexQuadraticChar p) s q -
        (quadraticCharReal p q *
          (Real.rpow (q : ℝ) s)⁻¹ : ℝ)‖ ≤
      (Real.rpow (q : ℝ) s)⁻¹ ^ 2 := by
  let z : ℂ := complexQuadraticChar p q *
    (q : ℂ) ^ (-(s : ℂ))
  have hpowNorm : ‖(q : ℂ) ^ (-(s : ℂ))‖ =
      (Real.rpow (q : ℝ) s)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos hq.pos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by positivity)]
    rfl
  have hzHalf : ‖z‖ ≤ (1 : ℝ) / 2 := by
    rw [norm_mul]
    have hpowHalf : ‖(q : ℂ) ^ (-(s : ℂ))‖ ≤ (1 : ℝ) / 2 :=
      Complex.norm_prime_cpow_le_one_half ⟨q, hq⟩ (by simpa using hs)
    calc
      ‖complexQuadraticChar p q‖ * ‖(q : ℂ) ^ (-(s : ℂ))‖ ≤
          1 * ‖(q : ℂ) ^ (-(s : ℂ))‖ :=
        mul_le_mul_of_nonneg_right
          ((complexQuadraticChar p).norm_le_one q) (norm_nonneg _)
      _ ≤ (1 : ℝ) / 2 := by simpa using hpowHalf
  have hzlt : ‖z‖ < 1 := hzHalf.trans_lt (by norm_num)
  have hlog := Complex.norm_log_one_sub_inv_sub_self_le hzlt
  have hloginv : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := by
    apply Complex.log_inv
    exact Complex.slitPlane_arg_ne_pi
      (by
        have hzmem := Complex.mem_slitPlane_of_norm_lt_one
          (z := -z) (by simpa using hzlt)
        simpa [sub_eq_add_neg] using hzmem)
  have hrem : ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
    rw [← hloginv]
    calc
      ‖Complex.log (1 - z)⁻¹ - z‖ ≤
          ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := hlog
      _ ≤ ‖z‖ ^ 2 := by
        have hden : 0 < 1 - ‖z‖ := by linarith
        have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hden (by norm_num)]
          linarith
        have hzsq : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hinv hzsq]
  have hzMain : z =
      (quadraticCharReal p q *
        (Real.rpow (q : ℝ) s)⁻¹ : ℝ) := by
    have hpower : (q : ℂ) ^ (-(s : ℂ)) =
        (((Real.rpow (q : ℝ) s)⁻¹ : ℝ) : ℂ) := by
      calc
        (q : ℂ) ^ (-(s : ℂ)) =
            ((Real.rpow (q : ℝ) (-s) : ℝ) : ℂ) := by
          simpa using (Complex.ofReal_cpow
            (show (0 : ℝ) ≤ q by positivity) (-s)).symm
        _ = (((Real.rpow (q : ℝ) s)⁻¹ : ℝ) : ℂ) := by
          congr 1
          exact Real.rpow_neg (by positivity) s
    dsimp [z]
    unfold quadraticCharReal
    rw [hpower]
    norm_cast
  rw [eulerLogNat, if_pos hq]
  rw [show complexQuadraticChar p q * (q : ℂ) ^ (-(s : ℂ)) = z by rfl]
  rw [← hzMain]
  exact hrem.trans (by
    rw [norm_mul, hpowNorm]
    have hchi : ‖complexQuadraticChar p q‖ ≤ 1 :=
      (complexQuadraticChar p).norm_le_one q
    have hr : 0 ≤ (Real.rpow (q : ℝ) s)⁻¹ :=
      inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
    exact (sq_le_sq₀
      (mul_nonneg (norm_nonneg _) hr) hr).2
        (mul_le_of_le_one_left hr hchi))

theorem Erdos164.analyticSeries_eq_tsum_nat {s : ℝ} (hs : 1 < s) :
    Erdos164.analyticSeries s =
      ∑' q : ℕ, if 2 ≤ q then
        ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) s else 0 := by
  let f : ℕ → ℝ := fun q ↦ if 2 ≤ q then
    ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) s else 0
  change (∑' q : {q : ℕ // 2 ≤ q},
      ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) s) = _
  calc
    (∑' q : {q : ℕ // 2 ≤ q},
        ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) s) =
        ∑' q : {q : ℕ // 2 ≤ q}, f q := by
      apply tsum_congr
      intro q
      simp [f, q.2]
    _ = ∑' q : ℕ, f q := by
      apply tsum_subtype_eq_of_support_subset
      intro q hq
      change 2 ≤ q
      by_contra hq2
      simp [f, hq2] at hq

theorem summable_primeLogRpowSum {s : ℝ} (hs : 1 < s) :
    Summable (fun q : ℕ ↦ if q.Prime then
      Real.log (q : ℝ) / Real.rpow (q : ℝ) s else 0) := by
  have hv : 0 < s - 1 := sub_pos.mpr hs
  have hsum := Erdos164.summable_vonMangoldt_div_rpow_if
    (v := s - 1) hv (P := fun q : ℕ ↦ q.Prime)
    (by intro q hq; exact hq.two_le)
  convert hsum using 1
  funext q
  by_cases hq : q.Prime
  · simp [hq, ArithmeticFunction.vonMangoldt_apply_prime, add_sub_cancel]
  · simp [hq]

theorem primeLogRpowSum_le_analyticSeries {s : ℝ} (hs : 1 < s) :
    primeLogRpowSum s ≤ Erdos164.analyticSeries s := by
  let f : ℕ → ℝ := fun q ↦ if hq : q.Prime then
    Real.log (q : ℝ) / Real.rpow (q : ℝ) s else 0
  let g : ℕ → ℝ := fun q ↦ if 2 ≤ q then
    ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) s else 0
  have hf : Summable f := by
    simpa [f] using summable_primeLogRpowSum hs
  have hg : Summable g := by
    have h := Erdos164.summable_vonMangoldt_div_rpow_if
      (v := s - 1) (sub_pos.mpr hs) (P := fun q : ℕ ↦ 2 ≤ q)
      (by intro q hq; exact hq)
    simpa [g, add_sub_cancel] using h
  have hfg : ∀ q, f q ≤ g q := by
    intro q
    by_cases hq : q.Prime
    · simp [f, g, hq, hq.two_le,
        ArithmeticFunction.vonMangoldt_apply_prime]
    · rw [show f q = 0 by simp [f, hq]]
      dsimp [g]
      split_ifs
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (by positivity) _)
      · exact le_rfl
  have hsum := Summable.tsum_le_tsum hfg hf hg
  rw [Erdos164.analyticSeries_eq_tsum_nat hs]
  change primeLogRpowSum s ≤ ∑' q : ℕ, g q
  rw [show primeLogRpowSum s = ∑' q : ℕ, f q by rfl]
  exact hsum

theorem summable_primeRpowTail {Q : ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (fun q : ℕ ↦
      if Q < q ∧ q.Prime then (Real.rpow (q : ℝ) s)⁻¹ else 0) := by
  have hfull : Summable (fun q : ℕ ↦ (Real.rpow (q : ℝ) s)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hs
  exact Summable.of_nonneg_of_le
    (fun q ↦ by
      split_ifs
      · exact inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
      · exact le_rfl)
    (fun q ↦ by
      split_ifs
      · exact le_rfl
      · exact inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
    hfull

theorem summable_eulerLogNat {M : ℕ}
    (chi : DirichletCharacter ℂ M) {s : ℝ} (hs : 1 < s) :
    Summable (eulerLogNat chi s) := by
  have hbase := summable_primeRpowTail (Q := 0) hs
  have hmajor : Summable (fun q : ℕ ↦
      (3 / 2 : ℝ) *
        (if q.Prime then (Real.rpow (q : ℝ) s)⁻¹ else 0)) := by
    have heq : (fun q : ℕ ↦
        (if 0 < q ∧ q.Prime then
          (Real.rpow (q : ℝ) s)⁻¹ else 0)) =
        (fun q : ℕ ↦
          if q.Prime then (Real.rpow (q : ℝ) s)⁻¹ else 0) := by
      funext q
      by_cases hq : q.Prime
      · simp [hq, hq.pos]
      · simp [hq]
    rw [heq] at hbase
    exact hbase.mul_left (3 / 2 : ℝ)
  exact Summable.of_norm_bounded hmajor
    (fun q ↦ norm_eulerLogNat_le chi hs q)

noncomputable def eulerLogTail {M : ℕ}
    (chi : DirichletCharacter ℂ M) (Q : ℕ) (s : ℝ) : ℂ :=
  ∑' q : ℕ, if Q < q then eulerLogNat chi s q else 0

theorem summable_norm_eulerLogTail {M : ℕ}
    (chi : DirichletCharacter ℂ M) {Q : ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (fun q : ℕ ↦
      ‖if Q < q then eulerLogNat chi s q else 0‖) := by
  have hmajor : Summable (fun q : ℕ ↦
      (3 / 2 : ℝ) *
        (if Q < q ∧ q.Prime then
          (Real.rpow (q : ℝ) s)⁻¹ else 0)) :=
    (summable_primeRpowTail (Q := Q) hs).mul_left (3 / 2 : ℝ)
  apply Summable.of_nonneg_of_le
    (fun q ↦ norm_nonneg _)
    (fun q ↦ ?_)
    hmajor
  by_cases hqQ : Q < q
  · by_cases hq : q.Prime
    · rw [if_pos hqQ, if_pos ⟨hqQ, hq⟩]
      simpa [hq] using norm_eulerLogNat_le chi hs q
    · rw [if_pos hqQ, if_neg (by simp [hq])]
      simp [eulerLogNat, hq]
  · simp [hqQ]

theorem norm_eulerLogTail_le {M : ℕ}
    (chi : DirichletCharacter ℂ M) {Q : ℕ} {s : ℝ} (hs : 1 < s) :
    ‖eulerLogTail chi Q s‖ ≤ (3 / 2 : ℝ) * primeRpowTail Q s := by
  have hnorm := summable_norm_eulerLogTail chi (Q := Q) hs
  have hmajor : Summable (fun q : ℕ ↦
      (3 / 2 : ℝ) *
        (if Q < q ∧ q.Prime then
          (Real.rpow (q : ℝ) s)⁻¹ else 0)) :=
    (summable_primeRpowTail (Q := Q) hs).mul_left (3 / 2 : ℝ)
  calc
    ‖eulerLogTail chi Q s‖ ≤
        ∑' q : ℕ, ‖if Q < q then eulerLogNat chi s q else 0‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, (3 / 2 : ℝ) *
        (if Q < q ∧ q.Prime then
          (Real.rpow (q : ℝ) s)⁻¹ else 0) := by
      exact hnorm.tsum_mono hmajor (fun q ↦ by
        change ‖if Q < q then eulerLogNat chi s q else 0‖ ≤
          (3 / 2 : ℝ) *
            (if Q < q ∧ q.Prime then
              (Real.rpow (q : ℝ) s)⁻¹ else 0)
        by_cases hqQ : Q < q
        · by_cases hq : q.Prime
          · rw [if_pos hqQ, if_pos ⟨hqQ, hq⟩]
            simpa [hq] using norm_eulerLogNat_le chi hs q
          · rw [if_pos hqQ, if_neg (by simp [hq])]
            simp [eulerLogNat, hq]
        · simp [hqQ])
    _ = (3 / 2 : ℝ) * primeRpowTail Q s := by
      rw [tsum_mul_left]
      rfl

noncomputable def eulerLogFinite {M : ℕ}
    (chi : DirichletCharacter ℂ M) (Q : ℕ) (s : ℝ) : ℂ :=
  ∑ q ∈ Nat.primesLE Q, eulerLogNat chi s q

theorem tsum_eulerLogNat_eq_finite_add_tail {M : ℕ}
    (chi : DirichletCharacter ℂ M) {Q : ℕ} {s : ℝ} (hs : 1 < s) :
    (∑' q : ℕ, eulerLogNat chi s q) =
      eulerLogFinite chi Q s + eulerLogTail chi Q s := by
  let f : ℕ → ℂ := eulerLogNat chi s
  let lo : ℕ → ℂ := fun q ↦ if q ≤ Q then f q else 0
  let hi : ℕ → ℂ := fun q ↦ if Q < q then f q else 0
  have hf : Summable f := summable_eulerLogNat chi hs
  have hlo : Summable lo := by
    have heq : lo = {q : ℕ | q ≤ Q}.indicator f := by
      funext q
      by_cases hq : q ≤ Q <;> simp [lo, Set.indicator, hq]
    rw [heq]
    exact hf.indicator {q : ℕ | q ≤ Q}
  have hhi : Summable hi := by
    have heq : hi = {q : ℕ | Q < q}.indicator f := by
      funext q
      by_cases hq : Q < q <;> simp [hi, Set.indicator, hq]
    rw [heq]
    exact hf.indicator {q : ℕ | Q < q}
  have hpoint : f = fun q ↦ lo q + hi q := by
    funext q
    dsimp [lo, hi]
    by_cases hq : q ≤ Q
    · simp [hq, not_lt_of_ge hq]
    · simp [hq, lt_of_not_ge hq]
  have hloSum : (∑' q : ℕ, lo q) = eulerLogFinite chi Q s := by
    rw [tsum_eq_sum (s := Nat.primesLE Q)]
    · unfold eulerLogFinite
      apply Finset.sum_congr rfl
      intro q hq
      simp [lo, f, (Nat.mem_primesLE.mp hq).1]
    · intro q hq
      by_cases hqQ : q ≤ Q
      · have hnprime : ¬ q.Prime := by
          intro hprime
          exact hq (Nat.mem_primesLE.mpr ⟨hqQ, hprime⟩)
        simp [lo, f, eulerLogNat, hqQ, hnprime]
      · simp [lo, hqQ]
  calc
    (∑' q : ℕ, eulerLogNat chi s q) = ∑' q : ℕ, f q := rfl
    _ = ∑' q : ℕ, (lo q + hi q) := by rw [hpoint]
    _ = (∑' q : ℕ, lo q) + ∑' q : ℕ, hi q := hlo.tsum_add hhi
    _ = eulerLogFinite chi Q s + eulerLogTail chi Q s := by
      rw [hloSum]
      rfl

theorem exp_tsum_eulerLogNat_eq_LFunction {M : ℕ} [NeZero M]
    (chi : DirichletCharacter ℂ M) {s : ℝ} (hs : 1 < s) :
    Complex.exp (∑' q : ℕ, eulerLogNat chi s q) =
      DirichletCharacter.LFunction chi (s : ℂ) := by
  have hsupport : Function.support (eulerLogNat chi s) ⊆
      {q : ℕ | q.Prime} := by
    intro q hq
    by_contra hprime
    have hnprime : ¬ q.Prime := by simpa using hprime
    exact hq (by simp [eulerLogNat, hnprime])
  have hsub := tsum_subtype_eq_of_support_subset hsupport
  have hsum :
      (∑' q : Nat.Primes,
          -Complex.log
            (1 - chi (q : ℕ) * ((q : ℕ) : ℂ) ^ (-(s : ℂ)))) =
        ∑' q : ℕ, eulerLogNat chi s q := by
    calc
      (∑' q : Nat.Primes,
          -Complex.log
            (1 - chi (q : ℕ) * ((q : ℕ) : ℂ) ^ (-(s : ℂ)))) =
          ∑' q : Nat.Primes, eulerLogNat chi s q := by
        apply tsum_congr
        intro q
        simp [eulerLogNat, q.property]
      _ = ∑' q : ℕ, eulerLogNat chi s q := hsub
  have hsC : 1 < ((s : ℂ)).re := by simpa using hs
  calc
    Complex.exp (∑' q : ℕ, eulerLogNat chi s q) =
        Complex.exp (∑' q : Nat.Primes,
          -Complex.log
            (1 - chi (q : ℕ) * ((q : ℕ) : ℂ) ^ (-(s : ℂ)))) := by
      rw [hsum]
    _ = L (fun n : ℕ ↦ chi n) (s : ℂ) :=
      DirichletCharacter.LSeries_eulerProduct_exp_log
        (s := (s : ℂ)) chi hsC
    _ = DirichletCharacter.LFunction chi (s : ℂ) :=
      (DirichletCharacter.LFunction_eq_LSeries chi hsC).symm

theorem primeRpowTail_le {Q : ℕ} {s : ℝ} (hQ : 2 ≤ Q) (hs : 1 < s) :
    primeRpowTail Q s ≤
      (Real.log (Q : ℝ))⁻¹ * Erdos164.analyticSeries s := by
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have htail := summable_primeRpowTail (Q := Q) hs
  have hlogsum := (summable_primeLogRpowSum hs).mul_left
    (Real.log (Q : ℝ))⁻¹
  have hpoint : ∀ q : ℕ,
      (if Q < q ∧ q.Prime then (Real.rpow (q : ℝ) s)⁻¹ else 0) ≤
        (Real.log (Q : ℝ))⁻¹ *
          (if q.Prime then
            Real.log (q : ℝ) / Real.rpow (q : ℝ) s else 0) := by
    intro q
    by_cases hq : Q < q ∧ q.Prime
    · have hpow : 0 < Real.rpow (q : ℝ) s :=
        Real.rpow_pos_of_pos (by exact_mod_cast hq.2.pos) _
      have hlogle : Real.log (Q : ℝ) ≤ Real.log (q : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hq.1.le)
      simp only [if_pos hq, if_pos hq.2]
      have hratio : 1 ≤ (Real.log (Q : ℝ))⁻¹ * Real.log (q : ℝ) :=
        (le_inv_mul_iff₀ hlogQ).mpr (by simpa [mul_comm] using hlogle)
      calc
        (Real.rpow (q : ℝ) s)⁻¹ =
            1 * (Real.rpow (q : ℝ) s)⁻¹ := by ring
        _ ≤ ((Real.log (Q : ℝ))⁻¹ * Real.log (q : ℝ)) *
            (Real.rpow (q : ℝ) s)⁻¹ :=
          mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr hpow.le)
        _ = (Real.log (Q : ℝ))⁻¹ *
            (Real.log (q : ℝ) / Real.rpow (q : ℝ) s) := by ring
    · simp only [if_neg hq]
      by_cases hprime : q.Prime
      · simp only [if_pos hprime]
        exact mul_nonneg (inv_nonneg.mpr hlogQ.le)
          (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le))
            (Real.rpow_nonneg (by positivity) _))
      · simp [hprime]
  unfold primeRpowTail
  calc
    (∑' q : ℕ,
        if Q < q ∧ q.Prime then (Real.rpow (q : ℝ) s)⁻¹ else 0) ≤
        ∑' q : ℕ, (Real.log (Q : ℝ))⁻¹ *
          (if q.Prime then
            Real.log (q : ℝ) / Real.rpow (q : ℝ) s else 0) :=
      Summable.tsum_le_tsum hpoint htail hlogsum
    _ = (Real.log (Q : ℝ))⁻¹ * primeLogRpowSum s := by
      rw [tsum_mul_left]
      rfl
    _ ≤ (Real.log (Q : ℝ))⁻¹ * Erdos164.analyticSeries s :=
      mul_le_mul_of_nonneg_left (primeLogRpowSum_le_analyticSeries hs)
        (inv_nonneg.mpr hlogQ.le)

noncomputable def shiftedEulerExponent (Q : ℕ) : ℝ :=
  1 + 4 / Real.log (Q : ℝ)

theorem one_lt_shiftedEulerExponent {Q : ℕ} (hQ : 2 ≤ Q) :
    1 < shiftedEulerExponent Q := by
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  unfold shiftedEulerExponent
  have hdiv : 0 < 4 / Real.log (Q : ℝ) :=
    div_pos (by norm_num) hlogQ
  linarith

theorem primeRpowTail_shiftedEulerExponent_le {Q : ℕ} (hQ : 2 ≤ Q) :
    primeRpowTail Q (shiftedEulerExponent Q) ≤ (1 : ℝ) / 4 := by
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hs : 1 < shiftedEulerExponent Q := one_lt_shiftedEulerExponent hQ
  calc
    primeRpowTail Q (shiftedEulerExponent Q) ≤
        (Real.log (Q : ℝ))⁻¹ *
          Erdos164.analyticSeries (shiftedEulerExponent Q) :=
      primeRpowTail_le hQ hs
    _ ≤ (Real.log (Q : ℝ))⁻¹ *
        (2 / ((shiftedEulerExponent Q) ^ 2 - 1)) :=
      mul_le_mul_of_nonneg_left
        (Erdos164.analyticSeries_le_two_div_sq_sub_one hs)
        (inv_nonneg.mpr hlogQ.le)
    _ = Real.log (Q : ℝ) /
        (4 * (Real.log (Q : ℝ) + 2)) := by
      unfold shiftedEulerExponent
      have hlog_ne : Real.log (Q : ℝ) ≠ 0 := hlogQ.ne'
      have hlog_add_ne : Real.log (Q : ℝ) + 2 ≠ 0 := by
        nlinarith
      have hsq :
          (1 + 4 / Real.log (Q : ℝ)) ^ 2 - 1 =
            8 * (Real.log (Q : ℝ) + 2) /
              (Real.log (Q : ℝ)) ^ 2 := by
        field_simp [hlog_ne]
        <;> ring
      rw [hsq]
      field_simp [hlog_ne, hlog_add_ne]
      <;> ring
    _ ≤ (1 : ℝ) / 4 := by
      apply (div_le_div_iff₀ (by positivity)
        (show (0 : ℝ) < 4 by norm_num)).mpr
      nlinarith

theorem exp_eulerLogFinite_re_lower_shifted {M : ℕ} [NeZero M]
    (chi : DirichletCharacter ℂ M) {Q : ℕ} (hQ : 2 ≤ Q) :
    Real.exp (-(3 / 8 : ℝ)) *
        ‖DirichletCharacter.LFunction chi (shiftedEulerExponent Q : ℂ)‖ ≤
      Real.exp (eulerLogFinite chi Q (shiftedEulerExponent Q)).re := by
  have hs : 1 < shiftedEulerExponent Q := one_lt_shiftedEulerExponent hQ
  have htail0 := norm_eulerLogTail_le chi (Q := Q) hs
  have htail : ‖eulerLogTail chi Q (shiftedEulerExponent Q)‖ ≤
      (3 / 8 : ℝ) := by
    calc
      ‖eulerLogTail chi Q (shiftedEulerExponent Q)‖ ≤
          (3 / 2 : ℝ) *
            primeRpowTail Q (shiftedEulerExponent Q) := htail0
      _ ≤ (3 / 2 : ℝ) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (primeRpowTail_shiftedEulerExponent_le hQ) (by norm_num)
      _ = (3 / 8 : ℝ) := by norm_num
  have htailRe :
      (eulerLogTail chi Q (shiftedEulerExponent Q)).re ≤ (3 / 8 : ℝ) :=
    Complex.re_le_norm _ |>.trans htail
  have hEuler := exp_tsum_eulerLogNat_eq_LFunction chi hs
  rw [tsum_eulerLogNat_eq_finite_add_tail chi hs] at hEuler
  have hnorm := congrArg norm hEuler
  rw [Complex.norm_exp] at hnorm
  have hupper :
      ‖DirichletCharacter.LFunction chi (shiftedEulerExponent Q : ℂ)‖ ≤
        Real.exp (eulerLogFinite chi Q (shiftedEulerExponent Q)).re *
          Real.exp (3 / 8 : ℝ) := by
    rw [← hnorm, Complex.add_re, Real.exp_add]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr htailRe) (Real.exp_pos _).le
  rw [Real.exp_neg]
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos (3 / 8 : ℝ))).2 hupper

theorem abs_eulerLogFinite_re_sub_quadraticCharRpowSum_le
    {p Q : ℕ} [Fact p.Prime] {s : ℝ} (hs : 1 < s) :
    |(eulerLogFinite (complexQuadraticChar p) Q s).re -
        quadraticCharRpowSum p Q s| ≤ Erdos469.naturalSquareSeries := by
  let main : ℕ → ℝ := fun q ↦
    quadraticCharReal p q * (Real.rpow (q : ℝ) s)⁻¹
  have heq :
      eulerLogFinite (complexQuadraticChar p) Q s -
          (quadraticCharRpowSum p Q s : ℂ) =
        ∑ q ∈ Nat.primesLE Q,
          (eulerLogNat (complexQuadraticChar p) s q - (main q : ℂ)) := by
    unfold eulerLogFinite quadraticCharRpowSum
    rw [Finset.sum_sub_distrib]
    congr 1
    simp [main]
  have hnorm :
      ‖eulerLogFinite (complexQuadraticChar p) Q s -
          (quadraticCharRpowSum p Q s : ℂ)‖ ≤
        ∑ q ∈ Nat.primesLE Q, (q : ℝ)⁻¹ ^ 2 := by
    rw [heq]
    calc
      ‖∑ q ∈ Nat.primesLE Q,
          (eulerLogNat (complexQuadraticChar p) s q - (main q : ℂ))‖ ≤
          ∑ q ∈ Nat.primesLE Q,
            ‖eulerLogNat (complexQuadraticChar p) s q - (main q : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ q ∈ Nat.primesLE Q, (q : ℝ)⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hqprime := Nat.prime_of_mem_primesLE hq
        have hlocal := norm_eulerLogNat_sub_quadraticMain_le
          (p := p) (q := q) (s := s) hqprime hs
        have hbase : (1 : ℝ) ≤ q := by
          exact_mod_cast hqprime.one_le
        have hrpow : (q : ℝ) ≤ Real.rpow (q : ℝ) s := by
          simpa using Real.rpow_le_rpow_of_exponent_le hbase hs.le
        have hinv : (Real.rpow (q : ℝ) s)⁻¹ ≤ (q : ℝ)⁻¹ := by
          exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _)
            (by positivity)).2 hrpow
        have hsquare := mul_self_le_mul_self
          (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) hinv
        dsimp [main]
        change ‖eulerLogNat (complexQuadraticChar p) s q -
            (quadraticCharReal p q *
              (Real.rpow (q : ℝ) s)⁻¹ : ℝ)‖ ≤ (q : ℝ)⁻¹ ^ 2
        exact hlocal.trans (by simpa [pow_two] using hsquare)
  have hre :
      (eulerLogFinite (complexQuadraticChar p) Q s).re -
          quadraticCharRpowSum p Q s =
        (eulerLogFinite (complexQuadraticChar p) Q s -
          (quadraticCharRpowSum p Q s : ℂ)).re := by
    simp
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans
    (hnorm.trans (finite_sum_inv_sq_le_naturalSquareSeries (Nat.primesLE Q)))

theorem abs_quadraticCharReal_le_one
    (p q : ℕ) [Fact p.Prime] : |quadraticCharReal p q| ≤ 1 := by
  have h := (complexQuadraticChar p).norm_le_one q
  rw [complexQuadraticChar_nat_eq_ofReal, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

theorem inv_sub_inv_rpow_le_log_mul
    {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 1 ≤ s) :
    (q : ℝ)⁻¹ - (Real.rpow (q : ℝ) s)⁻¹ ≤
      (s - 1) * Real.log (q : ℝ) * (q : ℝ)⁻¹ := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  let t : ℝ := (s - 1) * Real.log (q : ℝ)
  have ht : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hs) hlog
  have hexp : 1 - Real.exp (-t) ≤ t := by
    linarith [Real.add_one_le_exp (-t)]
  have hinvq : (q : ℝ)⁻¹ = Real.exp (-Real.log (q : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hqpos]
  have hinvrpow : (Real.rpow (q : ℝ) s)⁻¹ =
      Real.exp (-Real.log (q : ℝ)) * Real.exp (-t) := by
    rw [show Real.rpow (q : ℝ) s =
        Real.exp (Real.log (q : ℝ) * s) by
      exact Real.rpow_def_of_pos hqpos s]
    rw [← Real.exp_neg]
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  rw [hinvq, hinvrpow]
  have hmul := mul_le_mul_of_nonneg_left hexp
    (Real.exp_pos (-Real.log (q : ℝ))).le
  dsimp [t] at hmul ⊢
  rw [← hinvq] at hmul
  nlinarith

noncomputable def quadraticCharReciprocalSum
    (p Q : ℕ) [Fact p.Prime] : ℝ :=
  ∑ q ∈ Nat.primesLE Q, quadraticCharReal p q * (q : ℝ)⁻¹

theorem abs_quadraticCharReciprocalSum_sub_rpowSum_le
    {p Q : ℕ} [Fact p.Prime] {s : ℝ} (hs : 1 ≤ s) :
    |quadraticCharReciprocalSum p Q - quadraticCharRpowSum p Q s| ≤
      (s - 1) * BoundedGaps.Maynard.primeLogHarmonicSum Q := by
  unfold quadraticCharReciprocalSum quadraticCharRpowSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ q ∈ Nat.primesLE Q,
        (quadraticCharReal p q * (q : ℝ)⁻¹ -
          quadraticCharReal p q * (Real.rpow (q : ℝ) s)⁻¹)| ≤
        ∑ q ∈ Nat.primesLE Q,
          |quadraticCharReal p q * (q : ℝ)⁻¹ -
            quadraticCharReal p q * (Real.rpow (q : ℝ) s)⁻¹| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Nat.primesLE Q,
        (s - 1) * (Real.log q * (q : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqprime := Nat.prime_of_mem_primesLE hq
      have hdiff0 : 0 ≤ (q : ℝ)⁻¹ -
          (Real.rpow (q : ℝ) s)⁻¹ := by
        have hrpow : (q : ℝ) ≤ Real.rpow (q : ℝ) s := by
          simpa using Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast hqprime.one_le : (1 : ℝ) ≤ q) hs
        exact sub_nonneg.mpr ((inv_le_inv₀
          (Real.rpow_pos_of_pos (by exact_mod_cast hqprime.pos) _)
          (by exact_mod_cast hqprime.pos)).2 hrpow)
      rw [← mul_sub, abs_mul, abs_of_nonneg hdiff0]
      calc
        |quadraticCharReal p q| *
            ((q : ℝ)⁻¹ - (Real.rpow (q : ℝ) s)⁻¹) ≤
            1 * ((q : ℝ)⁻¹ - (Real.rpow (q : ℝ) s)⁻¹) :=
          mul_le_mul_of_nonneg_right (abs_quadraticCharReal_le_one p q) hdiff0
        _ ≤ (s - 1) * Real.log (q : ℝ) * (q : ℝ)⁻¹ :=
          by simpa using inv_sub_inv_rpow_le_log_mul hqprime.one_le hs
        _ = (s - 1) * (Real.log q * (q : ℝ)⁻¹) := by ring
    _ = (s - 1) * BoundedGaps.Maynard.primeLogHarmonicSum Q := by
      rw [← Finset.mul_sum]
      unfold BoundedGaps.Maynard.primeLogHarmonicSum
      rfl

theorem eventually_abs_quadraticCharReciprocalSum_sub_shifted_le
    (p : ℕ) [Fact p.Prime] :
    ∀ᶠ Q : ℕ in atTop,
      |quadraticCharReciprocalSum p Q -
          quadraticCharRpowSum p Q (shiftedEulerExponent Q)| ≤ 8 := by
  obtain ⟨C, hC⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  have hlogTendsto : Tendsto (fun Q : ℕ ↦ Real.log (Q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hClog : ∀ᶠ Q : ℕ in atTop, C ≤ Real.log (Q : ℝ) :=
    hlogTendsto.eventually (eventually_ge_atTop C)
  filter_upwards [hClog, eventually_ge_atTop 2] with Q hCQ hQ
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hmass : BoundedGaps.Maynard.primeLogHarmonicSum Q ≤
      Real.log (Q : ℝ) + C := by
    have habs := hC Q
    linarith [le_abs_self
      (BoundedGaps.Maynard.primeLogHarmonicSum Q - Real.log (Q : ℝ))]
  have hbase := abs_quadraticCharReciprocalSum_sub_rpowSum_le
    (p := p) (Q := Q) (s := shiftedEulerExponent Q)
    (one_lt_shiftedEulerExponent hQ).le
  calc
    |quadraticCharReciprocalSum p Q -
        quadraticCharRpowSum p Q (shiftedEulerExponent Q)| ≤
        (shiftedEulerExponent Q - 1) *
          BoundedGaps.Maynard.primeLogHarmonicSum Q := hbase
    _ ≤ (4 / Real.log (Q : ℝ)) *
        (Real.log (Q : ℝ) + C) := by
      unfold shiftedEulerExponent
      rw [add_sub_cancel_left]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ 8 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hlogQ).2
      nlinarith

theorem tendsto_shiftedEulerExponent :
    Tendsto shiftedEulerExponent atTop (nhds 1) := by
  have hlog : Tendsto (fun Q : ℕ ↦ Real.log (Q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun Q : ℕ ↦ (Real.log (Q : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hlog
  have hmul : Tendsto (fun Q : ℕ ↦ (4 : ℝ) * (Real.log (Q : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  change Tendsto (fun Q : ℕ ↦ 1 + 4 / Real.log (Q : ℝ)) atTop (nhds 1)
  simpa only [div_eq_mul_inv, add_zero] using
    tendsto_const_nhds.add hmul

theorem tendsto_complexQuadraticChar_LFunction_shifted
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    Tendsto
      (fun Q : ℕ ↦
        DirichletCharacter.LFunction (complexQuadraticChar p)
          (shiftedEulerExponent Q : ℂ))
      atTop
      (nhds (DirichletCharacter.LFunction (complexQuadraticChar p) 1)) := by
  have hcont :=
    (DirichletCharacter.differentiableAt_LFunction
      (complexQuadraticChar p) 1
      (Or.inr (complexQuadraticChar_ne_one hp4))).continuousAt
  exact hcont.tendsto.comp
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_shiftedEulerExponent)

theorem eventually_complexQuadraticChar_LFunction_shifted_norm_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      ‖DirichletCharacter.LFunction (complexQuadraticChar p)
          (shiftedEulerExponent Q : ℂ)‖ ≥
        (1 / 2 : ℝ) *
          ‖DirichletCharacter.LFunction (complexQuadraticChar p) 1‖ := by
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.2 hpR
  have hLpos : 0 <
      ‖DirichletCharacter.LFunction (complexQuadraticChar p) 1‖ := by
    exact lt_of_lt_of_le
      (div_pos Real.pi_pos (mul_pos hpR hsqrt))
      (complexQuadraticChar_LFunction_one_norm_lower hp4)
  have hnorm :=
    (tendsto_complexQuadraticChar_LFunction_shifted hp4).norm
  have hhalf :
      (1 / 2 : ℝ) *
          ‖DirichletCharacter.LFunction (complexQuadraticChar p) 1‖ <
        ‖DirichletCharacter.LFunction (complexQuadraticChar p) 1‖ := by
    nlinarith
  filter_upwards [hnorm.eventually (Ioi_mem_nhds hhalf)] with Q hQ
  exact hQ.le

noncomputable def quadraticCharEulerLowerConstant : ℝ :=
  Real.exp (-(Erdos469.naturalSquareSeries + 8 + 3 / 8)) *
    (Real.pi / 2)

theorem quadraticCharEulerLowerConstant_pos :
    0 < quadraticCharEulerLowerConstant := by
  unfold quadraticCharEulerLowerConstant
  positivity

theorem eventually_exp_quadraticCharReciprocalSum_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      quadraticCharEulerLowerConstant /
          ((p : ℝ) * Real.sqrt p) ≤
        Real.exp (quadraticCharReciprocalSum p Q) := by
  have hL := eventually_complexQuadraticChar_LFunction_shifted_norm_lower hp4
  have hshift := eventually_abs_quadraticCharReciprocalSum_sub_shifted_le p
  filter_upwards [hL, hshift, eventually_ge_atTop 2] with Q hLQ hshiftQ hQ
  have hEuler := exp_eulerLogFinite_re_lower_shifted
    (complexQuadraticChar p) hQ
  have hTaylor := abs_eulerLogFinite_re_sub_quadraticCharRpowSum_le
    (p := p) (Q := Q) (one_lt_shiftedEulerExponent hQ)
  have hLone := complexQuadraticChar_LFunction_one_norm_lower hp4
  have hlogLower :
      (eulerLogFinite (complexQuadraticChar p) Q
          (shiftedEulerExponent Q)).re -
          Erdos469.naturalSquareSeries - 8 ≤
        quadraticCharReciprocalSum p Q := by
    have hTaylorLower :
        (eulerLogFinite (complexQuadraticChar p) Q
            (shiftedEulerExponent Q)).re -
            Erdos469.naturalSquareSeries ≤
          quadraticCharRpowSum p Q (shiftedEulerExponent Q) := by
      linarith [le_of_abs_le hTaylor]
    have hshiftLower :
        quadraticCharRpowSum p Q (shiftedEulerExponent Q) - 8 ≤
          quadraticCharReciprocalSum p Q := by
      linarith [neg_le_of_abs_le hshiftQ]
    linarith
  have hLshift :
      (1 / 2 : ℝ) *
          (Real.pi / ((p : ℝ) * Real.sqrt p)) ≤
        ‖DirichletCharacter.LFunction (complexQuadraticChar p)
          (shiftedEulerExponent Q : ℂ)‖ := by
    exact (mul_le_mul_of_nonneg_left hLone (by norm_num)).trans hLQ
  calc
    quadraticCharEulerLowerConstant /
          ((p : ℝ) * Real.sqrt p) =
        Real.exp (-(Erdos469.naturalSquareSeries + 8)) *
          (Real.exp (-(3 / 8 : ℝ)) *
            ((1 / 2 : ℝ) *
              (Real.pi / ((p : ℝ) * Real.sqrt p)))) := by
      unfold quadraticCharEulerLowerConstant
      rw [show -(Erdos469.naturalSquareSeries + 8 + 3 / 8) =
          -(Erdos469.naturalSquareSeries + 8) + -(3 / 8 : ℝ) by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (-(Erdos469.naturalSquareSeries + 8)) *
          (Real.exp (-(3 / 8 : ℝ)) *
            ‖DirichletCharacter.LFunction (complexQuadraticChar p)
              (shiftedEulerExponent Q : ℂ)‖) := by
      gcongr
    _ ≤ Real.exp (-(Erdos469.naturalSquareSeries + 8)) *
          Real.exp (eulerLogFinite (complexQuadraticChar p) Q
            (shiftedEulerExponent Q)).re := by
      exact mul_le_mul_of_nonneg_left hEuler (Real.exp_pos _).le
    _ = Real.exp
          ((eulerLogFinite (complexQuadraticChar p) Q
              (shiftedEulerExponent Q)).re -
            Erdos469.naturalSquareSeries - 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (quadraticCharReciprocalSum p Q) :=
      Real.exp_le_exp.mpr hlogLower

theorem quadraticCharReal_eq_legendreSym
    (p q : ℕ) [Fact p.Prime] :
    quadraticCharReal p q = (legendreSym p (q : ℤ) : ℝ) := by
  simp [quadraticCharReal, legendreSym]

noncomputable def specialRegularAllowedPrimesFinite
    (p Q : ℕ) : Finset ℕ :=
  (specialAllowedPrimesFinite p Q).filter (fun q ↦ q ≠ 2 ∧ q ≠ p)

@[simp] theorem mem_specialRegularAllowedPrimesFinite
    {p Q q : ℕ} :
    q ∈ specialRegularAllowedPrimesFinite p Q ↔
      q.Prime ∧ q ≤ Q ∧ q ≠ 2 ∧ q ≠ p ∧
        ¬ IsQuadraticObstruction (p ^ 3) q := by
  simp only [specialRegularAllowedPrimesFinite, Finset.mem_filter,
    mem_specialAllowedPrimesFinite]
  tauto

noncomputable def regularPrimesFinite (p Q : ℕ) : Finset ℕ :=
  (Nat.primesLE Q).filter (fun q ↦ q ≠ 2 ∧ q ≠ p)

noncomputable def regularPrimeReciprocalSum (p Q : ℕ) : ℝ :=
  ∑ q ∈ regularPrimesFinite p Q, (q : ℝ)⁻¹

noncomputable def regularQuadraticCharReciprocalSum
    (p Q : ℕ) [Fact p.Prime] : ℝ :=
  ∑ q ∈ regularPrimesFinite p Q,
    quadraticCharReal p q * (q : ℝ)⁻¹

noncomputable def specialRegularAllowedPrimeReciprocal
    (p Q : ℕ) : ℝ :=
  ∑ q ∈ specialRegularAllowedPrimesFinite p Q, (q : ℝ)⁻¹

theorem two_mul_specialRegularAllowedPrimeReciprocal
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) (Q : ℕ) :
    2 * specialRegularAllowedPrimeReciprocal p Q =
      regularPrimeReciprocalSum p Q +
        regularQuadraticCharReciprocalSum p Q := by
  classical
  unfold specialRegularAllowedPrimeReciprocal regularPrimeReciprocalSum
    regularQuadraticCharReciprocalSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  let R := regularPrimesFinite p Q
  have hallowed : specialRegularAllowedPrimesFinite p Q =
      R.filter (fun q ↦ ¬ IsQuadraticObstruction (p ^ 3) q) := by
    ext q
    simp only [mem_specialRegularAllowedPrimesFinite, R,
      regularPrimesFinite, Finset.mem_filter, Nat.mem_primesLE]
    tauto
  rw [hallowed, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  have hqData := Finset.mem_filter.mp hq
  have hqprime := Nat.prime_of_mem_primesLE hqData.1
  let : Fact q.Prime := ⟨hqprime⟩
  have hq2 : q ≠ 2 := hqData.2.1
  have hqp : q ≠ p := hqData.2.2
  have hpq : p ≠ q := hqp.symm
  have hiff := isQuadraticObstruction_primeCube_iff_of_ne_two
    hp4 hq2 hpq
  by_cases hobs : IsQuadraticObstruction (p ^ 3) q
  · have hleg : legendreSym p (q : ℤ) = -1 := hiff.mp hobs
    rw [if_neg (not_not.mpr hobs), quadraticCharReal_eq_legendreSym,
      hleg]
    norm_num
  · have hpnotdvd : ¬ p ∣ q := by
      intro hdvd
      exact hpq
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqprime).mp hdvd)
    have hqmod : ((q : ℤ) : ZMod p) ≠ 0 := by
      simpa [ZMod.natCast_eq_zero_iff] using hpnotdvd
    have hleg : legendreSym p (q : ℤ) = 1 := by
      rcases legendreSym.eq_one_or_neg_one p hqmod with h | h
      · exact h
      · exact False.elim (hobs (hiff.mpr h))
    rw [if_pos hobs, quadraticCharReal_eq_legendreSym, hleg]
    norm_num
    ring

theorem sum_filter_away_two_lower
    {S : Finset ℕ} {a b : ℕ} {f : ℕ → ℝ}
    (hf : ∀ q ∈ S, f q ≤ 1) :
    (∑ q ∈ S, f q) - 2 ≤
      ∑ q ∈ S.filter (fun q ↦ q ≠ a ∧ q ≠ b), f q := by
  classical
  let T := S.filter (fun q ↦ q ≠ a ∧ q ≠ b)
  let U := S.filter (fun q ↦ ¬ (q ≠ a ∧ q ≠ b))
  have hsplit : (∑ q ∈ T, f q) + ∑ q ∈ U, f q =
      ∑ q ∈ S, f q := by
    dsimp [T, U]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hUsub : U ⊆ {a, b} := by
    intro q hq
    simp only [U, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hq ⊢
    tauto
  have hUcard : U.card ≤ 2 := by
    calc
      U.card ≤ ({a, b} : Finset ℕ).card := Finset.card_le_card hUsub
      _ ≤ 2 := by
        have h := Finset.card_insert_le a ({b} : Finset ℕ)
        simpa using h
  have hUsum : (∑ q ∈ U, f q) ≤ 2 := by
    calc
      (∑ q ∈ U, f q) ≤ ∑ _q ∈ U, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact hf q (Finset.mem_filter.mp hq).1
      _ = U.card := by simp
      _ ≤ 2 := by exact_mod_cast hUcard
  change (∑ q ∈ S, f q) - 2 ≤ ∑ q ∈ T, f q
  linarith

theorem primeReciprocalSum_eq_primesLE (Q : ℕ) :
    Erdos469.primeReciprocalSum Q =
      ∑ q ∈ Nat.primesLE Q, (q : ℝ)⁻¹ := by
  unfold Erdos469.primeReciprocalSum
  apply Finset.sum_congr
  · ext q
    simp only [Erdos469.mem_primesThrough, Nat.mem_primesLE]
    tauto
  · intro q hq
    rfl

theorem regularPrimeReciprocalSum_lower (p Q : ℕ) :
    Erdos469.primeReciprocalSum Q - 2 ≤
      regularPrimeReciprocalSum p Q := by
  rw [primeReciprocalSum_eq_primesLE]
  unfold regularPrimeReciprocalSum regularPrimesFinite
  apply sum_filter_away_two_lower
  intro q hq
  have hqprime := Nat.prime_of_mem_primesLE hq
  exact (inv_le_one₀ (by exact_mod_cast hqprime.pos : (0 : ℝ) < q)).2
    (by exact_mod_cast hqprime.one_le : (1 : ℝ) ≤ q)

theorem regularQuadraticCharReciprocalSum_lower
    (p Q : ℕ) [Fact p.Prime] :
    quadraticCharReciprocalSum p Q - 2 ≤
      regularQuadraticCharReciprocalSum p Q := by
  unfold quadraticCharReciprocalSum regularQuadraticCharReciprocalSum
    regularPrimesFinite
  apply sum_filter_away_two_lower
  intro q hq
  have hqprime := Nat.prime_of_mem_primesLE hq
  have hinv : (q : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by exact_mod_cast hqprime.pos : (0 : ℝ) < q)).2
      (by exact_mod_cast hqprime.one_le : (1 : ℝ) ≤ q)
  calc
    quadraticCharReal p q * (q : ℝ)⁻¹ ≤
        |quadraticCharReal p q| * (q : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ 1 * 1 := mul_le_mul (abs_quadraticCharReal_le_one p q)
      hinv (by positivity) (by norm_num)
    _ = 1 := by norm_num

noncomputable def primeReciprocalEulerLowerConstant : ℝ :=
  Real.exp (-(Erdos469.reciprocalPrimeMertensConstant + 2))

theorem primeReciprocalEulerLowerConstant_pos :
    0 < primeReciprocalEulerLowerConstant := by
  unfold primeReciprocalEulerLowerConstant
  positivity

theorem regularPrimeReciprocalEuler_lower
    (p : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    primeReciprocalEulerLowerConstant * Real.log (Q : ℝ) ≤
      Real.exp (regularPrimeReciprocalSum p Q) := by
  have herr := Erdos469.abs_primeReciprocalSum_sub_logLog_le hQ
  have hreg := regularPrimeReciprocalSum_lower p Q
  have hlower :
      Real.log (Real.log (Q : ℝ)) -
          Erdos469.reciprocalPrimeMertensConstant - 2 ≤
        regularPrimeReciprocalSum p Q := by
    have hmain : Real.log (Real.log (Q : ℝ)) -
        Erdos469.reciprocalPrimeMertensConstant ≤
          Erdos469.primeReciprocalSum Q := by
      linarith [neg_le_of_abs_le herr]
    linarith
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  calc
    primeReciprocalEulerLowerConstant * Real.log (Q : ℝ) =
        Real.exp (Real.log (Real.log (Q : ℝ)) -
          Erdos469.reciprocalPrimeMertensConstant - 2) := by
      unfold primeReciprocalEulerLowerConstant
      rw [show Real.log (Real.log (Q : ℝ)) -
          Erdos469.reciprocalPrimeMertensConstant - 2 =
        -(Erdos469.reciprocalPrimeMertensConstant + 2) +
          Real.log (Real.log (Q : ℝ)) by ring,
        Real.exp_add, Real.exp_log hlogQ]
    _ ≤ Real.exp (regularPrimeReciprocalSum p Q) :=
      Real.exp_le_exp.mpr hlower

theorem eventually_exp_quadraticCharReciprocalSum_sq_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      quadraticCharEulerLowerConstant / ((p : ℝ) ^ 2) ≤
        Real.exp (quadraticCharReciprocalSum p Q) := by
  have hbase := eventually_exp_quadraticCharReciprocalSum_lower hp4
  filter_upwards [hbase] with Q hQ
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hsqrt : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hpR.le
  have hsqrtLe : Real.sqrt (p : ℝ) ≤ p := by
    nlinarith
  have hden : (p : ℝ) * Real.sqrt p ≤ (p : ℝ) ^ 2 := by
    nlinarith
  have hconst : 0 ≤ quadraticCharEulerLowerConstant :=
    quadraticCharEulerLowerConstant_pos.le
  calc
    quadraticCharEulerLowerConstant / ((p : ℝ) ^ 2) ≤
        quadraticCharEulerLowerConstant /
          ((p : ℝ) * Real.sqrt p) := by
      exact div_le_div_of_nonneg_left hconst
        (mul_pos hpR (Real.sqrt_pos.2 hpR)) hden
    _ ≤ Real.exp (quadraticCharReciprocalSum p Q) := hQ

theorem eventually_regularQuadraticCharEuler_sq_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      Real.exp (-2) *
          (quadraticCharEulerLowerConstant / ((p : ℝ) ^ 2)) ≤
        Real.exp (regularQuadraticCharReciprocalSum p Q) := by
  have hbase := eventually_exp_quadraticCharReciprocalSum_sq_lower hp4
  filter_upwards [hbase] with Q hQ
  have hreg := regularQuadraticCharReciprocalSum_lower p Q
  calc
    Real.exp (-2) *
        (quadraticCharEulerLowerConstant / ((p : ℝ) ^ 2)) ≤
      Real.exp (-2) * Real.exp (quadraticCharReciprocalSum p Q) := by
        exact mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le
    _ = Real.exp (quadraticCharReciprocalSum p Q - 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (regularQuadraticCharReciprocalSum p Q) :=
      Real.exp_le_exp.mpr hreg

noncomputable def regularAllowedReciprocalLowerConstant : ℝ :=
  Real.sqrt (primeReciprocalEulerLowerConstant * Real.exp (-2) *
    quadraticCharEulerLowerConstant)

theorem regularAllowedReciprocalLowerConstant_pos :
    0 < regularAllowedReciprocalLowerConstant := by
  unfold regularAllowedReciprocalLowerConstant
  apply Real.sqrt_pos.2
  exact mul_pos
    (mul_pos primeReciprocalEulerLowerConstant_pos (Real.exp_pos _))
    quadraticCharEulerLowerConstant_pos

theorem eventually_exp_specialRegularAllowedPrimeReciprocal_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      regularAllowedReciprocalLowerConstant / (p : ℝ) *
          Real.sqrt (Real.log (Q : ℝ)) ≤
        Real.exp (specialRegularAllowedPrimeReciprocal p Q) := by
  have hchar := eventually_regularQuadraticCharEuler_sq_lower hp4
  filter_upwards [hchar, eventually_ge_atTop 2] with Q hcharQ hQ
  have hprime := regularPrimeReciprocalEuler_lower p hQ
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  let B : ℝ := primeReciprocalEulerLowerConstant * Real.exp (-2) *
    quadraticCharEulerLowerConstant
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos
      (mul_pos primeReciprocalEulerLowerConstant_pos (Real.exp_pos _))
      quadraticCharEulerLowerConstant_pos
  have hcharLowerNonneg : 0 ≤
      Real.exp (-2) *
        (quadraticCharEulerLowerConstant / ((p : ℝ) ^ 2)) := by
    exact mul_nonneg (Real.exp_pos _).le
      (div_nonneg quadraticCharEulerLowerConstant_pos.le (sq_nonneg _))
  have hprod :
      (primeReciprocalEulerLowerConstant * Real.log (Q : ℝ)) *
          (Real.exp (-2) *
            (quadraticCharEulerLowerConstant / ((p : ℝ) ^ 2))) ≤
        Real.exp (regularPrimeReciprocalSum p Q) *
          Real.exp (regularQuadraticCharReciprocalSum p Q) := by
    exact mul_le_mul hprime hcharQ hcharLowerNonneg (Real.exp_pos _).le
  have hleftEq :
      (regularAllowedReciprocalLowerConstant / (p : ℝ) *
          Real.sqrt (Real.log (Q : ℝ))) ^ 2 =
        (primeReciprocalEulerLowerConstant * Real.log (Q : ℝ)) *
          (Real.exp (-2) *
            (quadraticCharEulerLowerConstant / ((p : ℝ) ^ 2))) := by
    have hBsqrt : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
    have hlogsqrt : Real.sqrt (Real.log (Q : ℝ)) ^ 2 =
        Real.log (Q : ℝ) := Real.sq_sqrt hlogQ.le
    unfold regularAllowedReciprocalLowerConstant
    change (Real.sqrt B / (p : ℝ) *
        Real.sqrt (Real.log (Q : ℝ))) ^ 2 = _
    rw [mul_pow, div_pow, hBsqrt, hlogsqrt]
    dsimp [B]
    ring
  have hrightEq :
      Real.exp (regularPrimeReciprocalSum p Q) *
          Real.exp (regularQuadraticCharReciprocalSum p Q) =
        Real.exp (specialRegularAllowedPrimeReciprocal p Q) ^ 2 := by
    rw [← Real.exp_add, ← two_mul_specialRegularAllowedPrimeReciprocal hp4 Q]
    rw [two_mul, Real.exp_add]
    ring
  have hsquare :
      (regularAllowedReciprocalLowerConstant / (p : ℝ) *
          Real.sqrt (Real.log (Q : ℝ))) ^ 2 ≤
        Real.exp (specialRegularAllowedPrimeReciprocal p Q) ^ 2 := by
    rw [hleftEq, ← hrightEq]
    exact hprod
  have hleftNonneg : 0 ≤
      regularAllowedReciprocalLowerConstant / (p : ℝ) *
        Real.sqrt (Real.log (Q : ℝ)) := by
    exact mul_nonneg
      (div_nonneg regularAllowedReciprocalLowerConstant_pos.le hpR.le)
      (Real.sqrt_nonneg _)
  have hrightPos : 0 <
      Real.exp (specialRegularAllowedPrimeReciprocal p Q) := Real.exp_pos _
  nlinarith

theorem finset_reciprocal_sub_squareSeries_le_logEulerMass
    (P : Finset ℕ) :
    (∑ q ∈ P, (q : ℝ)⁻¹) - Erdos469.naturalSquareSeries ≤
      Real.log (squarefreeEulerMass P) := by
  have hsq : (∑ q ∈ P, (q : ℝ)⁻¹ ^ 2) ≤
      Erdos469.naturalSquareSeries :=
    finite_sum_inv_sq_le_naturalSquareSeries P
  have hnonzero : ∀ q ∈ P, (1 + (q : ℝ)⁻¹) ≠ 0 := by
    intro q hq
    positivity
  calc
    (∑ q ∈ P, (q : ℝ)⁻¹) - Erdos469.naturalSquareSeries ≤
        (∑ q ∈ P, (q : ℝ)⁻¹) - ∑ q ∈ P, (q : ℝ)⁻¹ ^ 2 :=
      sub_le_sub_left hsq _
    _ = ∑ q ∈ P, ((q : ℝ)⁻¹ - (q : ℝ)⁻¹ ^ 2) := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ q ∈ P, Real.log (1 + (q : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q hq
      exact log_one_add_lower1081 (by positivity)
    _ = Real.log (squarefreeEulerMass P) := by
      rw [squarefreeEulerMass, Real.log_prod hnonzero]

noncomputable def regularSquarefreeEulerLowerConstant : ℝ :=
  Real.exp (-Erdos469.naturalSquareSeries) *
    regularAllowedReciprocalLowerConstant

theorem regularSquarefreeEulerLowerConstant_pos :
    0 < regularSquarefreeEulerLowerConstant := by
  unfold regularSquarefreeEulerLowerConstant
  exact mul_pos (Real.exp_pos _) regularAllowedReciprocalLowerConstant_pos

theorem eventually_squarefreeEulerMass_regular_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      regularSquarefreeEulerLowerConstant / (p : ℝ) *
          Real.sqrt (Real.log (Q : ℝ)) ≤
        squarefreeEulerMass (specialRegularAllowedPrimesFinite p Q) := by
  have hrec := eventually_exp_specialRegularAllowedPrimeReciprocal_lower hp4
  filter_upwards [hrec] with Q hrecQ
  have hlog := finset_reciprocal_sub_squareSeries_le_logEulerMass
    (specialRegularAllowedPrimesFinite p Q)
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (squarefreeEulerMass_pos _)] at hexp
  have hfactor :
      Real.exp (-Erdos469.naturalSquareSeries) *
          Real.exp (specialRegularAllowedPrimeReciprocal p Q) ≤
        squarefreeEulerMass (specialRegularAllowedPrimesFinite p Q) := by
    rw [← Real.exp_add]
    unfold specialRegularAllowedPrimeReciprocal
    convert hexp using 1 <;> ring_nf
  unfold regularSquarefreeEulerLowerConstant
  calc
    Real.exp (-Erdos469.naturalSquareSeries) *
          regularAllowedReciprocalLowerConstant / (p : ℝ) *
          Real.sqrt (Real.log (Q : ℝ)) =
        Real.exp (-Erdos469.naturalSquareSeries) *
          (regularAllowedReciprocalLowerConstant / (p : ℝ) *
            Real.sqrt (Real.log (Q : ℝ))) := by ring
    _ ≤ Real.exp (-Erdos469.naturalSquareSeries) *
          Real.exp (specialRegularAllowedPrimeReciprocal p Q) := by
      exact mul_le_mul_of_nonneg_left hrecQ (Real.exp_pos _).le
    _ ≤ squarefreeEulerMass
          (specialRegularAllowedPrimesFinite p Q) := hfactor

theorem boundedSubsetEulerMass_mono
    {P R : Finset ℕ} (hPR : P ⊆ R) (N : ℕ) :
    boundedSubsetEulerMass P N ≤ boundedSubsetEulerMass R N := by
  classical
  unfold boundedSubsetEulerMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨fun q hq ↦ hPR (hS.1 hq), hS.2⟩
  · intro S hS hnot
    unfold subsetReciprocalWeight
    positivity

theorem specialRegularAllowedPrimesFinite_subset
    (p Q : ℕ) :
    specialRegularAllowedPrimesFinite p Q ⊆
      specialAllowedPrimesFinite p Q := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

theorem primeLogReciprocalMass_regular_le (p Q : ℕ) :
    primeLogReciprocalMass (specialRegularAllowedPrimesFinite p Q) ≤
      primeLogReciprocalMass (specialAllowedPrimesFinite p Q) := by
  unfold primeLogReciprocalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact specialRegularAllowedPrimesFinite_subset p Q
  · intro q hq hnot
    exact mul_nonneg
      (Real.log_nonneg (by exact_mod_cast
        (mem_specialAllowedPrimesFinite.mp hq).1.one_le))
      (by positivity)

theorem eventually_specialLocalReciprocal_uniform_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ N : ℕ in atTop,
      regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
          Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N := by
  have hEuler := eventually_squarefreeEulerMass_regular_lower hp4
  have hEulerSqrt := tendsto_nat_sqrt_atTop1081.eventually hEuler
  filter_upwards [hEulerSqrt,
      eventually_primeLogReciprocalMass_allowed_sqrt_le p,
      eventually_ge_atTop 16] with N hEulerN hmomentFull hN
  let P := specialRegularAllowedPrimesFinite p N.sqrt
  have hsqrt3 : 3 ≤ N.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact (mem_specialRegularAllowedPrimesFinite.mp hq).1
  have hmoment : primeLogReciprocalMass P ≤
      (3 / 4 : ℝ) * Real.log (N : ℝ) :=
    (primeLogReciprocalMass_regular_le p N.sqrt).trans hmomentFull
  have hretained := boundedSubsetEulerMass_lower_of_log_moment
    P N (3 / 4 : ℝ) hprime (by omega) (by norm_num) (by norm_num) hmoment
  have hbridge : boundedSubsetEulerMass P N ≤
      HalberstamScratch.reciprocalPartialSum
        (specialLocalIndicator p) N :=
    (boundedSubsetEulerMass_mono
      (specialRegularAllowedPrimesFinite_subset p N.sqrt) N).trans
        (boundedSubsetEulerMass_le_localReciprocal p N.sqrt N)
  have hsqrtCompare := half_sqrt_log_nat_le_sqrt_log_sqrt hN
  have hcpos := regularSquarefreeEulerLowerConstant_pos
  calc
    regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
          Real.sqrt (Real.log (N : ℝ)) ≤
        (1 / 4 : ℝ) *
          (regularSquarefreeEulerLowerConstant / (p : ℝ) *
            Real.sqrt (Real.log (N.sqrt : ℝ))) := by
      have hpR : (0 : ℝ) < p := by
        exact_mod_cast (Fact.out : p.Prime).pos
      have hmul := mul_le_mul_of_nonneg_left hsqrtCompare
        (div_nonneg hcpos.le hpR.le)
      have hmul4 := mul_le_mul_of_nonneg_left hmul
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      calc
        regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
            Real.sqrt (Real.log (N : ℝ)) =
          (1 / 4 : ℝ) *
            (regularSquarefreeEulerLowerConstant / (p : ℝ) *
              ((1 / 2 : ℝ) * Real.sqrt (Real.log (N : ℝ)))) := by
                field_simp [hpR.ne']
                <;> ring
        _ ≤ (1 / 4 : ℝ) *
            (regularSquarefreeEulerLowerConstant / (p : ℝ) *
              Real.sqrt (Real.log (N.sqrt : ℝ))) := hmul4
    _ ≤ (1 / 4 : ℝ) * squarefreeEulerMass P := by
      exact mul_le_mul_of_nonneg_left hEulerN (by norm_num)
    _ ≤ boundedSubsetEulerMass P N := by
      norm_num at hretained ⊢
      exact hretained
    _ ≤ HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N := hbridge

theorem eventually_specialLocal_logPartialSum_lower_of_reciprocal
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    {c : ℝ} (hc : 0 < c)
    (hrec : ∀ᶠ N : ℕ in atTop,
      c * Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N) :
    ∀ᶠ N : ℕ in atTop,
      (c / 32) * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.logPartialSum (specialLocalIndicator p) N := by
  have hrecSqrt := tendsto_nat_sqrt_atTop1081.eventually hrec
  have hmass := eventually_specialLocalLogMass_lower hp hp4
  rw [eventually_atTop] at hmass
  obtain ⟨Q₀, hmass⟩ := hmass
  filter_upwards [hrecSqrt, eventually_ge_atTop 16,
      tendsto_nat_sqrt_atTop1081.eventually (eventually_ge_atTop Q₀)]
      with N hrecN hN hsqrtQ₀
  have hsqrtCompare := half_sqrt_log_nat_le_sqrt_log_sqrt hN
  have hrecLower :
      (c / 2) * Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N.sqrt := by
    calc
      (c / 2) * Real.sqrt (Real.log (N : ℝ)) =
          c * ((1 / 2 : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by ring
      _ ≤ c * Real.sqrt (Real.log (N.sqrt : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtCompare hc.le
      _ ≤ HalberstamScratch.reciprocalPartialSum
          (specialLocalIndicator p) N.sqrt := hrecN
  have hsmallSub : Finset.Icc 1 N.sqrt ⊆ Finset.Icc 1 N := by
    intro m hm
    have hmI := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr
      ⟨hmI.1, hmI.2.trans (Nat.sqrt_le_self N)⟩
  have hsmallToFull :
      (∑ m ∈ Finset.Icc 1 N.sqrt,
        specialLocalIndicator p m * specialLocalLogMass p (N / m)) ≤
        ∑ m ∈ Finset.Icc 1 N,
          specialLocalIndicator p m * specialLocalLogMass p (N / m) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsmallSub
    intro m hm hnot
    exact mul_nonneg (specialLocalIndicator_nonneg p m)
      (specialLocalLogMass_nonneg p (N / m))
  have hpoint (m : ℕ) (hm : m ∈ Finset.Icc 1 N.sqrt) :
      (1 / 16 : ℝ) * (N : ℝ) *
          (specialLocalIndicator p m / (m : ℝ)) ≤
        specialLocalIndicator p m * specialLocalLogMass p (N / m) := by
    have hmI := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmI.1
    have hmN : m ≤ N := hmI.2.trans (Nat.sqrt_le_self N)
    have hqge : N.sqrt ≤ N / m := by
      apply (Nat.le_div_iff_mul_le hmpos).2
      calc
        N.sqrt * m ≤ N.sqrt * N.sqrt := Nat.mul_le_mul_left _ hmI.2
        _ ≤ N := Nat.sqrt_le N
    have hmassQ := hmass (N / m) (hsqrtQ₀.trans hqge)
    have hdiv := half_real_div_le_nat_div hmpos hmN
    have hscale :
        (1 / 16 : ℝ) * (N : ℝ) / (m : ℝ) ≤
          (1 / 8 : ℝ) * ((N / m : ℕ) : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hdiv
        (by norm_num : (0 : ℝ) ≤ 1 / 8)
      calc
        (1 / 16 : ℝ) * (N : ℝ) / (m : ℝ) =
            (1 / 8 : ℝ) * ((N : ℝ) / (2 * (m : ℝ))) := by
          field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmpos.ne']
          ring
        _ ≤ (1 / 8 : ℝ) * ((N / m : ℕ) : ℝ) := hmul
    calc
      (1 / 16 : ℝ) * (N : ℝ) *
          (specialLocalIndicator p m / (m : ℝ)) =
          specialLocalIndicator p m *
            ((1 / 16 : ℝ) * (N : ℝ) / (m : ℝ)) := by ring
      _ ≤ specialLocalIndicator p m *
          ((1 / 8 : ℝ) * ((N / m : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hscale
          (specialLocalIndicator_nonneg p m)
      _ ≤ specialLocalIndicator p m * specialLocalLogMass p (N / m) :=
        mul_le_mul_of_nonneg_left hmassQ
          (specialLocalIndicator_nonneg p m)
  have hconv := specialLocalIndicator_log_convolution p N
  rw [hconv]
  calc
    (c / 32) * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        (1 / 16 : ℝ) * (N : ℝ) *
          HalberstamScratch.reciprocalPartialSum
            (specialLocalIndicator p) N.sqrt := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrecLower hNnonneg]
    _ = ∑ m ∈ Finset.Icc 1 N.sqrt,
          (1 / 16 : ℝ) * (N : ℝ) *
            (specialLocalIndicator p m / (m : ℝ)) := by
      unfold HalberstamScratch.reciprocalPartialSum
      rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.Icc 1 N.sqrt,
          specialLocalIndicator p m * specialLocalLogMass p (N / m) :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
          specialLocalIndicator p m * specialLocalLogMass p (N / m) :=
      hsmallToFull

noncomputable def uniformSpecialLocalLowerConstant : ℝ :=
  regularSquarefreeEulerLowerConstant / 256

theorem uniformSpecialLocalLowerConstant_pos :
    0 < uniformSpecialLocalLowerConstant := by
  unfold uniformSpecialLocalLowerConstant
  exact div_pos regularSquarefreeEulerLowerConstant_pos (by norm_num)

theorem eventually_specialLocal_logPartialSum_uniform_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ N : ℕ in atTop,
      uniformSpecialLocalLowerConstant / (p : ℝ) * (N : ℝ) *
          Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.logPartialSum (specialLocalIndicator p) N := by
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hrec := eventually_specialLocalReciprocal_uniform_lower hp4
  have hc : 0 < regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) :=
    div_pos regularSquarefreeEulerLowerConstant_pos (mul_pos (by norm_num) hpR)
  have hlog := eventually_specialLocal_logPartialSum_lower_of_reciprocal
    (Fact.out : p.Prime) hp4 hc hrec
  filter_upwards [hlog] with N hN
  convert hN using 1 <;>
    unfold uniformSpecialLocalLowerConstant <;>
    field_simp [hpR.ne'] <;> ring

theorem eventually_specialLocalValues_lower_of_log
    {p : ℕ} {c : ℝ}
    (hlogLower : ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        HalberstamScratch.logPartialSum (specialLocalIndicator p) N) :
    ∀ᶠ N : ℕ in atTop,
      c * landauScale N ≤ ((specialLocalValues p N).card : ℝ) := by
  filter_upwards [hlogLower, eventually_ge_atTop 3] with N hlower hN
  have hupper := logPartialSum_le_log_mul_partialSum
    (specialLocalIndicator p) (specialLocalIndicator_nonneg p)
    (show 1 ≤ N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrtpos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlogpos
  have hsquare : Real.sqrt (Real.log (N : ℝ)) ^ 2 =
      Real.log (N : ℝ) := Real.sq_sqrt hlogpos.le
  have hcombined :
      c * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        Real.log (N : ℝ) *
          HalberstamScratch.partialSum (specialLocalIndicator p) N :=
    hlower.trans hupper
  have hcancel :
      c * (N : ℝ) ≤
        HalberstamScratch.partialSum (specialLocalIndicator p) N *
          Real.sqrt (Real.log (N : ℝ)) := by
    apply le_of_mul_le_mul_right ?_ hsqrtpos
    calc
      c * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
          Real.log (N : ℝ) *
            HalberstamScratch.partialSum (specialLocalIndicator p) N := hcombined
      _ = (HalberstamScratch.partialSum (specialLocalIndicator p) N *
            Real.sqrt (Real.log (N : ℝ))) *
              Real.sqrt (Real.log (N : ℝ)) := by
        calc
          Real.log (N : ℝ) *
              HalberstamScratch.partialSum (specialLocalIndicator p) N =
              Real.sqrt (Real.log (N : ℝ)) ^ 2 *
                HalberstamScratch.partialSum (specialLocalIndicator p) N := by
            rw [hsquare]
          _ = (HalberstamScratch.partialSum (specialLocalIndicator p) N *
                Real.sqrt (Real.log (N : ℝ))) *
                  Real.sqrt (Real.log (N : ℝ)) := by ring
  rw [specialLocalValues_card_eq_indicator_partialSum]
  unfold landauScale
  rw [show c * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) =
      (c * (N : ℝ)) / Real.sqrt (Real.log (N : ℝ)) by ring]
  exact (div_le_iff₀ hsqrtpos).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel)

theorem eventually_specialLocalValues_uniform_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ N : ℕ in atTop,
      uniformSpecialLocalLowerConstant / (p : ℝ) * landauScale N ≤
        ((specialLocalValues p N).card : ℝ) := by
  exact eventually_specialLocalValues_lower_of_log
    (eventually_specialLocal_logPartialSum_uniform_lower hp4)

end

end Erdos1081
