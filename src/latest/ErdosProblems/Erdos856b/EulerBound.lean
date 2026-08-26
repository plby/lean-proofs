import ErdosProblems.Erdos856b.PrimeEstimates

/-! # The harmonic Euler-product upper estimate -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

noncomputable def omegaWeight (u : ℝ) (m : ℕ) : ℝ := u ^ m.primeFactors.card / m

noncomputable def omegaSum (u : ℝ) (N : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 N, omegaWeight u m

theorem omegaWeight_nonneg {u : ℝ} (hu : 0 ≤ u) (m : ℕ) : 0 ≤ omegaWeight u m := by
  unfold omegaWeight
  positivity

theorem omegaWeight_one (u : ℝ) : omegaWeight u 1 = 1 := by simp [omegaWeight]

theorem omegaWeight_mul (u : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    omegaWeight u (m * n) = omegaWeight u m * omegaWeight u n := by
  by_cases hm : m = 0
  · simp [hm, omegaWeight]
  by_cases hn : n = 0
  · simp [hn, omegaWeight]
  simp only [omegaWeight, Nat.primeFactors_mul hm hn,
    Finset.card_union_of_disjoint hmn.disjoint_primeFactors, pow_add, Nat.cast_mul]
  ring

theorem omegaWeight_prime_pow (u : ℝ) {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    omegaWeight u (p ^ e) = u * ((p : ℝ)⁻¹) ^ e := by
  simp [omegaWeight, Nat.primeFactors_prime_pow he hp, div_eq_mul_inv]

theorem hasSum_omegaWeight_prime_pow (u : ℝ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun e : ℕ => omegaWeight u (p ^ e)) (1 + u / (p - 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hgeom := (hasSum_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp1)).mul_left u
  have htotal := (hasSum_ite_eq (0 : ℕ) (1 - u)).add hgeom
  convert htotal using 1
  · funext e
    by_cases he : e = 0
    · subst e
      simp [omegaWeight]
    · simp [omegaWeight_prime_pow u hp he, he]
  · have hp10 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpInv : 1 - (p : ℝ)⁻¹ ≠ 0 := by
      have := inv_lt_one_of_one_lt₀ hp1
      linarith
    field_simp
    ring

theorem omegaSum_le_eulerProduct {u : ℝ} (hu : 0 ≤ u) (N : ℕ) :
    omegaSum u N ≤ ∏ p ∈ Nat.primesLE N, (1 + u / (p - 1)) := by
  classical
  let S := Nat.primesLE N
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (omegaWeight_one u) (fun {m n} h => omegaWeight_mul u h)
    (fun {p} hp => (hasSum_omegaWeight_prime_pow u hp).summable.norm) S
  have hmem (m : ↥(Finset.Icc 1 N)) : m.val ∈ Nat.factoredNumbers S := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset (by
      have := (Finset.mem_Icc.mp m.property).1
      omega)
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_mem_primeFactors hp).trans (Finset.mem_Icc.mp m.property).2,
        Nat.prime_of_mem_primeFactors hp⟩
  let e : ↥(Finset.Icc 1 N) ↪ Nat.factoredNumbers S :=
    ⟨fun m => ⟨m.val, hmem m⟩, fun x y h => by
      apply Subtype.ext
      exact congrArg (fun m : Nat.factoredNumbers S => m.val) h⟩
  have hle := Summable.sum_le_tsum (Finset.univ.map e)
    (fun m _ => omegaWeight_nonneg hu m.val) hs.2.summable
  rw [hs.2.tsum_eq] at hle
  have hfilter : S.filter Nat.Prime = S := by
    apply Finset.filter_eq_self.mpr
    exact fun p hp => Nat.prime_of_mem_primesLE hp
  rw [hfilter] at hle
  have hprod : (∏ p ∈ S, ∑' j : ℕ, omegaWeight u (p ^ j)) =
      ∏ p ∈ S, (1 + u / (p - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact (hasSum_omegaWeight_prime_pow u (Nat.prime_of_mem_primesLE hp)).tsum_eq
  rw [hprod] at hle
  rw [Finset.sum_map] at hle
  change (∑ m : ↥(Finset.Icc 1 N), omegaWeight u m.val) ≤
    ∏ p ∈ Nat.primesLE N, (1 + u / (p - 1)) at hle
  simpa only [Finset.sum_coe_sort, omegaSum] using hle

theorem eulerProduct_le_exp_primeHarmonic {u : ℝ} (hu : 0 ≤ u) (N : ℕ) :
    (∏ p ∈ Nat.primesLE N, (1 + u / (p - 1))) ≤ exp (u * (primeHarmonic N + 1)) := by
  have herror : (∑ p ∈ Nat.primesLE N, (((p : ℝ) - 1) * p)⁻¹) ≤ 1 := by
    have h := Summable.sum_le_tsum (Nat.primesLE N) (fun p _ => my_mul_thing')
      sum_thing'_has_sum.summable
    simpa only [sum_thing'_has_sum.tsum_eq] using h
  calc
    (∏ p ∈ Nat.primesLE N, (1 + u / (p - 1))) ≤
        ∏ p ∈ Nat.primesLE N, exp (u / (p - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
        positivity
      · intro p _
        simpa [add_comm] using add_one_le_exp (u / (p - 1))
    _ = exp (∑ p ∈ Nat.primesLE N, u / (p - 1)) := (exp_sum _ _).symm
    _ ≤ exp (u * (primeHarmonic N + 1)) := by
      apply exp_le_exp.mpr
      have heq : (∑ p ∈ Nat.primesLE N, u / (p - 1)) =
          u * primeHarmonic N + u * ∑ p ∈ Nat.primesLE N, (((p : ℝ) - 1) * p)⁻¹ := by
        simp only [primeHarmonic, Nat.floor_natCast, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
        have hp0 : (p : ℝ) ≠ 0 := by positivity
        have hp10 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
      rw [heq]
      nlinarith [mul_le_mul_of_nonneg_left herror hu]

theorem omegaSum_le_exp {u : ℝ} (hu : 0 ≤ u) (N : ℕ) :
    omegaSum u N ≤ exp (u * (primeHarmonic N + 1)) :=
  (omegaSum_le_eulerProduct hu N).trans (eulerProduct_le_exp_primeHarmonic hu N)

end Erdos856b
