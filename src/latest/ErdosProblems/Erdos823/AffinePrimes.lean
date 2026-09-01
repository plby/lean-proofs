import ErdosProblems.Erdos823.Abundancy

/-!
# The affine-prime interface in Pollack's proof

The deep input is separated from the elementary arithmetic around it.  The
special forms needed for Erdős 823 are `c i * x - 1`; their admissibility is
automatic because they are all `-1` at `x = 0`.
-/

namespace Erdos823

open Filter Finset Topology
open scoped ArithmeticFunction.sigma BigOperators

noncomputable section

/-- A quantitative special case of Maynard's theorem on admissible affine
linear forms.  The lower bound on `x` encodes the required infinitude. -/
def AffinePrimePairProperty (K : ℕ) : Prop :=
  ∀ c : Fin K → ℕ,
    (∀ i, 0 < c i) → Function.Injective c →
    ∀ B : ℕ, ∃ x : ℕ, ∃ i j : Fin K,
      B < x ∧ i.val < j.val ∧
      (c i * x - 1).Prime ∧ (c j * x - 1).Prime

theorem sigma_one_apply_prime {p : ℕ} (hp : p.Prime) :
    σ 1 p = p + 1 := by
  simpa using
    (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)

/-- The logarithmic correction incurred by replacing `p+1` by `p`. -/
theorem abs_log_nat_div_succ_le_inv {p : ℕ} (hp : 0 < p) :
    |Real.log ((p : ℝ) / (p + 1 : ℕ))| ≤ 1 / (p : ℝ) := by
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsuccR : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hratio_nonneg : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) + 1) := by positivity
  have hratio_le : (p : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hsuccR]
    norm_num
  rw [abs_of_nonpos (Real.log_nonpos hratio_nonneg hratio_le)]
  rw [Real.log_div hpR.ne' hsuccR.ne']
  have hlog := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < ((p : ℝ) + 1) / (p : ℝ) by positivity)
  have hid : -(Real.log (p : ℝ) - Real.log ((p : ℝ) + 1)) =
      Real.log (((p : ℝ) + 1) / (p : ℝ)) := by
    rw [Real.log_div hsuccR.ne' hpR.ne']
    ring
  rw [hid]
  convert hlog using 1
  field_simp
  ring

/-- The elementary consequence of the affine-prime theorem used in Pollack's
closure argument.  It supplies a uniformly nontrivial, but arbitrarily small,
positive logarithmic quotient while avoiding a prescribed modulus. -/
theorem exists_small_sigma_log_pair_of_affine
    (haffine : AffinePrimePairProperty 105)
    (Q : ℕ) (hQ : 0 < Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℕ,
      0 < m ∧ 0 < n ∧ Nat.Coprime (m * n) Q ∧
      σ 1 m = σ 1 n ∧
      ε / 212 < Real.log ((m : ℝ) / (n : ℝ)) ∧
      Real.log ((m : ℝ) / (n : ℝ)) < ε := by
  let δ : ℝ := ε / 106
  let η : ℝ := δ / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have htarget (i : Fin 105) : 0 ≤ (i.val : ℝ) * δ := by positivity
  choose A hApos hAcop hAlower hAupper using
    fun i : Fin 105 ↦ exists_abundancy_approx Q hQ (htarget i) hη
  let ℓ : Fin 105 → ℝ := fun i ↦
    Real.log ((σ 1 (A i) : ℕ) / (A i : ℝ))
  let c : Fin 105 → ℕ := fun i ↦ σ 1 (A i)
  have hcpos : ∀ i, 0 < c i := by
    intro i
    exact ArithmeticFunction.sigma_pos 1 (A i) (Nat.ne_of_gt (hApos i))
  have hℓlower : ∀ i, (i.val : ℝ) * δ ≤ ℓ i := hAlower
  have hℓupper : ∀ i, ℓ i < (i.val : ℝ) * δ + η := hAupper
  have hdirect : ∀ {a b : Fin 105}, a.val < b.val → c a = c b →
      ∃ m n : ℕ,
        0 < m ∧ 0 < n ∧ Nat.Coprime (m * n) Q ∧
        σ 1 m = σ 1 n ∧
        ε / 212 < Real.log ((m : ℝ) / (n : ℝ)) ∧
        Real.log ((m : ℝ) / (n : ℝ)) < ε := by
    intro a b hab hcab
    have hAaR : (A a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hApos a))
    have hAbR : (A b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hApos b))
    have hcaR : (c a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hcpos a))
    have hcbR : (c b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hcpos b))
    have hlog : Real.log ((A a : ℝ) / (A b : ℝ)) = ℓ b - ℓ a := by
      dsimp only [ℓ, c] at hcab ⊢
      rw [Real.log_div hAaR hAbR, Real.log_div hcbR hAbR,
        Real.log_div hcaR hAaR]
      have hcabR : ((σ 1 (A a) : ℕ) : ℝ) = (σ 1 (A b) : ℕ) := by
        exact_mod_cast hcab
      rw [hcabR]
      ring
    have hdiffLower : δ - η < ℓ b - ℓ a := by
      have hval : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast hab
      nlinarith [hℓlower b, hℓupper a]
    have hdiffUpper : ℓ b - ℓ a < 104 * δ + η := by
      have ha0 : (0 : ℝ) ≤ a.val := by positivity
      have hb104 : (b.val : ℝ) ≤ 104 := by
        exact_mod_cast (show b.val ≤ 104 by omega)
      nlinarith [hℓlower a, hℓupper b]
    refine ⟨A a, A b, hApos a, hApos b, (hAcop a).mul_left (hAcop b), ?_, ?_, ?_⟩
    · exact hcab
    · rw [hlog]
      dsimp [δ, η] at hdiffLower ⊢
      linarith
    · rw [hlog]
      dsimp [δ, η] at hdiffUpper ⊢
      linarith
  by_cases hinj : Function.Injective c
  · let Amax : ℕ := univ.sup A
    obtain ⟨C : ℕ, hC⟩ := exists_nat_gt (1 / η)
    let B : ℕ := max (max Q Amax) C
    obtain ⟨x, a, b, hx, hab, hpa, hpb⟩ := haffine c hcpos hinj (B + 1)
    let p : ℕ := c a * x - 1
    let q : ℕ := c b * x - 1
    have hp : p.Prime := hpa
    have hq : q.Prime := hpb
    have hxpos : 0 < x := by omega
    have hp_add : p + 1 = c a * x := by
      dsimp only [p]
      exact Nat.sub_add_cancel (mul_pos (hcpos a) hxpos)
    have hq_add : q + 1 = c b * x := by
      dsimp only [q]
      exact Nat.sub_add_cancel (mul_pos (hcpos b) hxpos)
    have hB_le_p : B < p := by
      have hxle : x ≤ c a * x := Nat.le_mul_of_pos_left x (hcpos a)
      dsimp only [p]
      omega
    have hB_le_q : B < q := by
      have hxle : x ≤ c b * x := Nat.le_mul_of_pos_left x (hcpos b)
      dsimp only [q]
      omega
    have hQleB : Q ≤ B := by simp [B]
    have hAmaxleB : Amax ≤ B := by simp [B]
    have hCleB : C ≤ B := by simp [B]
    have hA_le_max (i : Fin 105) : A i ≤ Amax := by
      exact Finset.le_sup (s := univ) (f := A) (mem_univ i)
    have hpaA : Nat.Coprime p (A b) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have := Nat.le_of_dvd (hApos b) hdvd
      exact (not_lt_of_ge (this.trans (hA_le_max b |>.trans hAmaxleB))) hB_le_p
    have hqbA : Nat.Coprime q (A a) := by
      apply hq.coprime_iff_not_dvd.mpr
      intro hdvd
      have := Nat.le_of_dvd (hApos a) hdvd
      exact (not_lt_of_ge (this.trans (hA_le_max a |>.trans hAmaxleB))) hB_le_q
    have hpQ : Nat.Coprime p Q := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have := Nat.le_of_dvd hQ hdvd
      exact (not_lt_of_ge (this.trans hQleB)) hB_le_p
    have hqQ : Nat.Coprime q Q := by
      apply hq.coprime_iff_not_dvd.mpr
      intro hdvd
      have := Nat.le_of_dvd hQ hdvd
      exact (not_lt_of_ge (this.trans hQleB)) hB_le_q
    have hsigma : σ 1 (q * A a) = σ 1 (p * A b) := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hqbA,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hpaA,
        sigma_one_apply_prime hq, sigma_one_apply_prime hp,
        hq_add, hp_add]
      ring
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hp1R : ((p + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hq1R : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hAaR : (A a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hApos a))
    have hAbR : (A b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hApos b))
    have hcaR : (c a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hcpos a))
    have hcbR : (c b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hcpos b))
    have hcaSigmaR : ((σ 1 (A a) : ℕ) : ℝ) ≠ 0 := hcaR
    have hcbSigmaR : ((σ 1 (A b) : ℕ) : ℝ) ≠ 0 := hcbR
    have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hxpos)
    let corr : ℝ :=
      Real.log ((q : ℝ) / (q + 1 : ℕ)) -
        Real.log ((p : ℝ) / (p + 1 : ℕ))
    have hlog : Real.log (((q * A a : ℕ) : ℝ) / (p * A b : ℕ)) =
        (ℓ b - ℓ a) + corr := by
      push_cast
      dsimp only [ℓ, c, corr] at hq_add hp_add ⊢
      rw [Real.log_div (mul_ne_zero hqR hAaR) (mul_ne_zero hpR hAbR),
        Real.log_mul hqR hAaR, Real.log_mul hpR hAbR,
        Real.log_div hcbR hAbR, Real.log_div hcaR hAaR,
        Real.log_div hqR hq1R, Real.log_div hpR hp1R]
      rw [hq_add, hp_add]
      norm_num only [Nat.cast_mul]
      rw [Real.log_mul hcbSigmaR hxR,
        Real.log_mul hcaSigmaR hxR]
      ring
    have hC_lt_p : (C : ℝ) < p := by exact_mod_cast lt_of_le_of_lt (le_max_right _ C) hB_le_p
    have hC_lt_q : (C : ℝ) < q := by exact_mod_cast lt_of_le_of_lt (le_max_right _ C) hB_le_q
    have hinvP : (1 : ℝ) / p < η := by
      have hCp : 1 / η < (p : ℝ) := hC.trans hC_lt_p
      have hpRpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      rw [div_lt_iff₀ hpRpos]
      have := mul_lt_mul_of_pos_right hCp hη
      field_simp at this
      linarith
    have hinvQ : (1 : ℝ) / q < η := by
      have hCq : 1 / η < (q : ℝ) := hC.trans hC_lt_q
      have hqRpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
      rw [div_lt_iff₀ hqRpos]
      have := mul_lt_mul_of_pos_right hCq hη
      field_simp at this
      linarith
    have hcorr : |corr| < 2 * η := by
      have hpbound := abs_log_nat_div_succ_le_inv hp.pos
      have hqbound := abs_log_nat_div_succ_le_inv hq.pos
      dsimp only [corr]
      calc
        |Real.log ((q : ℝ) / (q + 1 : ℕ)) -
            Real.log ((p : ℝ) / (p + 1 : ℕ))| ≤
            |Real.log ((q : ℝ) / (q + 1 : ℕ))| +
              |Real.log ((p : ℝ) / (p + 1 : ℕ))| := abs_sub _ _
        _ < 2 * η := by linarith
    have hdiffLower : δ - η < ℓ b - ℓ a := by
      have hval : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast hab
      nlinarith [hℓlower b, hℓupper a]
    have hdiffUpper : ℓ b - ℓ a < 104 * δ + η := by
      have ha0 : (0 : ℝ) ≤ a.val := by positivity
      have hb104 : (b.val : ℝ) ≤ 104 := by
        exact_mod_cast (show b.val ≤ 104 by omega)
      nlinarith [hℓlower a, hℓupper b]
    have hcorrLower : -(2 * η) < corr := (abs_lt.1 hcorr).1
    have hcorrUpper : corr < 2 * η := (abs_lt.1 hcorr).2
    refine ⟨q * A a, p * A b, mul_pos hq.pos (hApos a),
      mul_pos hp.pos (hApos b), ?_, hsigma, ?_, ?_⟩
    · exact (hqQ.mul_left (hAcop a)).mul_left (hpQ.mul_left (hAcop b))
    · rw [hlog]
      dsimp [δ, η] at hdiffLower hcorrLower ⊢
      linarith
    · rw [hlog]
      dsimp [δ, η] at hdiffUpper hcorrUpper ⊢
      linarith
  · have hcollision : ∃ i j, i ≠ j ∧ c i = c j := by
      by_contra hnone
      apply hinj
      intro i j hij
      by_contra hne
      exact hnone ⟨i, j, hne, hij⟩
    obtain ⟨i, j, hij, hcij⟩ := hcollision
    have hijval : i.val ≠ j.val := by
      intro hval
      exact hij (Fin.ext hval)
    rcases lt_or_gt_of_ne hijval with hij' | hji'
    · exact hdirect hij' hcij
    · exact hdirect hji' hcij.symm

end

end Erdos823
