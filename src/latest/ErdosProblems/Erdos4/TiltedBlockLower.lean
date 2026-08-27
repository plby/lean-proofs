import ErdosProblems.Erdos4.TiltedGlobalCorrelation

/-! A uniform lower bound for block survival, without a Taylor expansion. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

theorem exp_neg_two_le_one_sub {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    Real.exp (-2 * a) ≤ 1 - a := by
  have hpos : 0 < 1 + 2 * a := by linarith
  calc
    _ = 1 / Real.exp (2 * a) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
    _ ≤ 1 / (1 + 2 * a) := one_div_le_one_div_of_le hpos (by
      simpa only [add_comm] using Real.add_one_le_exp (2 * a))
    _ ≤ 1 - a := by
      apply (div_le_iff₀ hpos).mpr
      nlinarith [mul_nonneg ha0 (show 0 ≤ 1 - 2 * a by linarith)]

theorem baseline_lower_exp {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (-(2 / (s : ℝ))) ≤ baseline s u := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hhalf : 1 / (s : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hsR
  have ha := atom_le_inv hs hu0 hu1
  rw [baseline_eq_one_sub_atom hs hu0]
  calc
    _ = Real.exp (-2 * (1 / (s : ℝ))) := by congr 1; ring
    _ ≤ 1 - 1 / (s : ℝ) := exp_neg_two_le_one_sub (by positivity) hhalf
    _ ≤ _ := sub_le_sub_left ha _

theorem localLaw_prob_avoid_lower (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (E : Finset (ZMod s)) {K : ℕ}
    (hE : E.card ≤ K) (hsmall : 2 * K + 1 ≤ s) :
    (if (0 : ZMod s) ∈ E then u else 1) * Real.exp (-((4 * (K : ℝ) + 2) / s)) ≤
      (localLaw s hs u hu0.le hu1).prob (fun a => a ∉ E) := by
  classical
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hD : (0 : ℝ) < s - 1 := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hK : (K : ℝ) / ((s : ℝ) - 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hD).mpr
    have hh : (2 : ℝ) * K + 1 ≤ s := by exact_mod_cast hsmall
    linarith
  have hKR : (K : ℝ) / ((s : ℝ) - 1) ≤ 2 * (K : ℝ) / s := by
    apply (div_le_div_iff₀ hD hspos).mpr
    nlinarith [mul_nonneg hK0 (show 0 ≤ (s : ℝ) - 2 by linarith)]
  have hdec : Real.exp (-(4 * (K : ℝ) / s)) ≤ 1 - (K : ℝ) / ((s : ℝ) - 1) := by
    calc
      _ ≤ Real.exp (-2 * ((K : ℝ) / ((s : ℝ) - 1))) := by
        apply Real.exp_le_exp.mpr
        calc
          _ = -2 * (2 * (K : ℝ) / s) := by ring
          _ ≤ _ := mul_le_mul_of_nonpos_left hKR (by norm_num)
      _ ≤ _ := exp_neg_two_le_one_sub (div_nonneg hK0 hD.le) hK
  have hfactor0 : 0 ≤ 1 - (K : ℝ) / ((s : ℝ) - 1) := by linarith
  have hE' : (E.card : ℝ) ≤ K := by exact_mod_cast hE
  have hpre : baseline s u * (if (0 : ZMod s) ∈ E then u else 1) *
      (1 - (K : ℝ) / ((s : ℝ) - 1)) ≤
      (localLaw s hs u hu0.le hu1).prob (fun a => a ∉ E) := by
    rw [localLaw_prob_avoid]
    by_cases hz : (0 : ZMod s) ∈ E
    · simp only [if_pos hz]
      rw [← beta_eq_baseline_mul]
      apply mul_le_mul_of_nonneg_left _ (beta_nonneg hs hu0.le)
      apply sub_le_sub_left
      apply div_le_div_of_nonneg_right _ hD.le
      linarith
    · simp only [if_neg hz, mul_one]
      have hB1 : baseline s u ≤ 1 := by
        rw [baseline_eq_one_sub_atom hs hu0.le]
        linarith [atom_nonneg hs hu0.le]
      have ha := atom_le_inv hs hu0.le hu1
      have hinv : 1 / (s : ℝ) ≤ 1 / ((s : ℝ) - 1) := one_div_le_one_div_of_le hD (by linarith)
      have hprod : (E.card : ℝ) * atom s u ≤ (K : ℝ) / ((s : ℝ) - 1) := by
        calc
          _ ≤ (K : ℝ) * (1 / ((s : ℝ) - 1)) :=
            mul_le_mul hE' (ha.trans hinv) (atom_nonneg hs hu0.le) hK0
          _ = _ := by ring
      exact (mul_le_of_le_one_left hfactor0 hB1).trans (by linarith)
  have htilt0 : 0 ≤ (if (0 : ZMod s) ∈ E then u else 1) := by split_ifs <;> positivity
  calc
    _ = (if (0 : ZMod s) ∈ E then u else 1) *
        (Real.exp (-(2 / (s : ℝ))) * Real.exp (-(4 * (K : ℝ) / s))) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ (if (0 : ZMod s) ∈ E then u else 1) *
        (baseline s u * (1 - (K : ℝ) / ((s : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (baseline_lower_exp hs hu0.le hu1) hdec (Real.exp_pos _).le (baseline_pos hs hu0.le).le) htilt0
    _ = _ := by ring
    _ ≤ _ := hpre

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem sieveLaw_block_lower (hinj : Function.Injective ell) (τ : ℝ) (hτ : 0 ≤ τ)
    (T : Finset ℕ) {K : ℕ} (hT : T.card ≤ K) (hsmall : ∀ l, 2 * K + 1 ≤ ell l)
    (hsq : Squarefree (∏ n ∈ T, n))
    (hcomplete : ∀ p ∈ (∏ n ∈ T, n).primeFactors, ∃ l, ell l = p) :
    ((∏ n ∈ T, n : ℕ) : ℝ) ^ (-τ) *
      Real.exp (-((4 * (K : ℝ) + 2) * ∑ l, 1 / (ell l : ℝ))) ≤
      (sieveLaw ell τ hτ).prob (fun a => Survives ell a T) := by
  classical
  have hprod := Finset.prod_le_prod
    (s := Finset.univ)
    (f := fun l => (if (0 : ZMod (ell l)) ∈ residues ell T l then (ell l : ℝ) ^ (-τ) else 1) *
      Real.exp (-((4 * (K : ℝ) + 2) / ell l)))
    (g := fun l => (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).prob
      (fun a => a ∉ residues ell T l))
    (fun l _ => by split_ifs <;> positivity)
    (fun l _ => localLaw_prob_avoid_lower (ell l) (Fact.out : (ell l).Prime).two_le _
      (rpow_tilt_pos (Fact.out : (ell l).Prime).two_le τ)
      (rpow_tilt_le_one (Fact.out : (ell l).Prime).two_le hτ) _
      (Finset.card_image_le.trans hT) (hsmall l))
  rw [← sieveLaw_survival_product, Finset.prod_mul_distrib, ← Real.exp_sum] at hprod
  simp only [zero_mem_residues_iff] at hprod
  rw [divisor_tilt_product ell hinj τ hsq.ne_zero hcomplete, nat_prod_rpow,
    Nat.prod_primeFactors_of_squarefree hsq] at hprod
  have heq : (∑ l, -((4 * (K : ℝ) + 2) / ell l)) =
      -((4 * (K : ℝ) + 2) * ∑ l, 1 / (ell l : ℝ)) := by
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [heq] at hprod
  exact hprod

end Erdos4.Tilted
