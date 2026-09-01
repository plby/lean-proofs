import ErdosProblems.Erdos823.AffinePrimes

/-!
# Assembly of Pollack blocks

Small equal-`sigma` blocks are chosen successively, each coprime to all
previous blocks.  Their logarithmic quotients therefore add, while
multiplicativity preserves the common divisor sum.
-/

namespace Erdos823

open Filter Finset Topology
open scoped ArithmeticFunction.sigma BigOperators

noncomputable section

structure SigmaLogBlock (Q : ℕ) (ε : ℝ) where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  coprime : Nat.Coprime (m * n) Q
  sigma_eq : σ 1 m = σ 1 n
  log_lower : ε / 212 < Real.log ((m : ℝ) / (n : ℝ))
  log_upper : Real.log ((m : ℝ) / (n : ℝ)) < ε

theorem nonempty_sigmaLogBlock
    (haffine : AffinePrimePairProperty 105)
    (Q : ℕ) (hQ : 0 < Q) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (SigmaLogBlock Q ε) := by
  obtain ⟨m, n, hm, hn, hcop, hsigma, hlower, hupper⟩ :=
    exists_small_sigma_log_pair_of_affine haffine Q hQ hε
  exact ⟨⟨m, n, hm, hn, hcop, hsigma, hlower, hupper⟩⟩

noncomputable def chosenSigmaLogBlock
    (haffine : AffinePrimePairProperty 105)
    (Q : ℕ) (hQ : 0 < Q) (ε : ℝ) (hε : 0 < ε) :
    SigmaLogBlock Q ε :=
  Classical.choice (nonempty_sigmaLogBlock haffine Q hQ ε hε)

structure SigmaAccum where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  sigma_eq : σ 1 m = σ 1 n

def SigmaAccum.one : SigmaAccum :=
  ⟨1, 1, by norm_num, by norm_num, by simp⟩

noncomputable def SigmaAccum.block
    (haffine : AffinePrimePairProperty 105) (ε : ℝ) (hε : 0 < ε)
    (s : SigmaAccum) : SigmaLogBlock (s.m * s.n) ε :=
  chosenSigmaLogBlock haffine (s.m * s.n) (mul_pos s.m_pos s.n_pos) ε hε

private theorem coprime_components
    {a b c d : ℕ} (h : Nat.Coprime (a * b) (c * d)) :
    Nat.Coprime c a ∧ Nat.Coprime d b := by
  constructor
  · exact (Nat.Coprime.of_dvd_right (dvd_mul_right a b)
      (Nat.Coprime.of_dvd_left (dvd_mul_right c d) h.symm))
  · exact (Nat.Coprime.of_dvd_right (dvd_mul_left b a)
      (Nat.Coprime.of_dvd_left (dvd_mul_left d c) h.symm))

noncomputable def SigmaAccum.step
    (haffine : AffinePrimePairProperty 105) (ε : ℝ) (hε : 0 < ε)
    (s : SigmaAccum) : SigmaAccum := by
  let b := s.block haffine ε hε
  have hcross := coprime_components b.coprime
  refine ⟨s.m * b.m, s.n * b.n, mul_pos s.m_pos b.m_pos,
    mul_pos s.n_pos b.n_pos, ?_⟩
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcross.1,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcross.2,
    s.sigma_eq, b.sigma_eq]

noncomputable def sigmaAccumSeq
    (haffine : AffinePrimePairProperty 105) (ε : ℝ) (hε : 0 < ε) :
    ℕ → SigmaAccum
  | 0 => SigmaAccum.one
  | j + 1 => (sigmaAccumSeq haffine ε hε j).step haffine ε hε

theorem sigmaAccumSeq_log_succ
    (haffine : AffinePrimePairProperty 105) (ε : ℝ) (hε : 0 < ε)
    (j : ℕ) :
    Real.log (((sigmaAccumSeq haffine ε hε (j + 1)).m : ℝ) /
        (sigmaAccumSeq haffine ε hε (j + 1)).n) =
      Real.log (((sigmaAccumSeq haffine ε hε j).m : ℝ) /
        (sigmaAccumSeq haffine ε hε j).n) +
      Real.log ((((sigmaAccumSeq haffine ε hε j).block haffine ε hε).m : ℝ) /
        ((sigmaAccumSeq haffine ε hε j).block haffine ε hε).n) := by
  let s := sigmaAccumSeq haffine ε hε j
  let b := s.block haffine ε hε
  have hsm : (s.m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.m_pos)
  have hsn : (s.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.n_pos)
  have hbm : (b.m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt b.m_pos)
  have hbn : (b.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt b.n_pos)
  change Real.log (((s.step haffine ε hε).m : ℝ) /
      (s.step haffine ε hε).n) = _
  change Real.log (((s.m * b.m : ℕ) : ℝ) / (s.n * b.n : ℕ)) = _
  have hratio : (((s.m * b.m : ℕ) : ℝ) / (s.n * b.n : ℕ)) =
      ((s.m : ℝ) / s.n) * ((b.m : ℝ) / b.n) := by
    push_cast
    field_simp
  rw [hratio, Real.log_mul (div_ne_zero hsm hsn) (div_ne_zero hbm hbn)]

theorem sigmaAccumSeq_log_lower
    (haffine : AffinePrimePairProperty 105) (ε : ℝ) (hε : 0 < ε) :
    ∀ j : ℕ, (j : ℝ) * (ε / 212) ≤
      Real.log (((sigmaAccumSeq haffine ε hε j).m : ℝ) /
        (sigmaAccumSeq haffine ε hε j).n) := by
  intro j
  induction j with
  | zero => simp [sigmaAccumSeq, SigmaAccum.one]
  | succ j ih =>
      rw [sigmaAccumSeq_log_succ]
      have hblock :=
        ((sigmaAccumSeq haffine ε hε j).block haffine ε hε).log_lower
      push_cast
      nlinarith

private theorem exists_accum_reaches
    (haffine : AffinePrimePairProperty 105) {t ε : ℝ}
    (hε : 0 < ε) :
    ∃ j : ℕ, t ≤
      Real.log (((sigmaAccumSeq haffine ε hε j).m : ℝ) /
        (sigmaAccumSeq haffine ε hε j).n) := by
  have hlo : 0 < ε / 212 := by positivity
  obtain ⟨j : ℕ, hj⟩ := exists_nat_gt (t / (ε / 212))
  refine ⟨j, le_trans ?_ (sigmaAccumSeq_log_lower haffine ε hε j)⟩
  have := mul_lt_mul_of_pos_right hj hlo
  field_simp at this
  linarith

/-- Finite coprime assembly reaches a positive logarithmic target with
overshoot less than the prescribed tolerance. -/
theorem exists_sigma_log_approx_of_affine
    (haffine : AffinePrimePairProperty 105)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ m n : ℕ,
      0 < m ∧ 0 < n ∧ σ 1 m = σ 1 n ∧
      t ≤ Real.log ((m : ℝ) / (n : ℝ)) ∧
      Real.log ((m : ℝ) / (n : ℝ)) < t + ε := by
  let H : ∃ j : ℕ, t ≤
      Real.log (((sigmaAccumSeq haffine ε hε j).m : ℝ) /
        (sigmaAccumSeq haffine ε hε j).n) :=
    exists_accum_reaches haffine hε
  let J := Nat.find H
  have hJ := Nat.find_spec H
  change t ≤ Real.log (((sigmaAccumSeq haffine ε hε J).m : ℝ) /
    (sigmaAccumSeq haffine ε hε J).n) at hJ
  have hJpos : 0 < J := by
    by_contra hzero
    have hJzero : J = 0 := Nat.eq_zero_of_not_pos hzero
    have htzero : t ≤ 0 := by
      rw [hJzero] at hJ
      simpa [sigmaAccumSeq, SigmaAccum.one] using hJ
    linarith
  have hprev : Real.log
      (((sigmaAccumSeq haffine ε hε (J - 1)).m : ℝ) /
        (sigmaAccumSeq haffine ε hε (J - 1)).n) < t := by
    exact lt_of_not_ge (Nat.find_min H (show J - 1 < J by omega))
  have hstep := sigmaAccumSeq_log_succ haffine ε hε (J - 1)
  have hJeq : J - 1 + 1 = J := by omega
  rw [hJeq] at hstep
  have hblock :=
    ((sigmaAccumSeq haffine ε hε (J - 1)).block haffine ε hε).log_upper
  let s := sigmaAccumSeq haffine ε hε J
  refine ⟨s.m, s.n, s.m_pos, s.n_pos, s.sigma_eq, hJ, ?_⟩
  change Real.log (((sigmaAccumSeq haffine ε hε J).m : ℝ) /
      (sigmaAccumSeq haffine ε hε J).n) < t + ε
  rw [hstep]
  linarith

/-- For targets at least one, logarithmic approximation gives the required
ordinary quotient approximation. -/
theorem sigma_quotient_approx_of_affine
    (haffine : AffinePrimePairProperty 105)
    {α ε : ℝ} (hα : 1 ≤ α) (hε : 0 < ε) :
    ∃ m n : ℕ,
      0 < m ∧ 0 < n ∧ σ 1 m = σ 1 n ∧
      |(m : ℝ) / (n : ℝ) - α| < ε := by
  rcases hα.eq_or_lt with rfl | hαlt
  · exact ⟨1, 1, by norm_num, by norm_num, by simp, by simpa using hε⟩
  · have hαpos : 0 < α := one_pos.trans hαlt
    let η := Real.log (1 + ε / α)
    have hη : 0 < η := Real.log_pos (by
      have : 0 < ε / α := div_pos hε hαpos
      linarith)
    have hlogpos : 0 < Real.log α := Real.log_pos hαlt
    obtain ⟨m, n, hm, hn, hsigma, hlower, hupper⟩ :=
      exists_sigma_log_approx_of_affine haffine hlogpos hη
    have hratioPos : (0 : ℝ) < (m : ℝ) / n := by positivity
    have hlowerRatio : α ≤ (m : ℝ) / n := by
      rw [← Real.exp_log hαpos, ← Real.exp_log hratioPos]
      exact Real.exp_le_exp.mpr hlower
    have hupperRatio : (m : ℝ) / n < α + ε := by
      rw [← Real.exp_log hratioPos]
      have hexp := Real.exp_lt_exp.mpr hupper
      have hcalc : Real.exp (Real.log α + η) = α + ε := by
        rw [Real.exp_add, Real.exp_log hαpos]
        dsimp only [η]
        rw [Real.exp_log]
        · field_simp
        · have : 0 < ε / α := div_pos hε hαpos
          linarith
      rwa [hcalc] at hexp
    refine ⟨m, n, hm, hn, hsigma, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hlowerRatio)]
    linarith

end

end Erdos823
