import ErdosProblems.Erdos543.FiniteProbability

/-!
# A finite second-moment estimate for missed targets

This file packages the elementary second-moment calculation used for Erdős
Problem 543.  A family `M t` of events is interpreted as the event that target
`t` is missed, and `missCount M` counts the missed targets.  The main results
express its first and second moments through singleton and ordered distinct-pair
probabilities.  The final theorem only asks for an aggregate upper bound on the
distinct-pair probabilities; no pairwise symmetry is needed.
-/

open scoped BigOperators

namespace Erdos543.SecondMoment

open FiniteProbability

noncomputable section

variable {Ω T : Type*} [Fintype Ω] [Fintype T]

local instance : DecidableEq T := Classical.decEq T
local instance : ∀ p : Prop, Decidable p := Classical.propDecidable

/-- The number of target events which occur at a sample point. -/
noncomputable def missCount (M : T → Set Ω) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun t => ω ∈ M t).card

/-- The total probability mass of ordered intersections of distinct target
events. -/
noncomputable def distinctPairMass (M : T → Set Ω) : ℝ :=
  ∑ t, ∑ u ∈ (Finset.univ.erase t), prob (M t ∩ M u)

theorem cast_missCount_eq_sum_indicator (M : T → Set Ω) (ω : Ω) :
    (missCount M ω : ℝ) = ∑ t, indicator (M t) ω := by
  classical
  unfold missCount indicator
  exact (Finset.sum_boole (R := ℝ) (fun t => ω ∈ M t) Finset.univ).symm

/-- The first moment of the missed-target count is the sum of the singleton
miss probabilities. -/
theorem expect_missCount (M : T → Set Ω) :
    expect (fun ω => (missCount M ω : ℝ)) = ∑ t, prob (M t) := by
  calc
    expect (fun ω => (missCount M ω : ℝ)) =
        expect (fun ω => ∑ t, indicator (M t) ω) := by
      congr 1
      funext ω
      exact cast_missCount_eq_sum_indicator M ω
    _ = ∑ t, expect (indicator (M t)) :=
      expect_finset_sum Finset.univ (fun t => indicator (M t))
    _ = ∑ t, prob (M t) := by simp

/-- In particular, a uniform singleton miss probability gives the expected
number of missed targets exactly. -/
theorem expect_missCount_of_singleton_uniform (M : T → Set Ω) (q : ℝ)
    (hsingle : ∀ t, prob (M t) = q) :
    expect (fun ω => (missCount M ω : ℝ)) = (Fintype.card T : ℝ) * q := by
  rw [expect_missCount]
  simp_rw [hsingle]
  simp

private theorem sum_indicator_sq (M : T → Set Ω) (ω : Ω) :
    (∑ t, indicator (M t) ω) ^ 2 =
      (∑ t, indicator (M t) ω) +
        ∑ t, ∑ u ∈ (Finset.univ.erase t), indicator (M t ∩ M u) ω := by
  classical
  calc
    (∑ t, indicator (M t) ω) ^ 2 =
        ∑ t, indicator (M t) ω * (∑ u, indicator (M u) ω) := by
      rw [pow_two, Finset.sum_mul]
    _ = ∑ t, ∑ u, indicator (M t) ω * indicator (M u) ω := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
    _ = ∑ t, (indicator (M t) ω * indicator (M t) ω +
          ∑ u ∈ (Finset.univ.erase t),
            indicator (M t) ω * indicator (M u) ω) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ t)]
    _ = (∑ t, indicator (M t) ω) +
        ∑ t, ∑ u ∈ (Finset.univ.erase t), indicator (M t ∩ M u) ω := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      · by_cases hM : ω ∈ M t <;> simp [indicator, hM]
      · apply Finset.sum_congr rfl
        intro u hu
        exact (indicator_inter (M t) (M u) ω).symm

/-- The raw second moment is the singleton mass plus the ordered
distinct-pair intersection mass. -/
theorem secondMoment_missCount (M : T → Set Ω) :
    expect (fun ω => (missCount M ω : ℝ) ^ 2) =
      (∑ t, prob (M t)) + distinctPairMass M := by
  calc
    expect (fun ω => (missCount M ω : ℝ) ^ 2) =
        expect (fun ω =>
          (∑ t, indicator (M t) ω) +
            ∑ t, ∑ u ∈ (Finset.univ.erase t),
              indicator (M t ∩ M u) ω) := by
      congr 1
      funext ω
      rw [cast_missCount_eq_sum_indicator]
      exact sum_indicator_sq M ω
    _ = expect (fun ω => ∑ t, indicator (M t) ω) +
          expect (fun ω => ∑ t, ∑ u ∈ (Finset.univ.erase t),
            indicator (M t ∩ M u) ω) := by
      rw [expect_add]
    _ = (∑ t, prob (M t)) + distinctPairMass M := by
      rw [expect_finset_sum]
      simp only [expect_indicator]
      congr 1
      rw [distinctPairMass, expect_finset_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [expect_finset_sum]
      simp

/-- Exact variance identity for the missed-target count. -/
theorem variance_missCount [Nonempty Ω] (M : T → Set Ω) :
    variance (fun ω => (missCount M ω : ℝ)) =
      (∑ t, prob (M t)) + distinctPairMass M -
        (∑ t, prob (M t)) ^ 2 := by
  rw [variance_eq_secondMoment_sub_sq, secondMoment_missCount,
    expect_missCount]

/-- The variance identity when all singleton miss probabilities are equal. -/
theorem variance_missCount_of_singleton_uniform [Nonempty Ω]
    (M : T → Set Ω) (q : ℝ) (hsingle : ∀ t, prob (M t) = q) :
    variance (fun ω => (missCount M ω : ℝ)) =
      (Fintype.card T : ℝ) * q + distinctPairMass M -
        ((Fintype.card T : ℝ) * q) ^ 2 := by
  rw [variance_missCount]
  simp_rw [hsingle]
  simp

/-- If every ordered distinct pair has the same intersection probability,
the ordered pair mass has the expected closed form. -/
theorem distinctPairMass_of_pair_uniform [Nonempty T]
    (M : T → Set Ω) (q₂ : ℝ)
    (hpair : ∀ t u, t ≠ u → prob (M t ∩ M u) = q₂) :
    distinctPairMass M =
      (Fintype.card T : ℝ) * ((Fintype.card T : ℝ) - 1) * q₂ := by
  classical
  rw [distinctPairMass]
  calc
    (∑ t, ∑ u ∈ (Finset.univ.erase t), prob (M t ∩ M u)) =
        ∑ t, ∑ u ∈ (Finset.univ.erase t), q₂ := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      rw [hpair t u]
      simpa using (Finset.ne_of_mem_erase hu).symm
    _ = (Fintype.card T : ℝ) * ((Fintype.card T : ℝ) - 1) * q₂ := by
      have hcard : 0 < Fintype.card T := Fintype.card_pos
      simp [Nat.cast_sub hcard, mul_assoc]

/-- Exact closed form when singleton and distinct-pair probabilities are both
uniform. -/
theorem variance_missCount_of_uniform [Nonempty Ω] [Nonempty T]
    (M : T → Set Ω) (q₁ q₂ : ℝ)
    (hsingle : ∀ t, prob (M t) = q₁)
    (hpair : ∀ t u, t ≠ u → prob (M t ∩ M u) = q₂) :
    variance (fun ω => (missCount M ω : ℝ)) =
      (Fintype.card T : ℝ) * q₁ +
        (Fintype.card T : ℝ) * ((Fintype.card T : ℝ) - 1) * q₂ -
          ((Fintype.card T : ℝ) * q₁) ^ 2 := by
  rw [variance_missCount_of_singleton_uniform M q₁ hsingle,
    distinctPairMass_of_pair_uniform M q₂ hpair]

/-- A quantitative second-moment bound in the form needed later.  If the
singleton miss probability is `q > 0`, and the aggregate distinct-pair mass is
at most `(1+ε)` times the independent-pair benchmark, then the probability of
missing no target is at most `1 / (#T*q) + ε`.

The aggregate hypothesis is deliberately weaker than a pointwise pairwise
bound. -/
theorem prob_missCount_eq_zero_le [Nonempty Ω] [Nonempty T]
    (M : T → Set Ω) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 ≤ ε)
    (hsingle : ∀ t, prob (M t) = q)
    (hpairMass : distinctPairMass M ≤
      (Fintype.card T : ℝ) * ((Fintype.card T : ℝ) - 1) *
        ((1 + ε) * q ^ 2)) :
    prob {ω | missCount M ω = 0} ≤
      1 / ((Fintype.card T : ℝ) * q) + ε := by
  let n : ℝ := Fintype.card T
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card T)
  have hnq : 0 < n * q := mul_pos hn hq
  have hexpect : expect (fun ω => (missCount M ω : ℝ)) = n * q := by
    simpa [n] using expect_missCount_of_singleton_uniform M q hsingle
  have hcheb := prob_eq_zero_le_variance_div_expect_sq (missCount M)
    (by simpa [hexpect] using hnq)
  calc
    prob {ω | missCount M ω = 0} ≤
        variance (fun ω => (missCount M ω : ℝ)) /
          (expect fun ω => (missCount M ω : ℝ)) ^ 2 := hcheb
    _ = variance (fun ω => (missCount M ω : ℝ)) / (n * q) ^ 2 := by
      rw [hexpect]
    _ ≤ (n * q + n * (n - 1) * ((1 + ε) * q ^ 2) - (n * q) ^ 2) /
          (n * q) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg (n * q))
      rw [variance_missCount_of_singleton_uniform M q hsingle]
      dsimp [n]
      linarith
    _ ≤ 1 / (n * q) + ε := by
      rw [div_le_iff₀ (sq_pos_of_pos hnq)]
      field_simp
      nlinarith [sq_nonneg q, mul_nonneg hn.le hε]
    _ = 1 / ((Fintype.card T : ℝ) * q) + ε := by rfl

/-- Pointwise pairwise control implies the aggregate hypothesis in
`prob_missCount_eq_zero_le`. -/
theorem prob_missCount_eq_zero_le_of_pairwise [Nonempty Ω] [Nonempty T]
    (M : T → Set Ω) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 ≤ ε)
    (hsingle : ∀ t, prob (M t) = q)
    (hpair : ∀ t u, t ≠ u →
      prob (M t ∩ M u) ≤ (1 + ε) * q ^ 2) :
    prob {ω | missCount M ω = 0} ≤
      1 / ((Fintype.card T : ℝ) * q) + ε := by
  apply prob_missCount_eq_zero_le M q ε hq hε hsingle
  classical
  rw [distinctPairMass]
  calc
    (∑ t, ∑ u ∈ (Finset.univ.erase t), prob (M t ∩ M u)) ≤
        ∑ t, ∑ u ∈ (Finset.univ.erase t), (1 + ε) * q ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      apply hpair t u
      simpa using (Finset.ne_of_mem_erase hu).symm
    _ = (Fintype.card T : ℝ) * ((Fintype.card T : ℝ) - 1) *
          ((1 + ε) * q ^ 2) := by
      have hcard : 0 < Fintype.card T := Fintype.card_pos
      simp [Nat.cast_sub hcard, mul_assoc]

end

end Erdos543.SecondMoment
