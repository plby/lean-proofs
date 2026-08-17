import ErdosProblems.Erdos543.CoreObstruction
import ErdosProblems.Erdos543.FinalLogic
import ErdosProblems.Erdos543.HalfTransfer

/-!
# Final assembly of the prime-cyclic obstruction

This file combines the uniform one- and two-target Poisson estimates with the
second-moment inequality and the independent-to-uniform transfer.
-/

open Filter
open scoped Topology BigOperators

namespace Erdos543.CoreAssembly

attribute [local instance] Classical.propDecidable

noncomputable section

open FiniteProbability
open CoreObstruction

instance nonemptyNonzeroTarget (p : ℕ) [Fact p.Prime] :
    Nonempty (NonzeroTarget p) := by
  have hp1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  exact ⟨⟨1, hp1⟩⟩

lemma card_nonzeroTarget (p : ℕ) [Fact p.Prime] :
    Fintype.card (NonzeroTarget p) = p - 1 := by
  rw [show Fintype.card (NonzeroTarget p) =
      Fintype.card (ZMod p) - 1 by simp [NonzeroTarget]]
  simp [ZMod.card]

lemma missEvent_inter_eq_pairEvent {p k : ℕ} [Fact p.Prime]
    (x y : NonzeroTarget p) (hxy : x ≠ y) :
    missEvent (k := k) x ∩ missEvent (k := k) y =
      {a | Erdos543.targetSubsetEventCount (k := k)
        ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)) a = 0} := by
  ext a
  rw [Set.mem_inter_iff]
  change Erdos543.targetSubsetEventCount ({(x : ZMod p)} : Finset (ZMod p)) a = 0 ∧
      Erdos543.targetSubsetEventCount ({(y : ZMod p)} : Finset (ZMod p)) a = 0 ↔
    Erdos543.targetSubsetEventCount
      ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)) a = 0
  rw [targetSubsetEventCount_eq_zero_iff,
    targetSubsetEventCount_eq_zero_iff,
    targetSubsetEventCount_eq_zero_iff]
  constructor
  · rintro ⟨hx, hy⟩ S b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact hx S x (by simp)
    · exact hy S y (by simp)
  · intro h
    constructor
    · intro S b hb
      have : b = (x : ZMod p) := by simpa using hb
      subst b
      exact h S x (by simp)
    · intro S b hb
      have : b = (y : ZMod p) := by simpa using hb
      subst b
      exact h S y (by simp)

lemma abs_sub_le_of_abs_div_sub_one_le {a q δ : ℝ}
    (hq : 0 < q) (h : |a / q - 1| ≤ δ) :
    |a - q| ≤ δ * q := by
  have heq : a - q = (a / q - 1) * q := by
    field_simp [hq.ne']
  rw [heq, abs_mul, abs_of_pos hq]
  exact mul_le_mul_of_nonneg_right h hq.le

/-- The common relative error used for singleton and pair miss events. -/
def commonRelativeError (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  max (poissonRelativeError g 1 N) (poissonRelativeError g 2 N)

lemma commonRelativeError_nonneg (g : ℕ → ℝ) (N : ℕ) :
    0 ≤ commonRelativeError g N := by
  apply le_max_of_le_left
  rw [poissonRelativeError]
  apply add_nonneg
  · apply mul_nonneg (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (collisionParameter_nonneg g N)) _))
      (Nat.cast_nonneg _)
  · exact mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (Real.exp_pos _).le

lemma tendsto_commonRelativeError_zero {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (commonRelativeError g) atTop (nhds 0) := by
  change Tendsto (fun N ↦ max (poissonRelativeError g 1 N)
    (poissonRelativeError g 2 N)) atTop (nhds 0)
  simpa using
    (tendsto_poissonRelativeError_zero hg 1).max
      (tendsto_poissonRelativeError_zero hg 2)

/-! ## The one- and two-target estimates imply a no-miss bound -/

theorem prob_noMiss_le_at
    {g : ℕ → ℝ} {N : ℕ} [Fact N.Prime]
    (h1 : ∀ B : Finset (ZMod N), B.card = 1 →
      (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N →
      |prob {a | Erdos543.targetSubsetEventCount
            (k := cutoffSize g N) B a = 0} /
          Real.exp (-collisionParameter g N) - 1| ≤
        poissonRelativeError g 1 N)
    (h2 : ∀ B : Finset (ZMod N), B.card = 2 →
      (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N →
      |prob {a | Erdos543.targetSubsetEventCount
            (k := cutoffSize g N) B a = 0} /
          Real.exp (-((2 : ℝ) * collisionParameter g N)) - 1| ≤
        poissonRelativeError g 2 N)
    (hNq : (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N)
    (herr : commonRelativeError g N ≤ (1 / 2 : ℝ)) :
    prob {a | MissedEvents.missedCount
        (missEvent (p := N) (k := cutoffSize g N)) a = 0} ≤
      6 / (((N - 1 : ℕ) : ℝ) *
        Real.exp (-collisionParameter g N)) +
      12 * commonRelativeError g N := by
  have hbound := PoissonSecondMoment.prob_no_missed_le_of_relative_exp_errors
    (missEvent (p := N) (k := cutoffSize g N))
    (collisionParameter g N) (commonRelativeError g N)
    (commonRelativeError_nonneg g N) herr
  have hsingle : ∀ x : NonzeroTarget N,
      |prob (missEvent (k := cutoffSize g N) x) -
          Real.exp (-collisionParameter g N)| ≤
        commonRelativeError g N * Real.exp (-collisionParameter g N) := by
    intro x
    have hx := h1 ({(x : ZMod N)} : Finset (ZMod N)) (by simp) hNq
    have hx' := abs_sub_le_of_abs_div_sub_one_le
      (Real.exp_pos (-collisionParameter g N)) hx
    exact hx'.trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.exp_pos _).le)
  have hpair : ∀ x y : NonzeroTarget N, x ≠ y →
      |prob (missEvent (k := cutoffSize g N) x ∩
            missEvent (k := cutoffSize g N) y) -
          Real.exp (-2 * collisionParameter g N)| ≤
        commonRelativeError g N *
          Real.exp (-2 * collisionParameter g N) := by
    intro x y hxy
    have hcoe : (x : ZMod N) ≠ (y : ZMod N) := by
      intro h
      exact hxy (Subtype.ext h)
    have hxyBound := h2
      ({(x : ZMod N), (y : ZMod N)} : Finset (ZMod N))
      (by simp [hcoe]) hNq
    have hxyBound' := abs_sub_le_of_abs_div_sub_one_le
      (Real.exp_pos (-((2 : ℝ) * collisionParameter g N))) hxyBound
    rw [missEvent_inter_eq_pairEvent x y hxy]
    simpa [commonRelativeError] using
      hxyBound'.trans (mul_le_mul_of_nonneg_right
        (le_max_right (poissonRelativeError g 1 N) _) (Real.exp_pos _).le)
  specialize hbound hsingle hpair
  rw [card_nonzeroTarget N] at hbound
  exact hbound

/-! ## The second-moment upper envelope vanishes -/

def missedTargetDenominator (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N - 1 : ℕ) : ℝ) * Real.exp (-collisionParameter g N)

lemma tendsto_missedTargetDenominator_atTop {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (missedTargetDenominator g) atTop atTop := by
  have hbase := tendsto_nat_mul_exp_neg_collisionParameter_atTop hg
  have hhalf : Tendsto (fun N : ℕ ↦
      ((N : ℝ) * Real.exp (-collisionParameter g N)) / 2)
      atTop atTop := hbase.atTop_div_const (by norm_num)
  apply tendsto_atTop_mono' atTop _ hhalf
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [missedTargetDenominator, Nat.cast_sub (by omega : 1 ≤ N)]
  have hexp : 0 ≤ Real.exp (-collisionParameter g N) := (Real.exp_pos _).le
  have hcast : (2 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    (N : ℝ) * Real.exp (-collisionParameter g N) / 2 =
        ((N : ℝ) / 2) * Real.exp (-collisionParameter g N) := by ring
    _ ≤ ((N : ℝ) - 1) * Real.exp (-collisionParameter g N) := by
      gcongr
      linarith
    _ = ((N : ℝ) - (1 : ℕ)) * Real.exp (-collisionParameter g N) := by
      norm_num

lemma tendsto_secondMomentEnvelope_zero {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦
      6 / missedTargetDenominator g N + 12 * commonRelativeError g N)
      atTop (nhds 0) := by
  have hfirst : Tendsto (fun N : ℕ ↦ 6 / missedTargetDenominator g N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_missedTargetDenominator_atTop hg)
  have hsecond : Tendsto (fun N : ℕ ↦ 12 * commonRelativeError g N)
      atTop (nhds 0) := by
    simpa using (tendsto_commonRelativeError_zero hg).const_mul 12
  simpa using hfirst.add hsecond

/-! ## Eventual cyclic failure -/

theorem eventually_not_halfComplete_prime_moduli
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ hp : N.Prime,
      letI : NeZero N := ⟨hp.ne_zero⟩
      ¬ Model.HalfComplete (ZMod N) (cutoffSize g N) := by
  have hP1 := eventually_targetSet_poisson_relative_error hg 1 (by omega)
  have hP2 := eventually_targetSet_poisson_relative_error hg 2 (by omega)
  have herrHalf : ∀ᶠ N : ℕ in atTop,
      commonRelativeError g N ≤ (1 / 2 : ℝ) := by
    have hlt := (tendsto_order.1 (tendsto_commonRelativeError_zero hg)).2
      (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hlt] with N hN
    exact hN.le
  have henvelope : ∀ᶠ N : ℕ in atTop,
      6 / missedTargetDenominator g N + 12 * commonRelativeError g N <
        (1 / 4 : ℝ) :=
    (tendsto_order.1 (tendsto_secondMomentEnvelope_zero hg)).2
      (1 / 4 : ℝ) (by norm_num)
  have hcollision : ∀ᶠ N : ℕ in atTop,
      (cutoffSize g N : ℝ) ^ 2 / (N : ℝ) < (1 / 4 : ℝ) :=
    (tendsto_order.1 (HalfTransfer.tendsto_cutoffSize_sq_div_nat_zero hg)).2
      (1 / 4 : ℝ) (by norm_num)
  filter_upwards [hP1, hP2, herrHalf, henvelope, hcollision]
      with N hP1N hP2N herrN henvN hcollisionN
  intro hp
  letI : Fact N.Prime := ⟨hp⟩
  letI : NeZero N := ⟨hp.ne_zero⟩
  by_cases hNq : (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N
  · have h1 : ∀ B : Finset (ZMod N), B.card = 1 →
        (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N →
        |prob {a | Erdos543.targetSubsetEventCount
              (k := cutoffSize g N) B a = 0} /
            Real.exp (-collisionParameter g N) - 1| ≤
          poissonRelativeError g 1 N := by
      intro B hB hq
      have h := (hP1N hp) B hB hq
      norm_num at h ⊢
      exact h
    have h2 : ∀ B : Finset (ZMod N), B.card = 2 →
        (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N →
        |prob {a | Erdos543.targetSubsetEventCount
              (k := cutoffSize g N) B a = 0} /
            Real.exp (-((2 : ℝ) * collisionParameter g N)) - 1| ≤
          poissonRelativeError g 2 N := by
      intro B hB hq
      have h := (hP2N hp) B hB hq
      norm_num at h ⊢
      exact h
    have hmissLe := prob_noMiss_le_at h1 h2 hNq herrN
    have hmiss : prob {a | MissedEvents.missedCount
          (missEvent (p := N) (k := cutoffSize g N)) a = 0} <
        (1 / 4 : ℝ) :=
      hmissLe.trans_lt (by simpa [missedTargetDenominator] using henvN)
    have hcollisionRatio :
        ((IIDTransfer.collisionTuples (ZMod N) (cutoffSize g N)).card : ℝ) /
            (N ^ cutoffSize g N : ℕ) < (1 / 4 : ℝ) := by
      have hle := HalfTransfer.collision_ratio_le_sq_div_card
        (ZMod N) (cutoffSize g N)
      have hle' :
          ((IIDTransfer.collisionTuples (ZMod N) (cutoffSize g N)).card : ℝ) /
              (N ^ cutoffSize g N : ℕ) ≤
            (cutoffSize g N : ℝ) ^ 2 / (N : ℝ) := by
        simpa [ZMod.card] using hle
      exact hle'.trans_lt hcollisionN
    exact CoreObstruction.not_halfComplete_of_prob_noMiss_lt_quarter
      hmiss hcollisionRatio
  · have hreal : (2 : ℝ) ^ cutoffSize g N < (N : ℝ) :=
      lt_of_not_ge hNq
    have hpow : 2 ^ cutoffSize g N < N := by
      exact_mod_cast hreal
    exact Model.not_halfComplete_zmod_of_two_pow_lt hpow

/-- The central obstruction in exactly the interface consumed by
`FinalLogic`: every `o(log log)` proposed cutoff fails eventually along the
canonical cofinal sequence of prime cyclic groups. -/
theorem eventualPrimeCyclicFailure : FinalLogic.EventualPrimeCyclicFailure := by
  intro g hg
  have hall := eventually_not_halfComplete_prime_moduli hg
  have hseq := PrimeSequence.eventually_primeSeq hall
  filter_upwards [hseq] with i hi
  exact hi (PrimeSequence.primeSeq_prime i)

end

end Erdos543.CoreAssembly
