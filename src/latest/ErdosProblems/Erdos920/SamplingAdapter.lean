import ErdosProblems.Erdos920.Ordering
import ErdosProblems.Erdos920.RamseyPackaging
import ErdosProblems.Erdos920.Sampling

/-!
# Connecting the finite averaging lemmas to the `DStarWitness` interface

This file contains the small but important compatibility layer between the
concrete finite combinatorics in `Averaging`/`Ordering` and the numerical
interface in `RamseyPackaging`.

The only analytic inequality needed in this layer is the elementary lower
bound

`(m / e)^m <= m!`.

Together with the factorial ordering inequality and the forward-tuple bound
stored in a `DStarWitness`, it says that the expected number of independent
`m`-sets surviving Bernoulli sampling at density `m / (e C q^t)` is at most
one.
-/

open scoped BigOperators

namespace Erdos920

noncomputable section

open RamseyPackaging

/-- The elementary factorial lower bound used in the random-ordering step. -/
lemma factorial_lower_bound (m : ℕ) :
    ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
  field_simp
  rw [div_pow, div_le_iff₀ (by positivity)]
  rw [← div_le_iff₀' (by positivity)]
  rw [← Real.exp_nat_mul, mul_comm, Real.exp_eq_exp_ℝ]
  rw [NormedSpace.exp_eq_tsum_div]
  exact
    (Summable.le_tsum
      (show Summable _ from Real.summable_pow_div_factorial _)
      m (fun _ _ ↦ by positivity)).trans (by norm_num)

/-- A cleared-denominator form of the arithmetic cancellation behind the
sampling density.  It is kept independent of graphs so it can be reused by
the construction assembly. -/
lemma sampling_count_le_one_of_factorial_bound
    {m I F : ℕ} {B : ℝ} (hB : 0 < B)
    (horder : I * m.factorial ≤ F) (hforward : (F : ℝ) ≤ B ^ m) :
    ((m : ℝ) / (Real.exp 1 * B)) ^ m * (I : ℝ) ≤ 1 := by
  have hI : 0 ≤ (I : ℝ) := Nat.cast_nonneg I
  have hfactorial := factorial_lower_bound m
  have hcleared :
      (I : ℝ) * ((m : ℝ) / Real.exp 1) ^ m ≤ B ^ m := by
    calc
      (I : ℝ) * ((m : ℝ) / Real.exp 1) ^ m ≤
          (I : ℝ) * (m.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hfactorial hI
      _ ≤ (F : ℝ) := by exact_mod_cast horder
      _ ≤ B ^ m := hforward
  have hBpow : 0 < B ^ m := pow_pos hB _
  calc
    ((m : ℝ) / (Real.exp 1 * B)) ^ m * (I : ℝ) =
        ((I : ℝ) * ((m : ℝ) / Real.exp 1) ^ m) / B ^ m := by
      rw [div_pow, mul_pow, div_pow]
      field_simp [hB.ne']
    _ ≤ B ^ m / B ^ m := div_le_div_of_nonneg_right hcleared hBpow.le
    _ = 1 := div_self hBpow.ne'

namespace RamseyPackaging.DStarWitness

/-- The concrete factorial-ordering and sampling/deletion lemmas discharge
the averaging field of every `DStarWitness` whose sampling density is a
probability.

The three positivity assumptions are precisely what is needed to make the
base `C * q^t` positive.  In the construction they follow respectively from
the independent-set parameter, primality of `q`, and positivity of the
fixed tuple-counting constant. -/
theorem hasAveragingSamplingConclusion_of_sideConditions
    {t m q : ℕ} {C : ℝ} (W : DStarWitness t m q C)
    (hm : 1 ≤ m) (hq : 1 ≤ q) (hC : 0 < C)
    (hside : W.SamplingSideConditions) :
    W.HasAveragingSamplingConclusion := by
  classical
  letI : Fintype W.V := W.fintypeV
  letI : LinearOrder W.V := LinearOrder.lift' (Fintype.equivFin W.V)
    (Fintype.equivFin W.V).injective
  let D : W.V → W.V → Prop := W.D.arc
  have htfree : TransitiveTournamentFree D (t + 1) := by
    intro v hv htv
    apply W.transitiveTournamentFree
    refine ⟨v, hv, ?_⟩
    intro i j hij
    exact htv hij
  obtain ⟨π, hclique, horder⟩ :=
    exists_cliqueFree_forwardGraph_factorial_bound (D := D) htfree m
  have hcount_eq :
      (forwardIndependentFinset D m).card =
        @Digraph.forwardIndependentTupleCount W.V W.fintypeV W.D m := by
    simp only [forwardIndependentFinset, Digraph.forwardIndependentTupleCount,
      Finset.card_filter, D]
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
  let B : ℝ := C * (q : ℝ) ^ t
  have hB : 0 < B := by
    exact mul_pos hC (pow_pos (by exact_mod_cast (show 0 < q by omega)) _)
  have hforward : ((forwardIndependentFinset D m).card : ℝ) ≤ B ^ m := by
    rw [hcount_eq]
    exact W.forward_bound
  have hcount :
      W.samplingDensity ^ m *
          ((forwardGraph D π).indepSetFinset m).card ≤ 1 := by
    have h := sampling_count_le_one_of_factorial_bound hB horder hforward
    simpa [RamseyPackaging.DStarWitness.samplingDensity, B, mul_assoc] using h
  have hsamp := sampling_deletion_ramsey_lt
    (G := forwardGraph D π) hm hclique hside.1.le hside.2 hcount
  simpa [HasAveragingSamplingConclusion] using hsamp

end RamseyPackaging.DStarWitness

end

end Erdos920
