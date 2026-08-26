import ErdosProblems.Erdos67b.LogDilation
import ErdosProblems.Erdos67b.LogElliott
import ErdosProblems.Erdos67b.PrimeGraph

/-!
# Multiplicative correlations and prime graph edges

The logarithmic dilation comparison and translation estimate apply to
the actual graph divisibility indicator. Complete multiplicativity is
used only on positive integers, so no condition on the value at zero
is imposed in this module.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

/-- The pair correlation under the finite logarithmic probability law. -/
def logPairCorrelation (L U : ℕ) (f : ℕ → ℂ) (h : ℕ) : ℂ :=
  logProbExpectation L U (fun n ↦ f n * conj (f (n + h)))

/-- The unshifted observable for an edge whose step is `q*h`. -/
def divisiblePairObservable (f : ℕ → ℂ) (q h n : ℕ) : ℂ :=
  if q ∣ n then f n * conj (f (n + q * h)) else 0

theorem norm_divisiblePairObservable_le_one {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ = 1) (q h : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖divisiblePairObservable f q h n‖ ≤ 1 := by
  unfold divisiblePairObservable
  split_ifs
  · rw [norm_mul, Complex.norm_conj, hf n hn, hf (n + q * h) (by omega)]
    norm_num
  · norm_num

/-- Cancellation of the prime factor in a conjugate pair. -/
theorem unit_pair_dilation {f : ℕ → ℂ}
    (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hunit : ∀ n, 0 < n → ‖f n‖ = 1)
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) (h : ℕ) :
    f (q * n) * conj (f (q * n + q * h)) = f n * conj (f (n + h)) := by
  rw [← Nat.mul_add, hmul.2 q n hq hn, hmul.2 q (n + h) hq (by omega), map_mul]
  calc
    (f q * f n) * (conj (f q) * conj (f (n + h))) =
        (f q * conj (f q)) * (f n * conj (f (n + h))) := by ring
    _ = f n * conj (f (n + h)) := by rw [Complex.mul_conj', hunit q hq]; simp

/-- Each translated graph edge has mean `C_h/q`, with explicit errors. -/
theorem norm_logProb_divisiblePair_sub_correlation_le
    {L U q : ℕ} (hL : 0 < L) (hLU : L ≤ U) (hq : 0 < q)
    (f : ℕ → ℂ) (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hunit : ∀ n, 0 < n → ‖f n‖ = 1) (h j : ℕ) :
    ‖logProbExpectation L U (fun n ↦ divisiblePairObservable f q h (n + j)) -
      (q : ℝ)⁻¹ • logPairCorrelation L U f h‖ ≤
        2 / (logProbMassNN L U : ℝ) +
          2 * j / ((L : ℝ) * logProbMassNN L U) := by
  have hM : (0 : ℝ) < logProbMassNN L U := by
    exact_mod_cast logProbMassNN_pos hL hLU
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hdil := norm_logProbExpectation_dilation_sub_le hL hLU hq
    (fun n ↦ f n * conj (f (n + q * h))) (B := 1) zero_le_one (by
      intro n hn
      rw [norm_mul, Complex.norm_conj, hunit n hn,
        hunit (n + q * h) (by omega)]
      norm_num)
  have heq : logProbExpectation L U (fun n ↦ f (q * n) * conj (f (q * n + q * h))) =
      logPairCorrelation L U f h := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    exact unit_pair_dilation hmul hunit hq (hL.trans_le (mem_logProbWindow.mp n.2).1) h
  rw [heq] at hdil
  change ‖logPairCorrelation L U f h -
    (q : ℝ) • logProbExpectation L U (divisiblePairObservable f q h)‖ ≤ _ at hdil
  have hbase : ‖logProbExpectation L U (divisiblePairObservable f q h) -
      (q : ℝ)⁻¹ • logPairCorrelation L U f h‖ ≤ 2 / (logProbMassNN L U : ℝ) := by
    have hcancel : (q : ℝ)⁻¹ • (logPairCorrelation L U f h -
        (q : ℝ) • logProbExpectation L U (divisiblePairObservable f q h)) =
        (q : ℝ)⁻¹ • logPairCorrelation L U f h -
          logProbExpectation L U (divisiblePairObservable f q h) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hqr.ne', one_smul]
    calc
      _ = ‖(q : ℝ)⁻¹ • (logPairCorrelation L U f h -
          (q : ℝ) • logProbExpectation L U (divisiblePairObservable f q h))‖ := by
        rw [hcancel, norm_sub_rev]
      _ = (q : ℝ)⁻¹ * ‖logPairCorrelation L U f h -
          (q : ℝ) • logProbExpectation L U (divisiblePairObservable f q h)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hqr.le)]
      _ ≤ (q : ℝ)⁻¹ * (2 * 1 * q / (logProbMassNN L U : ℝ)) :=
        mul_le_mul_of_nonneg_left hdil (inv_nonneg.mpr hqr.le)
      _ = 2 / (logProbMassNN L U : ℝ) := by field_simp
  have htranslate := norm_logProbExpectation_translate_sub_le hL hLU j
    (divisiblePairObservable f q h) (B := 1) zero_le_one
    (fun n hn ↦ norm_divisiblePairObservable_le_one hunit q h (hL.trans_le hn))
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (logProbExpectation L U (fun n ↦ divisiblePairObservable f q h (n + j)))
    (logProbExpectation L U (divisiblePairObservable f q h))
    ((q : ℝ)⁻¹ • logPairCorrelation L U f h)
  linarith

/-- The finite logarithmic expectation commutes with a finite sum. -/
theorem logProbExpectation_finset_sum
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {ι : Type*}
    (L U : ℕ) (s : Finset ι) (F : ι → ℕ → E) :
    logProbExpectation L U (fun n ↦ ∑ i ∈ s, F i n) =
      ∑ i ∈ s, logProbExpectation L U (F i) := by
  simp only [logProbExpectation, Finset.smul_sum]
  exact Finset.sum_comm

/-- The number of edges of a fixed positive or zero step is exact. -/
theorem card_fin_add_lt (H a : ℕ) :
    (Finset.univ.filter fun j : Fin H ↦ j.1 + a < H).card = H - a := by
  classical
  calc
    _ = (Finset.range (H - a)).card := by
      apply Finset.card_bij (fun j _ ↦ j.1)
      · intro j hj
        have := (Finset.mem_filter.mp hj).2
        exact Finset.mem_range.mpr (by omega)
      · intro i hi j hj hij
        exact Fin.ext hij
      · intro n hn
        have hn' := Finset.mem_range.mp hn
        refine ⟨⟨n, by omega⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
    _ = H - a := Finset.card_range _

/-- The coefficient multiplying the original pair correlation after
averaging all actual graph edges. Natural subtraction records the cutoff. -/
def primeGraphCorrelationWeight (H h : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ p : PrimeGraphIndex H, if p.1 ∈ s then ((H - p.1 * h : ℕ) : ℝ) / p.1 else 0

theorem primeGraphCorrelationWeight_nonneg (H h : ℕ) (s : Finset ℕ) :
    0 ≤ primeGraphCorrelationWeight H h s := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> positivity

theorem primeGraphCorrelationWeight_eq_sum {H : ℕ} (h : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Nat.primesLE H) :
    primeGraphCorrelationWeight H h s = ∑ p ∈ s, ((H - p * h : ℕ) : ℝ) / p := by
  classical
  calc
    _ = ∑ p ∈ Nat.primesLE H, if p ∈ s then ((H - p * h : ℕ) : ℝ) / p else 0 :=
      Finset.sum_coe_sort (Nat.primesLE H) _
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun hp ↦ hp.2, fun hp ↦ ⟨hs hp, hp⟩⟩

/-- If every edge step is at most half the block length, the graph
coefficient retains at least half the full reciprocal-prime weight. -/
theorem half_mul_reciprocal_le_primeGraphCorrelationWeight
    {H : ℕ} (h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H)
    (hstep : ∀ p ∈ s, 2 * p * h ≤ H) :
    (H : ℝ) / 2 * (∑ p ∈ s, (p : ℝ)⁻¹) ≤ primeGraphCorrelationWeight H h s := by
  rw [primeGraphCorrelationWeight_eq_sum h s hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hph : p * h ≤ H := by nlinarith [hstep p hp]
  have hstepR : 2 * (p : ℝ) * h ≤ H := by exact_mod_cast hstep p hp
  rw [Nat.cast_sub hph, Nat.cast_mul, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

/-- Rewrite the CRT graph value in terms of the original sequence and
its genuine, non-wrapping edges. -/
theorem primeGraphSum_sequenceBlock (f : ℕ → ℂ) (H h n : ℕ) (s : Finset ℕ) :
    primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H)) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then
          divisiblePairObservable f p.1 h (n + (j.1 + 1)) else 0
      else 0 := by
  classical
  rw [primeGraphSum_natCast]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.1 + p.1 * h < H <;>
      simp [primeGraphEdge, finiteSequenceBlock, divisiblePairObservable, hj,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · rfl

/-- The complete graph average, with an explicit finite error. No
nonpretentiousness or short-interval estimate is assumed here. -/
theorem norm_logProb_primeGraph_sub_correlation_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (f : ℕ → ℂ) (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hunit : ∀ n, 0 < n → ‖f n‖ = 1) (H h : ℕ) (s : Finset ℕ) :
    ‖logProbExpectation L U (fun n ↦
        primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H))) -
      primeGraphCorrelationWeight H h s • logPairCorrelation L U f h‖ ≤
        (Nat.primeCounting H : ℝ) * H *
          (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U)) := by
  classical
  let C := logPairCorrelation L U f h
  let e := 2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U)
  have he : 0 ≤ e := by dsimp [e]; positivity
  let A (p : PrimeGraphIndex H) (j : Fin H) : ℂ :=
    logProbExpectation L U (fun n ↦ divisiblePairObservable f p.1 h (n + (j.1 + 1)))
  have hedge (p : PrimeGraphIndex H) (j : Fin H) : ‖A p j - (p.1 : ℝ)⁻¹ • C‖ ≤ e := by
    have h := norm_logProb_divisiblePair_sub_correlation_le hL hLU
      (Nat.prime_of_mem_primesLE p.2).pos f hmul hunit h (j.1 + 1)
    refine h.trans ?_
    dsimp [e]
    gcongr
    exact_mod_cast (by omega : j.1 + 1 ≤ H)
  have hexpect : logProbExpectation L U (fun n ↦
        primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H))) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then A p j else 0 else 0 := by
    simp_rw [primeGraphSum_sequenceBlock]
    rw [logProbExpectation_finset_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.1 ∈ s
    · simp only [hp, if_true]
      rw [logProbExpectation_finset_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.1 + p.1 * h < H
      · simp only [hj, if_true]; rfl
      · simp [hj, logProbExpectation]
    · simp [hp, logProbExpectation]
  have hcoef : primeGraphCorrelationWeight H h s • C =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0 else 0 := by
    rw [primeGraphCorrelationWeight, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.1 ∈ s
    · simp only [hp, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, card_fin_add_lt, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul, div_eq_mul_inv]
    · simp [hp]
  rw [hexpect, hcoef, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : PrimeGraphIndex H, ‖(if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then A p j else 0 else 0) -
      (if p.1 ∈ s then ∑ j : Fin H,
        if j.1 + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0 else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, (H : ℝ) * e := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.1 ∈ s
      · simp only [hp, if_true, ← Finset.sum_sub_distrib]
        calc
          _ ≤ ∑ j : Fin H, ‖(if j.1 + p.1 * h < H then A p j else 0) -
              (if j.1 + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0)‖ := norm_sum_le _ _
          _ ≤ ∑ _j : Fin H, e := by
            apply Finset.sum_le_sum
            intro j _
            by_cases hj : j.1 + p.1 * h < H
            · simpa only [hj, if_true] using hedge p j
            · simpa only [hj, if_false, sub_zero, norm_zero] using he
          _ = H * e := by simp
      · simp only [hp, if_false, sub_zero, norm_zero]
        positivity
    _ = (Nat.primeCounting H : ℝ) * H * e := by
      rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul, mul_assoc]

end

end Erdos67b
