import ErdosProblems.Erdos67b.PrimeGraphConcentration

/-!
# Decoupling the prime graph under logarithmic sampling

Connect graph concentration to the entropy-selected scale and convert
the resulting rare-event probability into an expectation bound.
-/

open scoped BigOperators NNReal
open Finset Filter

namespace Erdos67b

open FiniteEntropy

noncomputable section

theorem norm_primeGraphSum_le {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hb : ∀ j, ‖b j‖ ≤ B)
    (hs : ∀ p ∈ s, δ * H ≤ p) (z : ZMod (primeGraphModulus H)) :
    ‖primeGraphSum b h s z‖ ≤ (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  unfold primeGraphSum crtComplexSum
  calc
    ‖∑ p, primeGraphObservable b h s p _‖ ≤ ∑ p, ‖primeGraphObservable b h s p _‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, primeGraphRadius B δ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_primeGraphObservable_le b h s hB hδ hb hs p _
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]

theorem norm_primeGraphMean_le {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hb : ∀ j, ‖b j‖ ≤ B)
    (hs : ∀ p ∈ s, δ * H ≤ p) :
    ‖primeGraphMean b h s‖ ≤ (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  rw [← crtComplexMean_primeGraphObservable]
  unfold crtComplexMean
  have hcoord (p : PrimeGraphIndex H) :
      ‖(p.1 : ℝ)⁻¹ • ∑ x, primeGraphObservable b h s p x‖ ≤ primeGraphRadius B δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsum : ‖∑ x, primeGraphObservable b h s p x‖ ≤ (p.1 : ℝ) * primeGraphRadius B δ := by
      calc
        ‖∑ x, primeGraphObservable b h s p x‖ ≤ ∑ x, ‖primeGraphObservable b h s p x‖ := norm_sum_le _ _
        _ ≤ ∑ _x : ZMod p.1, primeGraphRadius B δ := Finset.sum_le_sum
          (fun x _ ↦ norm_primeGraphObservable_le b h s hB hδ hb hs p x)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)⁻¹)
    have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.1)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp, one_mul] using h
  exact (norm_sum_le _ _).trans (by
    have h := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) ↦ hcoord p)
    simpa only [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul] using h)

/-- Centered graph observable evaluated on the actual sequence block
and the residue of its starting integer. -/
def primeGraphDiscrepancy (F : ℕ → ℂ) (H h : ℕ) (s : Finset ℕ) (n : ℕ) : ℂ :=
  primeGraphSum (finiteSequenceBlock F H n) h s (n : ZMod (primeGraphModulus H)) -
    primeGraphMean (finiteSequenceBlock F H n) h s

theorem norm_primeGraphDiscrepancy_le (F : ℕ → ℂ) (H h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hF : ∀ n, ‖F n‖ ≤ B)
    (hs : ∀ p ∈ s, δ * H ≤ p) (n : ℕ) :
    ‖primeGraphDiscrepancy F H h s n‖ ≤ 2 * (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  have hb : ∀ j, ‖finiteSequenceBlock F H n j‖ ≤ B := fun j ↦ hF _
  have hsum := norm_primeGraphSum_le (finiteSequenceBlock F H n) h s hB hδ hb hs
    (n : ZMod (primeGraphModulus H))
  have hmean := norm_primeGraphMean_le (finiteSequenceBlock F H n) h s hB hδ hb hs
  exact (norm_sub_le _ _).trans (by linarith)

/-- A uniform bound and a tail probability control a finite vector
expectation. The estimate counts the exceptional contribution only once. -/
theorem norm_finiteExpectation_le_of_tail
    {Ω E : Type*} [Fintype Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : FinProb Ω) (A : Ω → E) {t M η : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hbound : ∀ ω, ‖A ω‖ ≤ M)
    (htail : finiteEventMass p {ω | t ≤ ‖A ω‖} ≤ η) :
    ‖∑ ω, p ω • A ω‖ ≤ t + M * η := by
  classical
  have hpoint (ω : Ω) : ‖A ω‖ ≤ t + M * (if t ≤ ‖A ω‖ then 1 else 0) := by
    split_ifs with h
    · linarith [hbound ω]
    · have hlt : ‖A ω‖ < t := lt_of_not_ge h
      simpa only [mul_zero, add_zero] using hlt.le
  have hsum : ‖∑ ω, p ω • A ω‖ ≤
      ∑ ω, p ω * (t + M * (if t ≤ ‖A ω‖ then 1 else 0)) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro ω _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (prob_nonneg p ω)]
    exact mul_le_mul_of_nonneg_left (hpoint ω) (prob_nonneg p ω)
  have hevent : (∑ ω, p ω * (if t ≤ ‖A ω‖ then 1 else 0)) =
      finiteEventMass p {ω | t ≤ ‖A ω‖} := by
    simp only [finiteEventMass, Set.indicator_apply, Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]
  have hrewrite : (∑ ω, p ω * (t + M * (if t ≤ ‖A ω‖ then 1 else 0))) =
      t + M * finiteEventMass p {ω | t ≤ ‖A ω‖} := by
    simp_rw [mul_add, mul_left_comm (p _) M]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul,
      ← Finset.mul_sum, hevent]
  rw [hrewrite] at hsum
  exact hsum.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left htail hM))

theorem eventually_four_le_mul_nat_div_log {d : ℝ} (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop, 4 ≤ d * ((H : ℝ) / Real.log H) := by
  have hlogfour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h := eventually_log_four_le_mul_nat_div_log
    (show 0 < d * Real.log 4 / 4 by positivity)
  filter_upwards [h] with H hH
  apply (mul_le_mul_iff_left₀ hlogfour).mp
  nlinarith

/-- At one scale selected solely from the finite sequence, every active
prime graph has small exceptional probability under the actual harmonic
law. All constants and sampling thresholds precede the sequence. -/
theorem exists_logProb_primeGraph_small_tail
    {α : Type*} [Fintype α] [Nonempty α]
    (decode : α → ℂ) {B δ ρ κ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hdecode : ∀ a, ‖decode a‖ ≤ B) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J, ∀ (h : ℕ) (s : Finset ℕ),
        (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        finiteEventMass (logProbFiniteLaw L U hL (by omega))
          {n | ρ * entropyScale H₀ j / Real.log (entropyScale H₀ j) ≤
            ‖primeGraphDiscrepancy (decode ∘ F) (entropyScale H₀ j) h s n.1‖} ≤ κ := by
  classical
  obtain ⟨c, hc, H₁, hH₁, htail⟩ := exists_primeGraph_exponential_tail hB hδ hρ
  obtain ⟨H₂, hH₂⟩ := eventually_atTop.mp (eventually_four_le_mul_nat_div_log (mul_pos hc hκ))
  let H₀ := max Hmin (max H₁ H₂)
  have hH₀min : Hmin ≤ H₀ := le_max_left _ _
  have hH₀one : H₁ ≤ H₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hH₀two : H₂ ≤ H₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hH₀ : 2 ≤ H₀ := hH₁.trans hH₀one
  let τ := c * κ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let P : ℕ → ℕ := fun j ↦ primeGraphModulus (entropyScale H₀ j)
  let : ∀ j, NeZero (P j) := fun j ↦ instNeZeroPrimeGraphModulus _
  have hP (j : ℕ) : Real.log (P j) ≤ Real.log 4 * entropyScale H₀ j := by
    rw [show P j = primorial (entropyScale H₀ j) from primeGraphModulus_eq_primorial _]
    exact log_primorial_le_log_four_mul _
  obtain ⟨J, L₀, hJ, hL₀, hselect⟩ := exists_logProb_block_entropy_control (α := α)
    hH₀ hτ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)) P hP
  refine ⟨H₀, J, L₀, hH₀min, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL F
  obtain ⟨j, hj, hinfo, hdef⟩ := hselect L U hL hU hLL F
  refine ⟨j, hj, ?_⟩
  intro h s hs
  let H := entropyScale H₀ j
  have hHH₀ : H₀ ≤ H := le_entropyScale H₀ j
  have hHH₁ : H₁ ≤ H := hH₀one.trans hHH₀
  have hHH₂ : H₂ ≤ H := hH₀two.trans hHH₀
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  let E : (Fin H → α) → Finset (ZMod (primeGraphModulus H)) := fun b ↦
    Finset.univ.filter fun z ↦ ρ * H / Real.log H ≤
      ‖primeGraphSum (decode ∘ b) h s z - primeGraphMean (decode ∘ b) h s‖
  have hrare : ∀ b, ((E b).card : ℝ) * Real.exp (c * H / Real.log H) ≤ primeGraphModulus H := by
    intro b
    exact htail H hHH₁ (decode ∘ b) h s (fun i ↦ hdecode (b i)) hs
  have hprob := logProb_block_rare_event_le hL (by omega : L ≤ U) F E
    (show 0 < c * H / Real.log H by positivity) hrare hinfo hdef
  have hsmall : (τ * H / Real.log H + 2) / (c * H / Real.log H) ≤ κ := by
    apply (div_le_iff₀ (show 0 < c * H / Real.log H by positivity)).mpr
    have hlarge := hH₂ H hHH₂
    dsimp [τ]
    simp only [mul_div_assoc] at *
    nlinarith
  have hfinal := hprob.trans hsmall
  have hset : {n : LogProbIndex L U | (n.1 : ZMod (primeGraphModulus H)) ∈
      E (finiteSequenceBlock F H n.1)} =
      {n : LogProbIndex L U | ρ * H / Real.log H ≤
        ‖primeGraphDiscrepancy (decode ∘ F) H h s n.1‖} := by
    ext n
    change ((n.1 : ZMod (primeGraphModulus H)) ∈ E (finiteSequenceBlock F H n.1)) ↔ _
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hset] at hfinal
  exact hfinal

/-- Averaged graph decoupling with an arbitrarily small coefficient,
uniformly over finite-alphabet sequences and all eligible prime subsets.
This conclusion has no analytic input hypothesis. -/
theorem exists_logProb_primeGraph_decoupling
    {α : Type*} [Fintype α] [Nonempty α]
    (decode : α → ℂ) {B δ ε : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hε : 0 < ε)
    (hdecode : ∀ a, ‖decode a‖ ≤ B) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J, ∀ (h : ℕ) (s : Finset ℕ),
        (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U
          (primeGraphDiscrepancy (decode ∘ F) (entropyScale H₀ j) h s)‖ ≤
            ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  let R := primeGraphRadius B δ
  have hR : 0 < R := primeGraphRadius_pos hB hδ
  let ρ := ε / 2
  let κ := ε / (16 * R)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcoef : ρ + 8 * R * κ = ε := by
    dsimp [ρ, κ]
    field_simp
    ring
  obtain ⟨Hprime, hprime⟩ := eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  obtain ⟨H₀, J, L₀, hmin, hH₀, hJ, hL₀, hselect⟩ :=
    exists_logProb_primeGraph_small_tail decode hB hδ hρ hκ hdecode (max Hmin Hprime)
  refine ⟨H₀, J, L₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL F
  obtain ⟨j, hj, htail⟩ := hselect L U hL hU hLL F
  refine ⟨j, hj, ?_⟩
  intro h s hs
  let H := entropyScale H₀ j
  have hHlower : H₀ ≤ H := le_entropyScale H₀ j
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hcount := hprime H (((le_max_right _ _).trans hmin).trans hHlower)
  have hbound (n : LogProbIndex L U) :
      ‖primeGraphDiscrepancy (decode ∘ F) H h s n.1‖ ≤ 2 * (Nat.primeCounting H : ℝ) * R :=
    norm_primeGraphDiscrepancy_le (decode ∘ F) H h s hB.le hδ (fun n ↦ hdecode (F n)) hs n.1
  have hexp := norm_finiteExpectation_le_of_tail (logProbFiniteLaw L U hL (by omega))
    (fun n ↦ primeGraphDiscrepancy (decode ∘ F) H h s n.1)
    (show 0 ≤ ρ * H / Real.log H by positivity)
    (show 0 ≤ 2 * (Nat.primeCounting H : ℝ) * R by positivity)
    hbound (htail h s hs)
  change ‖logProbExpectation L U (primeGraphDiscrepancy (decode ∘ F) H h s)‖ ≤
    ρ * H / Real.log H + (2 * (Nat.primeCounting H : ℝ) * R) * κ at hexp
  have hmul := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 2 * R * κ by positivity)
  apply hexp.trans
  calc
    ρ * H / Real.log H + (2 * (Nat.primeCounting H : ℝ) * R) * κ ≤
        (ρ + 8 * R * κ) * ((H : ℝ) / Real.log H) := by
      rw [mul_div_assoc]
      nlinarith
    _ = ε * H / Real.log H := by rw [hcoef, mul_div_assoc]

end

end Erdos67b
