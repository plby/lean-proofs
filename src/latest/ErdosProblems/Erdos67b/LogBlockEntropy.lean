import ErdosProblems.Erdos67b.EntropyScale
import ErdosProblems.Erdos67b.LogTranslation
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Primorial

/-!
# Entropy continuity for logarithmically sampled finite blocks

The lower sampling endpoint is chosen after the finite alphabets and
shift range, uniformly over the values of the sampled functions.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.FiniteEntropy

theorem exists_delta_condEntropy_sub_abs_lt
    {α β : Type*} [Fintype α] [Fintype β] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : FinProb (α × β),
      l1Dist p q < δ → |condEntropy p - condEntropy q| < ε := by
  have hu : UniformContinuous (condEntropy : FinProb (α × β) → ℝ) :=
    CompactSpace.uniformContinuous_of_continuous continuous_condEntropy
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.1 hu) ε hε
  refine ⟨δ, hδ, fun p q hpq ↦ hmod ?_⟩
  have hdist : dist p q ≤ l1Dist p q := by
    change dist (p : (α × β) → ℝ) (q : (α × β) → ℝ) ≤ l1Dist p q
    rw [dist_pi_le_iff (l1Dist_nonneg p q)]
    intro z
    rw [Real.dist_eq]
    exact Finset.single_le_sum (fun w _ ↦ abs_nonneg (p w - q w)) (Finset.mem_univ z)
  exact hdist.trans_lt hpq

theorem rvEntropy_equiv
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    (p : FinProb Ω) (X : Ω → α) (e : α ≃ β) :
    rvEntropy p (e ∘ X) = rvEntropy p X := by
  apply le_antisymm (rvEntropy_comp_le p X e)
  have h := rvEntropy_comp_le p (e ∘ X) e.symm
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

/-- Conditional entropy is unchanged by an invertible recoding of the
conditioning variable. -/
theorem rvCondEntropy_condition_equiv
    {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) (e : β ≃ γ) :
    rvCondEntropy p X (e ∘ Y) = rvCondEntropy p X Y := by
  have hpair := rvEntropy_equiv p (fun ω ↦ (X ω, Y ω))
    (Equiv.prodCongr (Equiv.refl α) e)
  change rvEntropy p (fun ω ↦ (X ω, e (Y ω))) = rvEntropy p (fun ω ↦ (X ω, Y ω)) at hpair
  simp only [rvCondEntropy_eq_sub, Function.comp_apply, hpair, rvEntropy_equiv]

theorem rvCondEntropy_condition_add
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β] [AddCommGroup β]
    (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) (c : β) :
    rvCondEntropy p X (fun ω ↦ Y ω + c) = rvCondEntropy p X Y := by
  let e : β ≃ β := ⟨fun z ↦ z + c, fun z ↦ z - c,
    (fun z ↦ add_sub_cancel_right z c), (fun z ↦ sub_add_cancel z c)⟩
  exact rvCondEntropy_condition_equiv p X Y e

end Erdos67b.FiniteEntropy

namespace Erdos67b

open FiniteEntropy

/-- Uniform continuity of joint conditional entropy under simultaneous
translation of two arbitrary finite-valued observables. -/
theorem exists_logProb_condEntropy_translate_close
    {α β : Type*} [Fintype α] [Fintype β] {ε : ℝ} (hε : 0 < ε) (S : ℕ) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U),
      L₀ ≤ L → ∀ (F : ℕ → α) (G : ℕ → β) (h : ℕ), h ≤ S →
      |rvCondEntropy (logProbFiniteLaw L U hL (by omega))
          (fun n ↦ F (n.1 + h)) (fun n ↦ G (n.1 + h)) -
        rvCondEntropy (logProbFiniteLaw L U hL (by omega))
          (fun n ↦ F n.1) (fun n ↦ G n.1)| < ε := by
  obtain ⟨δ, hδ, hmod⟩ := exists_delta_condEntropy_sub_abs_lt (α := α) (β := β) hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * Fintype.card (α × β) * S / δ)
  refine ⟨N + 1, Nat.succ_pos _, ?_⟩
  intro L U hL hU hNL F G h hh
  apply hmod
  have hdist := l1Dist_logProb_law_translate_le_of_double hL hU h (fun n ↦ (F n, G n))
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hNl : (N : ℝ) < L := by exact_mod_cast (show N < L by omega)
  have hsmall : 4 * Fintype.card (α × β) * (S : ℝ) / L < δ := by
    apply (div_lt_iff₀ hLr).mpr
    have h := (div_lt_iff₀ hδ).mp (hN.trans hNl)
    simpa only [mul_comm] using h
  have hshift : 4 * Fintype.card (α × β) * (h : ℝ) / L ≤
      4 * Fintype.card (α × β) * (S : ℝ) / L := by
    gcongr
  exact hdist.trans_lt (hshift.trans_lt hsmall)

/-- Residue recoding removes the translation from the conditioning
variable, as required for relative block subadditivity. -/
theorem exists_logProb_residue_condEntropy_translate_close
    {α : Type*} [Fintype α] (P : ℕ) [NeZero P]
    {ε : ℝ} (hε : 0 < ε) (S : ℕ) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U),
      L₀ ≤ L → ∀ (F : ℕ → α) (h : ℕ), h ≤ S →
      |rvCondEntropy (logProbFiniteLaw L U hL (by omega))
          (fun n ↦ F (n.1 + h)) (fun n ↦ (n.1 : ZMod P)) -
        rvCondEntropy (logProbFiniteLaw L U hL (by omega))
          (fun n ↦ F n.1) (fun n ↦ (n.1 : ZMod P))| < ε := by
  obtain ⟨L₀, hL₀, hclose⟩ :=
    exists_logProb_condEntropy_translate_close (α := α) (β := ZMod P) hε S
  refine ⟨L₀, hL₀, ?_⟩
  intro L U hL hU hLL F h hh
  have hclose' := hclose L U hL hU hLL F (fun n ↦ (n : ZMod P)) h hh
  simpa only [Nat.cast_add, rvCondEntropy_condition_add] using hclose'

/-- A finite block starts at the next positive offset. -/
def finiteSequenceBlock {α : Type*} (F : ℕ → α) (H n : ℕ) : Fin H → α :=
  fun i ↦ F (n + i.1 + 1)

/-- Decode consecutive blocks using the standard quotient/remainder
equivalence on finite indices. -/
theorem finiteSequenceBlock_decode
    {α : Type*} (F : ℕ → α) (H k n : ℕ) :
    (fun i : Fin (k * H) ↦
      finiteSequenceBlock F H (n + (finProdFinEquiv.symm i).1.1 * H)
        (finProdFinEquiv.symm i).2) = finiteSequenceBlock F (k * H) n := by
  funext i
  have hi := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
  change (finProdFinEquiv.symm i).2.1 + H * (finProdFinEquiv.symm i).1.1 = i.1 at hi
  rw [Nat.mul_comm H _] at hi
  simp only [finiteSequenceBlock]
  congr 1
  omega

/-- The entropy-rate recurrence for actual logarithmically sampled
sequence blocks. The threshold is uniform over the arbitrary sequence;
only the finite alphabets, block parameters, modulus, and error are fixed. -/
theorem exists_logProb_block_entropy_rate_decrement
    {α : Type*} [Fintype α] {H k : ℕ} (hH : 0 < H) (hk : 0 < k)
    (P : ℕ) [NeZero P] {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U),
      L₀ ≤ L → ∀ (F : ℕ → α) (C : ℝ), Real.log P ≤ C * H →
      rvEntropy (logProbFiniteLaw L U hL (by omega))
          (fun n ↦ finiteSequenceBlock F (k * H) n.1) / (k * H : ℕ) ≤
        rvEntropy (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ finiteSequenceBlock F H n.1) / H -
          rvMutualInfo (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ finiteSequenceBlock F H n.1) (fun n ↦ (n.1 : ZMod P)) / H +
          C / k + ε / H := by
  obtain ⟨L₀, hL₀, hclose⟩ :=
    exists_logProb_residue_condEntropy_translate_close (α := Fin H → α) P hε (k * H)
  refine ⟨L₀, hL₀, ?_⟩
  intro L U hL hU hLL F C hP
  let p := logProbFiniteLaw L U hL (show L ≤ U by omega)
  let Y : LogProbIndex L U → ZMod P := fun n ↦ n.1
  let Xref : LogProbIndex L U → Fin H → α := fun n ↦ finiteSequenceBlock F H n.1
  let X : LogProbIndex L U → Fin k → Fin H → α :=
    fun n i ↦ finiteSequenceBlock F H (n.1 + i.1 * H)
  let decode : (Fin k → Fin H → α) → Fin (k * H) → α :=
    fun b i ↦ b (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hshift : ∀ i, rvCondEntropy p (fun n ↦ X n i) Y ≤ rvCondEntropy p Xref Y + ε := by
    intro i
    have hi : i.1 * H ≤ k * H := Nat.mul_le_mul_right H i.isLt.le
    have h := hclose L U hL hU hLL (finiteSequenceBlock F H) (i.1 * H) hi
    have h' := (abs_lt.mp h).2.le
    change rvCondEntropy p (fun n ↦ X n i) Y - rvCondEntropy p Xref Y ≤ ε at h'
    linarith
  have hY : rvEntropy p Y ≤ Real.log P := by
    have h := entropy_le_log_card (law p Y)
    simpa only [rvEntropy, ZMod.card] using h
  have hrate := rvEntropy_rate_decrement p Y hk X Xref decode (Nat.cast_pos.mpr hH)
    C ε (hY.trans hP) hshift
  have hdecode : decode ∘ X = fun n ↦ finiteSequenceBlock F (k * H) n.1 := by
    funext n
    exact finiteSequenceBlock_decode F H k n.1
  rw [hdecode] at hrate
  simpa only [p, Y, Xref, Nat.cast_mul] using hrate

/-- The entropy rate of an arbitrary finite-alphabet block is uniformly
bounded by the logarithm of the alphabet size. -/
theorem rvEntropy_finiteSequenceBlock_le
    {Ω α : Type*} [Fintype Ω] [Fintype α] [Nonempty α]
    (p : FinProb Ω) (n : Ω → ℕ) (F : ℕ → α) (H : ℕ) :
    rvEntropy p (fun ω ↦ finiteSequenceBlock F H (n ω)) ≤
      H * Real.log (Fintype.card α) := by
  have h := entropy_le_log_card (law p (fun ω ↦ finiteSequenceBlock F H (n ω)))
  simpa only [rvEntropy, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

/-- Entropy decrement for actual logarithmic block laws. The modulus
growth bound is explicit; in the prime-graph application it is supplied
by a Chebyshev estimate. All thresholds precede the arbitrary sequence. -/
theorem exists_logProb_block_small_mutualInfo
    {α : Type*} [Fintype α] [Nonempty α]
    {H₀ : ℕ} (hH₀ : 2 ≤ H₀) {τ C : ℝ} (hτ : 0 < τ) (hC : 0 ≤ C)
    (P : ℕ → ℕ) [∀ j, NeZero (P j)]
    (hP : ∀ j, Real.log (P j) ≤ C * entropyScale H₀ j) :
    ∃ J L₀ : ℕ, 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J,
        rvMutualInfo (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ finiteSequenceBlock F (entropyScale H₀ j) n.1)
            (fun n ↦ (n.1 : ZMod (P j))) ≤
          τ * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  classical
  have hK : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ Fintype.card α from Fintype.card_pos))
  obtain ⟨J, hJ, hselect⟩ := exists_finite_entropy_scale hH₀ hτ hK hC
  let e : ℝ := 1 / J
  have he : 0 < e := one_div_pos.mpr (Nat.cast_pos.mpr hJ)
  have hscale (j : ℕ) : 0 < entropyScale H₀ j :=
    lt_of_lt_of_le (by omega : 0 < H₀) (le_entropyScale H₀ j)
  have hstepExists (j : ℕ) := exists_logProb_block_entropy_rate_decrement
    (α := α) (hscale j) (show 0 < (j + 2) ^ 2 by positivity) (P j) he
  choose T hT hstep using hstepExists
  refine ⟨J, (Finset.range J).sup T + 1, hJ, Nat.succ_pos _, ?_⟩
  intro L U hL hU hLL F
  let p := logProbFiniteLaw L U hL (show L ≤ U by omega)
  let R : ℕ → ℝ := fun j ↦
    rvEntropy p (fun n ↦ finiteSequenceBlock F (entropyScale H₀ j) n.1) / entropyScale H₀ j
  let I : ℕ → ℝ := fun j ↦
    rvMutualInfo p (fun n ↦ finiteSequenceBlock F (entropyScale H₀ j) n.1)
      (fun n ↦ (n.1 : ZMod (P j)))
  apply hselect R I e
  · exact div_nonneg (entropy_nonneg _) (Nat.cast_nonneg _)
  · change rvEntropy p (fun n ↦ finiteSequenceBlock F (entropyScale H₀ 0) n.1) /
        entropyScale H₀ 0 ≤ _
    rw [entropyScale_zero]
    apply (div_le_iff₀ (show (0 : ℝ) < H₀ by exact_mod_cast (show 0 < H₀ by omega))).mpr
    have h := rvEntropy_finiteSequenceBlock_le p Subtype.val F H₀
    simpa only [mul_comm] using h
  · change (J : ℝ) * (1 / J) ≤ 1
    rw [mul_one_div_cancel (ne_of_gt (Nat.cast_pos.mpr hJ))]
  · intro j hj
    have hTL : T j ≤ L :=
      (Finset.le_sup (f := T) (Finset.mem_range.mpr hj)).trans (by omega)
    have hrec := hstep j L U hL hU hTL F C (hP j)
    rw [← entropyScale_succ H₀ j] at hrec
    have heH : e / entropyScale H₀ j ≤ e :=
      div_le_self he.le (by exact_mod_cast (hscale j))
    change R (j + 1) ≤ R j - I j / entropyScale H₀ j +
      C / (((j + 2 : ℕ) : ℝ) ^ 2) + e
    have hrec' : R (j + 1) ≤ R j - I j / entropyScale H₀ j +
        C / (((j + 2 : ℕ) : ℝ) ^ 2) + e / entropyScale H₀ j := by
      simpa only [R, I, p, Nat.cast_pow] using hrec
    linarith

/-- The required prime-modulus entropy budget is elementary Chebyshev,
using the already proved primorial bound rather than an analytic axiom. -/
theorem log_primorial_le_log_four_mul (H : ℕ) :
    Real.log (primorial H) ≤ Real.log 4 * H := by
  have hbound : (primorial H : ℝ) ≤ (4 : ℝ) ^ H := by
    exact_mod_cast primorial_le_four_pow H
  have h := Real.log_le_log (Nat.cast_pos.mpr (primorial_pos H)) hbound
  simpa only [Real.log_pow, mul_comm] using h

/-- Every primorial is a positive modulus. -/
instance instNeZeroPrimorial (H : ℕ) : NeZero (primorial H) := ⟨primorial_ne_zero H⟩

/-- Unconditional entropy decrement for arbitrary finite-alphabet
sequences, conditioning on every prime residue up to the selected scale. -/
theorem exists_logProb_primorial_block_small_mutualInfo
    {α : Type*} [Fintype α] [Nonempty α]
    {H₀ : ℕ} (hH₀ : 2 ≤ H₀) {τ : ℝ} (hτ : 0 < τ) :
    ∃ J L₀ : ℕ, 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J,
        rvMutualInfo (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ finiteSequenceBlock F (entropyScale H₀ j) n.1)
            (fun n ↦ (n.1 : ZMod (primorial (entropyScale H₀ j)))) ≤
          τ * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  let : ∀ j, NeZero (primorial (entropyScale H₀ j)) :=
    fun j ↦ ⟨primorial_ne_zero _⟩
  exact exists_logProb_block_small_mutualInfo hH₀ hτ
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    (fun j ↦ primorial (entropyScale H₀ j)) (fun j ↦ log_primorial_le_log_four_mul _)

end Erdos67b
