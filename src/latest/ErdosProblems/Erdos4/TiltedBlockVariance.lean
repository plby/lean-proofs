import ErdosProblems.Erdos4.TiltedNormalizerVariance
import ErdosProblems.Erdos4.TiltedGlobalCorrelation
import ErdosProblems.Erdos4.TiltedRootedGlobal

/-! Gcd moments give variance bounds for the actual unrooted and rooted block laws. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

theorem variance_of_exp_correlation {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : FiniteLaw Ω) (σ : FiniteLaw I) (E : I → Ω → Prop)
    (hE : ∀ i, ν.prob (E i) ≠ 0) {B b γ η : ℝ} (hB : 0 ≤ B)
    (hσ : ∀ i, σ.weight i ≤ b) (hdiag : ∀ i, 1 / ν.prob (E i) ≤ B)
    (G : I × I → ℝ) (hG : ∀ ij, 0 ≤ G ij)
    (hcross : ∀ i j, i ≠ j →
      ν.prob (fun o => E i o ∧ E j o) / (ν.prob (E i) * ν.prob (E j)) ≤ G (i, j) * Real.exp γ)
    (hmean : (pairLaw σ σ).mean G ≤ 1 + η) :
    ν.mean (fun o => (eventNormalizer ν σ E o - 1) ^ 2) ≤
      B * b + (Real.exp γ * (1 + η) - 1) := by
  apply eventNormalizer_variance_le ν σ E hE hB hσ hdiag
    (fun ij => G ij * Real.exp γ) (fun ij => mul_nonneg (hG ij) (Real.exp_pos _).le) hcross
  rw [FiniteLaw.mean_mul_const]
  have hh := mul_le_mul_of_nonneg_right hmean (Real.exp_pos γ).le
  linarith

theorem union_correlation_exponent_le {T U : Finset ℕ} {K Y : ℕ}
    (hT : T.card ≤ K) (hU : U.card ≤ K) (hY : 1 ≤ Y) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) :
    c * ((T ∪ U).card : ℝ) ^ 2 * Real.log Y / (w * Real.log 2) ≤
      c * (2 * (K : ℝ)) ^ 2 * Real.log Y / (w * Real.log 2) := by
  have hcard : (T ∪ U).card ≤ 2 * K := le_trans (Finset.card_union_le T U) (by omega)
  have hcardR : ((T ∪ U).card : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hcard
  apply div_le_div_of_nonneg_right _ (mul_nonneg hw.le (Real.log_nonneg (by norm_num)))
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hY))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcardR 2) hc

variable {P I : Type*} [Fintype P] [DecidableEq P] [Fintype I]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem disjoint_block_variance (hinj : Function.Injective ell) (τ : ℝ) (hτ : 0 ≤ τ)
    (σ : FiniteLaw I) (T : I → Finset ℕ) {K Y : ℕ}
    (hcard : ∀ i, (T i).card ≤ K) (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hsmall : ∀ l, 2 * K + 1 ≤ ell l) (hY : 1 ≤ Y)
    (hbound : ∀ i, ∀ n ∈ T i, n ≤ Y) {w B b η : ℝ} (hw : 0 < w)
    (hlarge : ∀ l, w ≤ ell l) (hB : 0 ≤ B) (hσ : ∀ i, σ.weight i ≤ b)
    (hdiag : ∀ i, 1 / (sieveLaw ell τ hτ).prob (fun a => Survives ell a (T i)) ≤ B)
    (hG : ∀ i j, Squarefree (blockGcd (T i) (T j)))
    (hcomplete : ∀ i j, ∀ p ∈ (blockGcd (T i) (T j)).primeFactors, ∃ l, ell l = p)
    (hmean : (pairLaw σ σ).mean (fun ij => (blockGcd (T ij.1) (T ij.2) : ℝ) ^ τ) ≤ 1 + η) :
    (sieveLaw ell τ hτ).mean (fun a =>
      (eventNormalizer (sieveLaw ell τ hτ) σ (fun i a => Survives ell a (T i)) a - 1) ^ 2) ≤
      B * b + (Real.exp ((2 + 8 * (K : ℝ)) * (2 * (K : ℝ)) ^ 2 * Real.log Y /
        (w * Real.log 2)) * (1 + η) - 1) := by
  apply variance_of_exp_correlation _ σ _ _ hB hσ hdiag
    (fun ij => (blockGcd (T ij.1) (T ij.2) : ℝ) ^ τ)
    (fun ij => Real.rpow_nonneg (Nat.cast_nonneg _) _) _ hmean
  · intro i
    exact (sieveLaw_survival_pos ell τ hτ (T i) (fun l => by
      have hc := hcard i
      have hs := hsmall l
      omega)).ne'
  · intro i j hij
    have heq : (fun a => Survives ell a (T i) ∧ Survives ell a (T j)) =
        (fun a => Survives ell a (T i ∪ T j)) := by
      funext a
      exact propext (survives_union ell a (T i) (T j)).symm
    rw [heq]
    have hh := sieveLaw_pair_ratio_uniform ell hinj τ hτ (T i) (T j) (hdis i j hij)
      (hcard i) (hcard j) hsmall hY
      (fun n hn => (Finset.mem_union.mp hn).elim (hbound i n) (hbound j n)) hw hlarge
      (hG i j) (hcomplete i j)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact Real.exp_le_exp.mpr (union_correlation_exponent_le (hcard i) (hcard j) hY hw (by positivity))

theorem rooted_block_variance (hinj : Function.Injective ell) (τ : ℝ) (hτ : 0 ≤ τ)
    (v : ℕ) (σ : FiniteLaw I) (T : I → Finset ℕ) {K Y : ℕ}
    (hcard : ∀ i, (T i).card ≤ K) (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hroot : ∀ i l, (v : ZMod (ell l)) ∉ residues ell (T i) l)
    (hsmall : ∀ l, 2 * (K + 1) + 1 ≤ ell l) (hY : 1 ≤ Y)
    (hbound : ∀ i, ∀ n ∈ T i, n ≤ Y) {w B b η : ℝ} (hw : 0 < w)
    (hlarge : ∀ l, w ≤ ell l) (hB : 0 ≤ B) (hσ : ∀ i, σ.weight i ≤ b)
    (hpos : ∀ i, (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a (T i)) ≠ 0)
    (hdiag : ∀ i, 1 / (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a (T i)) ≤ B)
    (hG : ∀ i j, Squarefree (blockGcd (T i) (T j)))
    (hcomplete : ∀ i j, ∀ p ∈ (blockGcd (T i) (T j)).primeFactors, ∃ l, ell l = p)
    (hmean : (pairLaw σ σ).mean (fun ij => (blockGcd (T ij.1) (T ij.2) : ℝ) ^ τ) ≤ 1 + η) :
    (rootedSieveLaw ell τ hτ v).mean (fun a =>
      (eventNormalizer (rootedSieveLaw ell τ hτ v) σ (fun i a => Survives ell a (T i)) a - 1) ^ 2) ≤
      B * b + (Real.exp (8 * ((K : ℝ) + 1) * (2 * (K : ℝ)) ^ 2 * Real.log Y /
        (w * Real.log 2)) * (1 + η) - 1) := by
  apply variance_of_exp_correlation _ σ _ hpos hB hσ hdiag
    (fun ij => (blockGcd (T ij.1) (T ij.2) : ℝ) ^ τ)
    (fun ij => Real.rpow_nonneg (Nat.cast_nonneg _) _) _ hmean
  intro i j hij
  have heq : (fun a => Survives ell a (T i) ∧ Survives ell a (T j)) =
      (fun a => Survives ell a (T i ∪ T j)) := by
    funext a
    exact propext (survives_union ell a (T i) (T j)).symm
  rw [heq]
  have hh := rootedSieveLaw_pair_ratio_uniform ell hinj τ hτ v (T i) (T j) (hroot i) (hroot j)
    (hdis i j hij) (hcard i) (hcard j) hsmall hY
    (fun n hn => (Finset.mem_union.mp hn).elim (hbound i n) (hbound j n)) hw hlarge
    (hG i j) (hcomplete i j)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact Real.exp_le_exp.mpr (union_correlation_exponent_le (hcard i) (hcard j) hY hw (by positivity))

end Erdos4.Tilted
