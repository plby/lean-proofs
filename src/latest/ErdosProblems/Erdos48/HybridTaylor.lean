/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.HybridLargeSieve
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Taylor recovery of hybrid Dirichlet phases

After splitting an additive interval into short blocks, write the frequency
attached to `n` as a block centre plus a small offset.  Expanding the offset
exponential gives the block polynomials controlled by `HybridLargeSieve`.
This file records both the exact finite Taylor expansion and its uniform
convergence on a bounded `t`-interval.
-/

open scoped BigOperators Topology Interval
open Filter Set

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

private theorem summable_finset_sum
    {α : Type*} {S : Finset α} {f : α → ℕ → ℂ}
    (hf : ∀ a ∈ S, Summable (f a)) :
    Summable (fun k ↦ ∑ a ∈ S, f a k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℂ)))
  | @insert a S ha ih =>
      have hadd :=
        (hf a (by simp)).add (ih fun b hb ↦ hf b (by simp [hb]))
      have hfun :
          (fun k ↦ ∑ b ∈ insert a S, f b k) =
            (fun k ↦ f a k + ∑ b ∈ S, f b k) := by
        funext k
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact hadd

/-- Uniform convergence of continuous complex functions on a compact real
interval permits passage to the integrals of their squared norms. -/
theorem TendstoUniformlyOn.tendsto_intervalIntegral_norm_sq_of_continuousOn
    {κ : Type*} {l : Filter κ} [l.IsCountablyGenerated]
    {F : κ → ℝ → ℂ} {f : ℝ → ℂ} {a b : ℝ}
    (hF : ∀ᶠ k in l, ContinuousOn (F k) [[a, b]])
    (hlim : TendstoUniformlyOn F f l [[a, b]]) :
    Tendsto (fun k ↦ ∫ t in a..b, ‖F k t‖ ^ 2) l
      (𝓝 (∫ t in a..b, ‖f t‖ ^ 2)) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rcases isCompact_uIcc.bddAbove_image
      (hlim.continuousOn hF.frequently).norm with ⟨C, hC⟩
  have hnormUniform :=
    uniformContinuous_norm.comp_tendstoUniformlyOn hlim
  have hnormBound : ∀ᶠ k in l, ∀ t ∈ [[a, b]], ‖F k t‖ ≤ C + 1 :=
    hnormUniform.eventually_forall_le (show C < C + 1 by simp)
      (by simpa [upperBounds] using hC)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ (C + 1) ^ 2)
  · exact hF.mono fun k hk ↦
      ((hk.norm.pow 2).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
  · filter_upwards [hnormBound] with k hk
    exact Filter.Eventually.of_forall fun t ht ↦ by
      have hnonneg : 0 ≤ ‖F k t‖ := norm_nonneg _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ hnonneg (hk t (uIoc_subset_uIcc ht)) 2
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht ↦
      ((hlim.tendsto_at (uIoc_subset_uIcc ht)).norm.pow 2)

/-- The `R`-term Taylor approximation to a block-frequency polynomial. -/
noncomputable def primitiveHybridTaylorPolynomial
    {ι : Type*} [Fintype ι]
    (R : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) (t : ℝ) : ℂ :=
  blockTaylorPolynomial R x
    (fun k i ↦ ∑ n ∈ s i, c n * (d n : ℂ) ^ k * psi.1 n) t

/-- The exact polynomial before expanding the small within-block offsets. -/
noncomputable def primitiveHybridPolynomial
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) (t : ℝ) : ℂ :=
  ∑ i, ∑ n ∈ s i,
    c n * psi.1 n *
      Complex.exp (Complex.I * (((t * (x i + d n)) : ℝ) : ℂ))

/-- Weighted primitive-character mass of the finite Taylor approximation. -/
noncomputable def primitiveHybridTaylorMass
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2

/-- Weighted primitive-character mass of the exact hybrid polynomial. -/
noncomputable def primitiveHybridMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        ‖primitiveHybridPolynomial x s c d q psi t‖ ^ 2

/-- The block-frequency mass at one fixed Taylor order. -/
noncomputable def primitiveBlockFrequencyMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        ‖realFrequencyPolynomial x
          (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) t‖ ^ 2

@[fun_prop] theorem continuous_primitiveHybridTaylorPolynomial
    {ι : Type*} [Fintype ι]
    (R : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) :
    Continuous (primitiveHybridTaylorPolynomial R x s c d q psi) := by
  unfold primitiveHybridTaylorPolynomial blockTaylorPolynomial
    realFrequencyPolynomial
  fun_prop

@[fun_prop] theorem continuous_primitiveHybridPolynomial
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) :
    Continuous (primitiveHybridPolynomial x s c d q psi) := by
  unfold primitiveHybridPolynomial
  fun_prop

private theorem norm_taylorTerm_sq_div_inv
    (k : ℕ) (t : ℝ) (z : ℂ) (ht : 0 ≤ t) :
    ‖(Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ) * z‖ ^ 2 /
        ((k.factorial : ℝ))⁻¹ =
      t ^ (2 * k) / (k.factorial : ℝ) * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
    Complex.norm_natCast, one_mul]
  have hfac : (0 : ℝ) < k.factorial := by positivity
  field_simp
  ring

/-- Pointwise Cauchy--Schwarz bound for the Taylor approximation, with the
factorial weights simplified to a form suited for integration. -/
theorem norm_primitiveHybridTaylorPolynomial_sq_le
    {ι : Type*} [Fintype ι]
    (R : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) (t : ℝ) (ht : 0 ≤ t) :
    ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2 ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        ∑ k ∈ Finset.range R,
          t ^ (2 * k) / (k.factorial : ℝ) *
            ‖realFrequencyPolynomial x
              (fun i ↦ ∑ n ∈ s i,
                c n * (d n : ℂ) ^ k * psi.1 n) t‖ ^ 2 := by
  unfold primitiveHybridTaylorPolynomial
  refine (norm_blockTaylorPolynomial_sq_le R x
    (fun k i ↦ ∑ n ∈ s i,
      c n * (d n : ℂ) ^ k * psi.1 n) t).trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact norm_taylorTerm_sq_div_inv k t _ ht

/-- Regrouping the finite Taylor approximation by its Taylor order gives the
block polynomial used by the hybrid large sieve. -/
theorem primitiveHybridTaylorPolynomial_eq
    {ι : Type*} [Fintype ι]
    (R : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) (t : ℝ) :
    primitiveHybridTaylorPolynomial R x s c d q psi t =
      ∑ i, ∑ n ∈ s i,
        c n * psi.1 n *
          Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)) *
            (∑ k ∈ Finset.range R,
              (Complex.I * (((t * d n) : ℝ) : ℂ)) ^ k /
                (k.factorial : ℂ)) := by
  classical
  unfold primitiveHybridTaylorPolynomial blockTaylorPolynomial
    realFrequencyPolynomial
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

/-- The block Taylor approximations converge uniformly to the exact hybrid
polynomial on every bounded nonnegative interval. -/
theorem tendstoUniformlyOn_primitiveHybridTaylorPolynomial
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    TendstoUniformlyOn
      (fun R t ↦ primitiveHybridTaylorPolynomial R x s c d q psi t)
      (primitiveHybridPolynomial x s c d q psi) atTop [[0, T]] := by
  classical
  let f : ℕ → ℝ → ℂ := fun k t ↦
    ∑ i, ∑ n ∈ s i,
      c n * psi.1 n *
        Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)) *
          ((Complex.I * (((t * d n) : ℝ) : ℂ)) ^ k /
            (k.factorial : ℂ))
  let A : ℝ := ∑ i, ∑ n ∈ s i, ‖c n‖
  let u : ℕ → ℝ := fun k ↦ A * (T * B) ^ k / k.factorial
  have hu : Summable u := by
    simpa only [u, mul_div_assoc] using
      (Real.summable_pow_div_factorial (T * B)).mul_left A
  have hfbound : ∀ k t, t ∈ [[0, T]] → ‖f k t‖ ≤ u k := by
    intro k t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht0 : 0 ≤ t := ht.1
    have htT : t ≤ T := ht.2
    unfold f u A
    calc
      ‖∑ i, ∑ n ∈ s i,
          c n * psi.1 n *
            Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)) *
              ((Complex.I * (((t * d n) : ℝ) : ℂ)) ^ k /
                (k.factorial : ℂ))‖ ≤
          ∑ i, ∑ n ∈ s i,
            ‖c n * psi.1 n *
              Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)) *
                ((Complex.I * (((t * d n) : ℝ) : ℂ)) ^ k /
                  (k.factorial : ℂ))‖ := by
        exact (norm_sum_le _ _).trans <|
          Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
      _ ≤ ∑ i, ∑ n ∈ s i,
          ‖c n‖ * ((T * B) ^ k / k.factorial) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp]
        have him :
            (Complex.I * (((t * x i) : ℝ) : ℂ)).re = 0 := by simp
        rw [him, Real.exp_zero, mul_one]
        have hpsi : ‖psi.1 n‖ ≤ 1 :=
          DirichletCharacter.norm_le_one psi.1 (n : ZMod q)
        have htd : |t * d n| ≤ T * B := by
          rw [abs_mul, abs_of_nonneg ht0]
          exact mul_le_mul htT (hd i n hn) (abs_nonneg _) hT
        have hpow : |t * d n| ^ k ≤ (T * B) ^ k :=
          pow_le_pow_left₀ (abs_nonneg _) htd k
        have hfac : (0 : ℝ) ≤ k.factorial := by positivity
        calc
          ‖c n‖ * ‖psi.1 n‖ *
              ‖(Complex.I * (((t * d n) : ℝ) : ℂ)) ^ k /
                (k.factorial : ℂ)‖ ≤
              ‖c n‖ * 1 *
                (|t * d n| ^ k / k.factorial) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hpsi (norm_nonneg _)
            · rw [norm_div, norm_pow, norm_mul, Complex.norm_I,
                Complex.norm_real, Real.norm_eq_abs, one_mul,
                Complex.norm_natCast]
            · positivity
            · positivity
          _ ≤ ‖c n‖ * ((T * B) ^ k / k.factorial) := by
            simp only [mul_one]
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hpow hfac) (norm_nonneg _)
      _ = (∑ i, ∑ n ∈ s i, ‖c n‖) *
          (T * B) ^ k / k.factorial := by
        calc
          (∑ i, ∑ n ∈ s i,
              ‖c n‖ * ((T * B) ^ k / k.factorial)) =
              (∑ i, ∑ n ∈ s i, ‖c n‖) *
                ((T * B) ^ k / k.factorial) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          _ = _ := by ring
      _ = _ := rfl
  have huniform := tendstoUniformlyOn_tsum_nat hu hfbound
  have hpoint (t : ℝ) : (∑' k, f k t) =
      primitiveHybridPolynomial x s c d q psi t := by
    unfold f primitiveHybridPolynomial
    rw [Summable.tsum_finsetSum (fun i _ ↦
      summable_finset_sum (fun n hn ↦
        (NormedSpace.expSeries_div_hasSum_exp
          (Complex.I * (((t * d n) : ℝ) : ℂ))).summable.mul_left
            (c n * psi.1 n *
              Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Summable.tsum_finsetSum (fun n hn ↦
      (NormedSpace.expSeries_div_hasSum_exp
        (Complex.I * (((t * d n) : ℝ) : ℂ))).summable.mul_left
          (c n * psi.1 n *
            Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ))))]
    apply Finset.sum_congr rfl
    intro n hn
    calc
      (∑' b : ℕ,
          c n * psi.1 n *
            Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)) *
              ((Complex.I * (((t * d n) : ℝ) : ℂ)) ^ b /
                (b.factorial : ℂ))) =
          c n * psi.1 n *
            Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)) *
              Complex.exp (Complex.I * (((t * d n) : ℝ) : ℂ)) :=
        by simpa only [Complex.exp_eq_exp_ℂ] using
          ((NormedSpace.expSeries_div_hasSum_exp
            (Complex.I * (((t * d n) : ℝ) : ℂ))).mul_left
              (c n * psi.1 n *
                Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)))).tsum_eq
      _ = c n * psi.1 n *
          Complex.exp (Complex.I * (((t * (x i + d n)) : ℝ) : ℂ)) := by
        rw [show Complex.I * (((t * (x i + d n)) : ℝ) : ℂ) =
          Complex.I * (((t * x i) : ℝ) : ℂ) +
            Complex.I * (((t * d n) : ℝ) : ℂ) by
              push_cast
              ring,
          Complex.exp_add]
        ring
  apply (huniform.congr (Filter.Eventually.of_forall fun R t ht ↦ ?_)).congr_right
  · intro t ht
    exact hpoint t
  · rw [primitiveHybridTaylorPolynomial_eq]
    unfold f
    dsimp only
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simpa only using (Finset.mul_sum (Finset.range R)
      (fun k ↦ (Complex.I * (((t * d n) : ℝ) : ℂ)) ^ k /
        (k.factorial : ℂ))
      (c n * psi.1 n *
        Complex.exp (Complex.I * (((t * x i) : ℝ) : ℂ)))).symm

/-- If each block centre plus its within-block offset is the logarithm of
the underlying integer, the recovered hybrid polynomial is the ordinary
Dirichlet polynomial on those blocks.  Keeping the right-hand side as a
double sum avoids imposing disjointness before it is needed by an
application. -/
theorem primitiveHybridPolynomial_eq_dirichletPhase
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) (t : ℝ)
    (hlog : ∀ i, ∀ n ∈ s i, x i + d n = Real.log n) :
    primitiveHybridPolynomial x s c d q psi t =
      ∑ i, ∑ n ∈ s i,
        c n * psi.1 n *
          Complex.exp (Complex.I * (((t * Real.log n) : ℝ) : ℂ)) := by
  classical
  unfold primitiveHybridPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro n hn
  rw [hlog i n hn]

/-- Choose the logarithmic offset belonging to the unique block containing
`n`.  The value away from all blocks is irrelevant and is set to zero. -/
noncomputable def blockLogOffset
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s : ι → Finset ℕ) (n : ℕ) : ℝ :=
  if h : ∃ i, n ∈ s i then
    Real.log n - x (Classical.choose h)
  else 0

/-- On pairwise disjoint blocks, `blockLogOffset` uses the prescribed block
centre, independently of the witness selected in its definition. -/
theorem blockLogOffset_eq
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s : ι → Finset ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (i : ι) {n : ℕ} (hn : n ∈ s i) :
    blockLogOffset x s n = Real.log n - x i := by
  classical
  unfold blockLogOffset
  rw [dif_pos ⟨i, hn⟩]
  let j := Classical.choose (show ∃ j, n ∈ s j from ⟨i, hn⟩)
  have hj : n ∈ s j :=
    Classical.choose_spec (show ∃ j, n ∈ s j from ⟨i, hn⟩)
  have hji : j = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj j i hne) hj hn)
  rw [show Classical.choose (show ∃ j, n ∈ s j from ⟨i, hn⟩) = i by
    exact hji]

/-- The ordinary Dirichlet-polynomial mass after a finite support has been
split into blocks. -/
noncomputable def primitiveDirichletBlockMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (s : ι → Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        ‖∑ i, ∑ n ∈ s i,
          c n * psi.1 n *
            Complex.exp (Complex.I * (((t * Real.log n) : ℝ) : ℂ))‖ ^ 2

theorem primitiveHybridMass_blockLogOffset_eq
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j)) (t : ℝ) :
    primitiveHybridMass Q x s c (blockLogOffset x s) t =
      primitiveDirichletBlockMass Q s c t := by
  classical
  unfold primitiveHybridMass primitiveDirichletBlockMass
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun z : ℝ ↦ (q : ℝ) / (q.totient : ℝ) * z)
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [primitiveHybridPolynomial_eq_dirichletPhase
    x s c (blockLogOffset x s) q psi t fun i n hn ↦ by
        rw [blockLogOffset_eq x s hdisj i hn]
        ring]

/-- Integral convergence for one primitive character. -/
theorem tendsto_intervalIntegral_primitiveHybridTaylorPolynomial_norm_sq
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (q : ℕ)
    (psi : primitiveCharacters q) {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    Tendsto (fun R ↦ ∫ t in (0 : ℝ)..T,
        ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2)
      atTop
      (𝓝 (∫ t in (0 : ℝ)..T,
        ‖primitiveHybridPolynomial x s c d q psi t‖ ^ 2)) := by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_norm_sq_of_continuousOn
      (Filter.Eventually.of_forall fun R ↦
        (continuous_primitiveHybridTaylorPolynomial R x s c d q psi).continuousOn)
  exact tendstoUniformlyOn_primitiveHybridTaylorPolynomial
    x s c d q psi hT hB hd

theorem continuous_primitiveHybridTaylorMass
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) :
    Continuous (primitiveHybridTaylorMass R Q x s c d) := by
  unfold primitiveHybridTaylorMass
  fun_prop

theorem continuous_primitiveHybridMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) :
    Continuous (primitiveHybridMass Q x s c d) := by
  unfold primitiveHybridMass
  fun_prop

theorem continuous_primitiveBlockFrequencyMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) :
    Continuous (primitiveBlockFrequencyMass Q x s c) := by
  classical
  unfold primitiveBlockFrequencyMass
  apply continuous_finsetSum (Finset.Ioc 0 Q)
  intro q hq
  apply continuous_const.mul
  apply continuous_finsetSum Finset.univ
  intro psi hpsi
  exact (continuous_realFrequencyPolynomial x
    (fun i ↦ ∑ n ∈ s i, c n * psi.1 n)).norm.pow 2

theorem intervalIntegral_primitiveHybridTaylorMass_eq
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        primitiveHybridTaylorMass R Q x s c d t) =
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            (∫ t in (0 : ℝ)..T,
              ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2) := by
  classical
  unfold primitiveHybridTaylorMass
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum]
    intro psi hpsi
    exact ((continuous_primitiveHybridTaylorPolynomial
      R x s c d q psi).norm.pow 2).intervalIntegrable 0 T
  · intro q hq
    apply Continuous.intervalIntegrable
    apply continuous_const.mul
    apply continuous_finsetSum Finset.univ
    intro psi hpsi
    exact (continuous_primitiveHybridTaylorPolynomial
      R x s c d q psi).norm.pow 2

theorem intervalIntegral_primitiveHybridMass_eq
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, primitiveHybridMass Q x s c d t) =
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            (∫ t in (0 : ℝ)..T,
              ‖primitiveHybridPolynomial x s c d q psi t‖ ^ 2) := by
  classical
  unfold primitiveHybridMass
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum]
    intro psi hpsi
    exact ((continuous_primitiveHybridPolynomial
      x s c d q psi).norm.pow 2).intervalIntegrable 0 T
  · intro q hq
    apply Continuous.intervalIntegrable
    apply continuous_const.mul
    apply continuous_finsetSum Finset.univ
    intro psi hpsi
    exact (continuous_primitiveHybridPolynomial
      x s c d q psi).norm.pow 2

/-- Uniform Taylor convergence survives the finite primitive-character and
modulus averages. -/
theorem tendsto_intervalIntegral_primitiveHybridTaylorMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    Tendsto (fun R ↦ ∫ t in (0 : ℝ)..T,
        primitiveHybridTaylorMass R Q x s c d t) atTop
      (𝓝 (∫ t in (0 : ℝ)..T,
        primitiveHybridMass Q x s c d t)) := by
  classical
  simp_rw [intervalIntegral_primitiveHybridTaylorMass_eq,
    intervalIntegral_primitiveHybridMass_eq]
  apply tendsto_finset_sum
  intro q hq
  apply tendsto_const_nhds.mul
  apply tendsto_finsetSum
  intro psi hpsi
  exact tendsto_intervalIntegral_primitiveHybridTaylorPolynomial_norm_sq
    x s c d q psi hT hB hd

/-- The pointwise Taylor Cauchy bound after summing over primitive
characters and conductors. -/
theorem primitiveHybridTaylorMass_le_blockFrequencyMass
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    primitiveHybridTaylorMass R Q x s c d t ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        ∑ k ∈ Finset.range R,
          t ^ (2 * k) / (k.factorial : ℝ) *
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
  classical
  let A : ℝ := ∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹
  let G : ℕ → (q : ℕ) → primitiveCharacters q → ℝ := fun k q psi ↦
    ‖realFrequencyPolynomial x
      (fun i ↦ ∑ n ∈ s i,
        (c n * (d n : ℂ) ^ k) * psi.1 n) t‖ ^ 2
  let wq : ℕ → ℝ := fun q ↦ (q : ℝ) / (q.totient : ℝ)
  let wk : ℕ → ℝ := fun k ↦ t ^ (2 * k) / (k.factorial : ℝ)
  have hpoint (q : ℕ) (psi : primitiveCharacters q) :
      ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2 ≤
        A * ∑ k ∈ Finset.range R, wk k * G k q psi := by
    simpa only [A, wk, G, mul_assoc] using
      norm_primitiveHybridTaylorPolynomial_sq_le
        R x s c d q psi t ht
  calc
    primitiveHybridTaylorMass R Q x s c d t ≤
        ∑ q ∈ Finset.Ioc 0 Q, wq q *
          ∑ psi : primitiveCharacters q,
            (A * ∑ k ∈ Finset.range R, wk k * G k q psi) := by
      unfold primitiveHybridTaylorMass
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun psi hpsi ↦ hpoint q psi
      · positivity
    _ = A * ∑ k ∈ Finset.range R, wk k *
          primitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k) t := by
      let H : (q : ℕ) → primitiveCharacters q → ℕ → ℝ :=
        fun q psi k ↦ wq q * (wk k * G k q psi)
      have hswap :
          (∑ q ∈ Finset.Ioc 0 Q,
              ∑ psi : primitiveCharacters q,
                ∑ k ∈ Finset.range R, H q psi k) =
            ∑ k ∈ Finset.range R,
              ∑ q ∈ Finset.Ioc 0 Q,
                ∑ psi : primitiveCharacters q, H q psi k := by
        calc
          (∑ q ∈ Finset.Ioc 0 Q,
              ∑ psi : primitiveCharacters q,
                ∑ k ∈ Finset.range R, H q psi k) =
              ∑ q ∈ Finset.Ioc 0 Q,
                ∑ k ∈ Finset.range R,
                  ∑ psi : primitiveCharacters q, H q psi k := by
            apply Finset.sum_congr rfl
            intro q hq
            exact Finset.sum_comm
          _ = _ := Finset.sum_comm
      calc
        (∑ q ∈ Finset.Ioc 0 Q, wq q *
            ∑ psi : primitiveCharacters q,
              (A * ∑ k ∈ Finset.range R, wk k * G k q psi)) =
            A * ∑ q ∈ Finset.Ioc 0 Q,
              ∑ psi : primitiveCharacters q,
                ∑ k ∈ Finset.range R, H q psi k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro psi hpsi
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [H]
          ring
        _ = A * ∑ k ∈ Finset.range R,
              ∑ q ∈ Finset.Ioc 0 Q,
                ∑ psi : primitiveCharacters q, H q psi k := by rw [hswap]
        _ = A * ∑ k ∈ Finset.range R, wk k *
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          unfold primitiveBlockFrequencyMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro psi hpsi
          dsimp [H, G]
          ring
    _ = _ := rfl

/-- On `[0,T]`, replace every Taylor power of `t` by the corresponding
power of the endpoint. -/
theorem primitiveHybridTaylorMass_le_blockFrequencyMass_endpoint
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    primitiveHybridTaylorMass R Q x s c d t ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        ∑ k ∈ Finset.range R,
          T ^ (2 * k) / (k.factorial : ℝ) *
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
  refine (primitiveHybridTaylorMass_le_blockFrequencyMass
    R Q x s c d t ht).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_right
    · apply div_le_div_of_nonneg_right
      · exact pow_le_pow_left₀ ht htT (2 * k)
      · positivity
    · unfold primitiveBlockFrequencyMass
      positivity
  · positivity

/-- Raising a uniformly bounded within-block offset to Taylor order `k`
costs at most `B^(2k)` in coefficient energy. -/
theorem sum_norm_mul_offset_pow_sq_le
    {ι : Type*} [Fintype ι]
    (s : ι → Finset ℕ) (c : ℕ → ℂ) (d : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) (k : ℕ) :
    (∑ i, ∑ n ∈ s i,
        ‖c n * (d n : ℂ) ^ k‖ ^ 2) ≤
      B ^ (2 * k) * ∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  calc
    (∑ i, ∑ n ∈ s i,
        ‖c n * (d n : ℂ) ^ k‖ ^ 2) ≤
        ∑ i, ∑ n ∈ s i,
          B ^ (2 * k) * ‖c n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have hpow : |d n| ^ (2 * k) ≤ B ^ (2 * k) :=
        pow_le_pow_left₀ (abs_nonneg _) (hd i n hn) (2 * k)
      calc
        (‖c n‖ * |d n| ^ k) ^ 2 =
            ‖c n‖ ^ 2 * |d n| ^ (2 * k) := by
          rw [mul_pow, ← pow_mul]
          congr 2
          omega
        _ ≤ ‖c n‖ ^ 2 * B ^ (2 * k) :=
          mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
        _ = B ^ (2 * k) * ‖c n‖ ^ 2 := by ring
    _ = B ^ (2 * k) * ∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- The finite Taylor approximation satisfies the hybrid large-sieve bound.
The two finite exponential sums are left visible so that the next theorem can
pass to their exact exponential values. -/
theorem intervalIntegral_primitiveHybridTaylorMass_le
    {ι : Type*} [Fintype ι]
    (R Q H : ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    (∫ t in (0 : ℝ)..T,
        primitiveHybridTaylorMass R Q x s c d t) ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        (T + 2 * Real.pi * δ⁻¹) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
            (∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2) *
              ∑ k ∈ Finset.range R,
                (T * B) ^ (2 * k) / (k.factorial : ℝ) := by
  classical
  let A : ℝ := ∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  let D : ℝ := (H : ℝ) + (Q : ℝ) ^ 2
  let E : ℝ := ∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2
  let wk : ℕ → ℝ := fun k ↦ T ^ (2 * k) / (k.factorial : ℝ)
  let bk : ℕ → ℝ := fun k ↦ (T * B) ^ (2 * k) / (k.factorial : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hwk (k : ℕ) : 0 ≤ wk k := by dsimp [wk]; positivity
  have hblock (k : ℕ) :
      (∫ t in (0 : ℝ)..T,
          primitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k) t) ≤
        C * D * ∑ i, ∑ n ∈ s i,
          ‖c n * (d n : ℂ) ^ k‖ ^ 2 := by
    simpa only [primitiveBlockFrequencyMass, C, D] using
      intervalIntegral_weighted_primitive_blockPolynomial_le
        Q H s m0 hs (fun n ↦ c n * (d n : ℂ) ^ k)
          x hδ hT hsep
  have hmono :
      (∫ t in (0 : ℝ)..T,
          primitiveHybridTaylorMass R Q x s c d t) ≤
        ∫ t in (0 : ℝ)..T,
          A * ∑ k ∈ Finset.range R, wk k *
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
    apply intervalIntegral.integral_mono_on hT
    · exact (continuous_primitiveHybridTaylorMass
        R Q x s c d).intervalIntegrable 0 T
    · apply Continuous.intervalIntegrable
      apply continuous_const.mul
      apply continuous_finsetSum (Finset.range R)
      intro k hk
      exact continuous_const.mul
        (continuous_primitiveBlockFrequencyMass Q x s
          (fun n ↦ c n * (d n : ℂ) ^ k))
    · intro t ht
      exact primitiveHybridTaylorMass_le_blockFrequencyMass_endpoint
        R Q x s c d ht.1 ht.2
  calc
    (∫ t in (0 : ℝ)..T,
        primitiveHybridTaylorMass R Q x s c d t) ≤
        ∫ t in (0 : ℝ)..T,
          A * ∑ k ∈ Finset.range R, wk k *
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := hmono
    _ = A * ∑ k ∈ Finset.range R, wk k *
          (∫ t in (0 : ℝ)..T,
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum]
      · apply congrArg (fun z : ℝ ↦ A * z)
        apply Finset.sum_congr rfl
        intro k hk
        rw [intervalIntegral.integral_const_mul]
      · intro k hk
        exact (continuous_const.mul
          (continuous_primitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k))).intervalIntegrable 0 T
    _ ≤ A * ∑ k ∈ Finset.range R, wk k *
          (C * D * ∑ i, ∑ n ∈ s i,
            ‖c n * (d n : ℂ) ^ k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hblock k) (hwk k)
    _ ≤ A * ∑ k ∈ Finset.range R, wk k *
          (C * D * (B ^ (2 * k) * E)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (hwk k)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
      simpa only [E] using
        sum_norm_mul_offset_pow_sq_le s c d hB hd k
    _ = A * C * D * E *
          ∑ k ∈ Finset.range R, bk k := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [wk, bk]
      rw [mul_pow]
      ring
    _ = _ := rfl

theorem sum_range_inv_factorial_le_exp_one (R : ℕ) :
    (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) ≤ Real.exp 1 := by
  have hs := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  have hle := hs.summable.sum_le_tsum (Finset.range R)
    (fun k hk ↦ by positivity)
  calc
    (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) =
        ∑ k ∈ Finset.range R, (1 : ℝ) ^ k / k.factorial := by simp
    _ ≤ ∑' k : ℕ, (1 : ℝ) ^ k / k.factorial := hle
    _ = Real.exp 1 := by
      simpa only [Real.exp_eq_exp_ℝ] using hs.tsum_eq

theorem sum_range_mul_pow_two_mul_div_factorial_le_exp
    (R : ℕ) {T B : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) :
    (∑ k ∈ Finset.range R,
        (T * B) ^ (2 * k) / (k.factorial : ℝ)) ≤
      Real.exp ((T * B) ^ 2) := by
  let z : ℝ := (T * B) ^ 2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hs := NormedSpace.expSeries_div_hasSum_exp z
  have hle := hs.summable.sum_le_tsum (Finset.range R)
    (fun k hk ↦ by positivity)
  calc
    (∑ k ∈ Finset.range R,
        (T * B) ^ (2 * k) / (k.factorial : ℝ)) =
        ∑ k ∈ Finset.range R, z ^ k / k.factorial := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [z]
      rw [pow_mul]
    _ ≤ ∑' k : ℕ, z ^ k / k.factorial := hle
    _ = Real.exp z := by
      simpa only [Real.exp_eq_exp_ℝ] using hs.tsum_eq
    _ = _ := rfl

/-- Exact hybrid large-sieve estimate for the recovered block polynomial. -/
theorem intervalIntegral_primitiveHybridMass_le
    {ι : Type*} [Fintype ι]
    (Q H : ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    (∫ t in (0 : ℝ)..T,
        primitiveHybridMass Q x s c d t) ≤
      Real.exp 1 * Real.exp ((T * B) ^ 2) *
        (T + 2 * Real.pi * δ⁻¹) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
            ∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  let D : ℝ := (H : ℝ) + (Q : ℝ) ^ 2
  let E : ℝ := ∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlim := tendsto_intervalIntegral_primitiveHybridTaylorMass
    Q x s c d hT hB hd
  apply le_of_tendsto' hlim
  intro R
  refine (intervalIntegral_primitiveHybridTaylorMass_le
    R Q H s m0 hs x hδ hT hsep c d hB hd).trans ?_
  calc
    (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
          C * D * E *
            ∑ k ∈ Finset.range R,
              (T * B) ^ (2 * k) / (k.factorial : ℝ) ≤
        Real.exp 1 * C * D * E *
          ∑ k ∈ Finset.range R,
            (T * B) ^ (2 * k) / (k.factorial : ℝ) := by
      gcongr
      exact sum_range_inv_factorial_le_exp_one R
    _ ≤ Real.exp 1 * C * D * E * Real.exp ((T * B) ^ 2) := by
      gcongr
      exact sum_range_mul_pow_two_mul_div_factorial_le_exp R hT hB
    _ = Real.exp 1 * Real.exp ((T * B) ^ 2) * C * D * E := by ring
    _ = _ := rfl

/-- Hybrid large sieve for an ordinary Dirichlet polynomial on pairwise
disjoint short blocks.  This is the form consumed by a zero detector: the
Taylor offsets have disappeared completely from the statement. -/
theorem intervalIntegral_primitiveDirichletBlockMass_le
    {ι : Type*} [Fintype ι]
    (Q H : ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (hB : 0 ≤ B)
    (hoffset : ∀ i, ∀ n ∈ s i, |Real.log n - x i| ≤ B) :
    (∫ t in (0 : ℝ)..T,
        primitiveDirichletBlockMass Q s c t) ≤
      Real.exp 1 * Real.exp ((T * B) ^ 2) *
        (T + 2 * Real.pi * δ⁻¹) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
            ∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  let d := blockLogOffset x s
  have hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B := by
    intro i n hn
    rw [show d n = Real.log n - x i by
      exact blockLogOffset_eq x s hdisj i hn]
    exact hoffset i n hn
  have hmain := intervalIntegral_primitiveHybridMass_le
    Q H s m0 hs x hδ hT hsep c d hB hd
  rw [show primitiveHybridMass Q x s c d =
      primitiveDirichletBlockMass Q s c by
    funext t
    exact primitiveHybridMass_blockLogOffset_eq Q x s c hdisj t] at hmain
  exact hmain

end Erdos48
