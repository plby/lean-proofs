import ErdosProblems.Erdos67b.MRMeanSquareProof

/-!
# Finite duality for sparse-frequency energy estimates

The duality principle is proved by a concrete choice of dual coefficients,
finite complex Cauchy--Schwarz, and cancellation of a positive energy.
Arithmetic bounds for the corresponding Gram kernel remain to be supplied.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

theorem mrNorm_sum_mul_sq_le
    {ι : Type*} (A : Finset ι) (a b : ι → ℂ) :
    ‖∑ n ∈ A, a n * b n‖ ^ 2 ≤ (∑ n ∈ A, ‖a n‖ ^ 2) * ∑ n ∈ A, ‖b n‖ ^ 2 := by
  calc
    _ ≤ (∑ n ∈ A, ‖a n‖ * ‖b n‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using norm_sum_le A (fun n ↦ a n * b n)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq A (fun n ↦ ‖a n‖) (fun n ↦ ‖b n‖)

/-- The finite dual estimate implies its transpose, with exactly the
same constant. There is no conjugation assumption on the matrix. -/
theorem mrFinite_duality
    {ι κ : Type*} (A : Finset ι) (S : Finset κ) (x : κ → ι → ℂ)
    {D : ℝ} (hD : 0 ≤ D)
    (hdual : ∀ b : κ → ℂ, (∑ n ∈ A, ‖∑ s ∈ S, b s * x s n‖ ^ 2) ≤
      D * ∑ s ∈ S, ‖b s‖ ^ 2) (a : ι → ℂ) :
    (∑ s ∈ S, ‖∑ n ∈ A, a n * x s n‖ ^ 2) ≤ D * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  let F : κ → ℂ := fun s ↦ ∑ n ∈ A, a n * x s n
  let E : ℝ := ∑ s ∈ S, ‖F s‖ ^ 2
  let b : κ → ℂ := fun s ↦ conj (F s)
  let B : ι → ℂ := fun n ↦ ∑ s ∈ S, b s * x s n
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmass : 0 ≤ ∑ n ∈ A, ‖a n‖ ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hident : (E : ℂ) = ∑ n ∈ A, a n * B n := by
    calc
      (E : ℂ) = ∑ s ∈ S, conj (F s) * F s := by
        dsimp only [E]
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [← Complex.normSq_eq_norm_sq]
        exact Complex.normSq_eq_conj_mul_self
      _ = ∑ s ∈ S, ∑ n ∈ A, a n * (b s * x s n) := by
        apply Finset.sum_congr rfl
        intro s hs
        dsimp only [F, b]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp only [B]
        rw [Finset.mul_sum]
  have hnorm : ‖∑ n ∈ A, a n * B n‖ = E := by
    rw [← hident, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
  have hcs := mrNorm_sum_mul_sq_le A a B
  rw [hnorm] at hcs
  have hB : (∑ n ∈ A, ‖B n‖ ^ 2) ≤ D * E := by
    simpa only [B, b, Complex.norm_conj, E] using hdual b
  have hsquare : E ^ 2 ≤ (D * ∑ n ∈ A, ‖a n‖ ^ 2) * E := by
    calc
      _ ≤ (∑ n ∈ A, ‖a n‖ ^ 2) * ∑ n ∈ A, ‖B n‖ ^ 2 := hcs
      _ ≤ (∑ n ∈ A, ‖a n‖ ^ 2) * (D * E) := mul_le_mul_of_nonneg_left hB hmass
      _ = _ := by ring
  change E ≤ D * ∑ n ∈ A, ‖a n‖ ^ 2
  rcases eq_or_lt_of_le hE with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hD hmass
  · apply (mul_le_mul_iff_left₀ hpos).mp
    simpa only [pow_two] using hsquare

/-- Finite matrix energy and its transpose have the same upper bounds. -/
theorem mrFinite_duality_iff
    {ι κ : Type*} (A : Finset ι) (S : Finset κ) (x : κ → ι → ℂ)
    {D : ℝ} (hD : 0 ≤ D) :
    (∀ a : ι → ℂ, (∑ s ∈ S, ‖∑ n ∈ A, a n * x s n‖ ^ 2) ≤
      D * ∑ n ∈ A, ‖a n‖ ^ 2) ↔
    (∀ b : κ → ℂ, (∑ n ∈ A, ‖∑ s ∈ S, b s * x s n‖ ^ 2) ≤
      D * ∑ s ∈ S, ‖b s‖ ^ 2) := by
  constructor
  · intro hh b
    exact mrFinite_duality S A (fun n s ↦ x s n) hD hh b
  · intro hh a
    exact mrFinite_duality A S x hD hh a

/-- The finite symmetric Schur estimate, with no spectral theorem. -/
theorem mrFinite_symmetricKernel_sum_le
    {κ : Type*} (S : Finset κ) (K : κ → κ → ℝ) (b : κ → ℝ) {D : ℝ}
    (hK : ∀ s ∈ S, ∀ t ∈ S, 0 ≤ K s t)
    (hsymm : ∀ s ∈ S, ∀ t ∈ S, K s t = K t s)
    (hrow : ∀ s ∈ S, (∑ t ∈ S, K s t) ≤ D) :
    (∑ s ∈ S, ∑ t ∈ S, b s * b t * K s t) ≤ D * ∑ s ∈ S, b s ^ 2 := by
  have hswap : (∑ s ∈ S, ∑ t ∈ S, b t ^ 2 * K s t) =
      ∑ s ∈ S, ∑ t ∈ S, b s ^ 2 * K s t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    rw [hsymm t ht s hs]
  calc
    _ ≤ ∑ s ∈ S, ∑ t ∈ S, ((b s ^ 2 + b t ^ 2) / 2) * K s t := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (b s - b t)]) (hK s hs t ht)
    _ = ((∑ s ∈ S, ∑ t ∈ S, b s ^ 2 * K s t) +
        (∑ s ∈ S, ∑ t ∈ S, b t ^ 2 * K s t)) / 2 := by
      simp only [add_mul, div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul]
      ring
    _ = ∑ s ∈ S, ∑ t ∈ S, b s ^ 2 * K s t := by rw [hswap]; ring
    _ ≤ ∑ s ∈ S, b s ^ 2 * D := by
      apply Finset.sum_le_sum
      intro s hs
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hrow s hs) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

noncomputable section

/-- The finite Gram kernel of the rows of a complex matrix. -/
def mrFiniteGramKernel {ι κ : Type*} (A : Finset ι) (x : κ → ι → ℂ) (s t : κ) : ℂ :=
  ∑ n ∈ A, conj (x s n) * x t n

theorem mrFiniteGramKernel_conj
    {ι κ : Type*} (A : Finset ι) (x : κ → ι → ℂ) (s t : κ) :
    conj (mrFiniteGramKernel A x s t) = mrFiniteGramKernel A x t s := by
  unfold mrFiniteGramKernel
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [map_mul, starRingEnd_self_apply]
  ring

theorem mrFiniteGramKernel_norm_symm
    {ι κ : Type*} (A : Finset ι) (x : κ → ι → ℂ) (s t : κ) :
    ‖mrFiniteGramKernel A x s t‖ = ‖mrFiniteGramKernel A x t s‖ := by
  rw [← mrFiniteGramKernel_conj A x s t, Complex.norm_conj]

/-- Opening the finite dual square exposes the Gram kernel exactly. -/
theorem mrFinite_dual_energy_eq_gram
    {ι κ : Type*} (A : Finset ι) (S : Finset κ) (x : κ → ι → ℂ) (b : κ → ℂ) :
    (∑ n ∈ A, ‖∑ s ∈ S, b s * x s n‖ ^ 2) =
      ∑ s ∈ S, ∑ t ∈ S, (conj (b s) * b t * mrFiniteGramKernel A x s t).re := by
  simp only [← Complex.normSq_eq_norm_sq, normSq_finset_sum_eq_sum_correlation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [mrFiniteGramKernel, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [map_mul]
  ring

/-- Kernel row estimates imply the dual energy bound. -/
theorem mrFinite_dual_energy_le_of_gram_rows
    {ι κ : Type*} (A : Finset ι) (S : Finset κ) (x : κ → ι → ℂ) {D : ℝ}
    (hrow : ∀ s ∈ S, (∑ t ∈ S, ‖mrFiniteGramKernel A x s t‖) ≤ D)
    (b : κ → ℂ) :
    (∑ n ∈ A, ‖∑ s ∈ S, b s * x s n‖ ^ 2) ≤ D * ∑ s ∈ S, ‖b s‖ ^ 2 := by
  calc
    _ = ∑ s ∈ S, ∑ t ∈ S, (conj (b s) * b t * mrFiniteGramKernel A x s t).re :=
      mrFinite_dual_energy_eq_gram A S x b
    _ ≤ ∑ s ∈ S, ∑ t ∈ S, ‖b s‖ * ‖b t‖ * ‖mrFiniteGramKernel A x s t‖ := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro t ht
      simpa only [norm_mul, Complex.norm_conj] using
        Complex.re_le_norm (conj (b s) * b t * mrFiniteGramKernel A x s t)
    _ ≤ _ := mrFinite_symmetricKernel_sum_le S (fun s t ↦ ‖mrFiniteGramKernel A x s t‖)
      (fun s ↦ ‖b s‖) (fun _ _ _ _ ↦ norm_nonneg _)
      (fun s _ t _ ↦ mrFiniteGramKernel_norm_symm A x s t) hrow

/-- The finite sparse-energy reduction: a proved Gram row bound is
transferred to arbitrary coefficient vectors with the same constant. -/
theorem mrFinite_energy_le_of_gram_rows
    {ι κ : Type*} (A : Finset ι) (S : Finset κ) (x : κ → ι → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ s ∈ S, (∑ t ∈ S, ‖mrFiniteGramKernel A x s t‖) ≤ D)
    (a : ι → ℂ) :
    (∑ s ∈ S, ‖∑ n ∈ A, a n * x s n‖ ^ 2) ≤ D * ∑ n ∈ A, ‖a n‖ ^ 2 :=
  mrFinite_duality A S x hD (mrFinite_dual_energy_le_of_gram_rows A S x hrow) a

theorem conj_logarithmicPhase_mul_same_index (n : ℕ) (s t : ℝ) :
    conj (logarithmicPhase n s) * logarithmicPhase n t = logarithmicPhase n (t - s) := by
  change conj (realExponentialPhase (s * Real.log n)) * realExponentialPhase (t * Real.log n) =
    realExponentialPhase ((t - s) * Real.log n)
  rw [conj_realExponentialPhase, realExponentialPhase_mul]
  congr 1
  ring

/-- The unweighted Gram kernel is the integer exponential sum at the
sample-frequency difference, with the phase sign fixed explicitly. -/
theorem mrLogarithmic_gram_eq
    (A : Finset ℕ) (s t : ℝ) :
    mrFiniteGramKernel A (fun u n ↦ logarithmicPhase n u) s t =
      logarithmicDirichletPolynomial A (fun _ ↦ 1) (t - s) := by
  unfold mrFiniteGramKernel logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [one_mul, conj_logarithmicPhase_mul_same_index]

theorem mrSparse_logarithmic_energy_le_of_kernel_rows
    (A : Finset ℕ) (S : Finset ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ s ∈ S,
      (∑ t ∈ S, ‖logarithmicDirichletPolynomial A (fun _ ↦ 1) (t - s)‖) ≤ D)
    (a : ℕ → ℂ) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤ D * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  apply mrFinite_energy_le_of_gram_rows A S (fun t n ↦ logarithmicPhase n t) hD
  intro s hs
  simpa only [mrLogarithmic_gram_eq] using hrow s hs

theorem mrWeighted_logarithmic_gram_eq
    (A : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ n ∈ A, 0 ≤ w n) (s t : ℝ) :
    mrFiniteGramKernel A (fun u n ↦ (Real.sqrt (w n) : ℂ) * logarithmicPhase n u) s t =
      logarithmicDirichletPolynomial A (fun n ↦ (w n : ℂ)) (t - s) := by
  unfold mrFiniteGramKernel logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = (Real.sqrt (w n) : ℂ) ^ 2 * (conj (logarithmicPhase n s) * logarithmicPhase n t) := by
      rw [map_mul, Complex.conj_ofReal]
      ring
    _ = _ := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (hw n hn), conj_logarithmicPhase_mul_same_index]

/-- Positive-weight normalization of the sparse logarithmic criterion.
Zero weights are explicitly excluded on the finite coefficient support. -/
theorem mrWeighted_sparse_logarithmic_energy_le_of_kernel_rows
    (A : Finset ℕ) (S : Finset ℝ) (w : ℕ → ℝ) (hw : ∀ n ∈ A, 0 < w n)
    {D : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ s ∈ S,
      (∑ t ∈ S, ‖logarithmicDirichletPolynomial A (fun n ↦ (w n : ℂ)) (t - s)‖) ≤ D)
    (a : ℕ → ℂ) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤
      D * ∑ n ∈ A, ‖a n‖ ^ 2 / w n := by
  let b : ℕ → ℂ := fun n ↦ a n / (Real.sqrt (w n) : ℂ)
  let x : ℝ → ℕ → ℂ := fun t n ↦ (Real.sqrt (w n) : ℂ) * logarithmicPhase n t
  have hsqrt (n : ℕ) (hn : n ∈ A) : 0 < Real.sqrt (w n) := Real.sqrt_pos.mpr (hw n hn)
  have hpoly (t : ℝ) : (∑ n ∈ A, b n * x t n) = logarithmicDirichletPolynomial A a t := by
    apply Finset.sum_congr rfl
    intro n hn
    have hne : (Real.sqrt (w n) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hsqrt n hn).ne'
    dsimp only [b, x]
    field_simp
  have hmass : (∑ n ∈ A, ‖b n‖ ^ 2) = ∑ n ∈ A, ‖a n‖ ^ 2 / w n := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      div_pow, Real.sq_sqrt (hw n hn).le]
  have hrows : ∀ s ∈ S, (∑ t ∈ S, ‖mrFiniteGramKernel A x s t‖) ≤ D := by
    intro s hs
    dsimp only [x]
    simpa only [mrWeighted_logarithmic_gram_eq A w (fun n hn ↦ (hw n hn).le)] using hrow s hs
  have hh := mrFinite_energy_le_of_gram_rows A S x hD hrows b
  simpa only [hpoly, hmass] using hh

end

end Erdos67b
