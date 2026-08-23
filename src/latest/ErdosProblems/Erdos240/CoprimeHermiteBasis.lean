/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma4Concrete
import ErdosProblems.Erdos240.BakerCoprimeInterpolation
import Mathlib.Analysis.Complex.Liouville

/-!
# A factorial-cancelled Hermite basis for a finite subset of integer nodes

This is the arbitrary-node version needed on p. 52.  It deliberately keeps
the Lagrange denominator as the exact product of integer spacings.  A Cauchy
circle of radius `1/2` loses only a power of two; the source-specific
arithmetic lemma for the coprime subset then bounds the target/denominator
ratio by an exponential in the radius, with no `R log R` loss.
-/

open scoped BigOperators

open Complex Finset Function Metric Polynomial Set

noncomputable section

namespace Erdos240.CoprimeHermiteBasis

open BakerLemma4Concrete

/-- The product over a finite set of positive integer nodes `i+1`. -/
def finiteNodePolynomial (s : Finset ℕ) : ℂ[X] :=
  ∏ i ∈ s, (X - C (((i + 1 : ℕ) : ℂ)))

/-- The product with the node indexed by `r` omitted. -/
def finiteCofactorPolynomial (s : Finset ℕ) (r : ℕ) : ℂ[X] :=
  ∏ i ∈ s.erase r, (X - C (((i + 1 : ℕ) : ℂ)))

/-- Inverse cofactor power in a half-disc around the omitted node. -/
def finiteInverseCofactorPower (s : Finset ℕ) (T r : ℕ) (z : ℂ) : ℂ :=
  ((finiteCofactorPolynomial s r).eval z)⁻¹ ^ T

/-- Normalized Taylor coefficient of the inverse cofactor power. -/
def finiteInverseCofactorJet (s : Finset ℕ) (T r j : ℕ) : ℂ :=
  iteratedDeriv j (finiteInverseCofactorPower s T r) ((r + 1 : ℕ) : ℂ) /
    (j.factorial : ℂ)

/-- A single term of the explicit Hermite basis. -/
def finiteBasisTerm (s : Finset ℕ) (T r m j : ℕ) : ℂ[X] :=
  (X - C (((r + 1 : ℕ) : ℂ))) ^ m *
    (finiteCofactorPolynomial s r) ^ T *
    (C (finiteInverseCofactorJet s T r j) *
      (X - C (((r + 1 : ℕ) : ℂ))) ^ j)

/-- The complete explicit basis polynomial for the `m`th normalized jet. -/
def finiteBasisPolynomial (s : Finset ℕ) (T r m : ℕ) : ℂ[X] :=
  ∑ j ∈ range (T - m), finiteBasisTerm s T r m j

/-- The truncated inverse-cofactor Taylor series in the local coordinate. -/
def finiteInverseCofactorTaylor (s : Finset ℕ) (T r n : ℕ) : ℂ[X] :=
  ∑ j ∈ range n,
    C (finiteInverseCofactorJet s T r j) *
      (X - C (((r + 1 : ℕ) : ℂ))) ^ j

@[simp] theorem eval_finiteNodePolynomial (s : Finset ℕ) (z : ℂ) :
    (finiteNodePolynomial s).eval z =
      ∏ i ∈ s, (z - (((i + 1 : ℕ) : ℂ))) := by
  simp [finiteNodePolynomial, Polynomial.eval_prod]

@[simp] theorem eval_finiteCofactorPolynomial
    (s : Finset ℕ) (r : ℕ) (z : ℂ) :
    (finiteCofactorPolynomial s r).eval z =
      ∏ i ∈ s.erase r, (z - (((i + 1 : ℕ) : ℂ))) := by
  simp [finiteCofactorPolynomial, Polynomial.eval_prod]

/-- The full nodal product splits into the omitted factor and its cofactor. -/
theorem finiteNodePolynomial_eval_eq_mul_cofactor
    {s : Finset ℕ} {r : ℕ} (hr : r ∈ s) (z : ℂ) :
    (finiteNodePolynomial s).eval z =
      (z - (((r + 1 : ℕ) : ℂ))) *
        (finiteCofactorPolynomial s r).eval z := by
  simp only [eval_finiteNodePolynomial, eval_finiteCofactorPolynomial]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hr
    (fun i ↦ z - (((i + 1 : ℕ) : ℂ)))

/-- Distinct positive integer nodes are separated by at least one. -/
theorem one_le_norm_positiveNode_sub_of_ne {i r : ℕ} (hir : i ≠ r) :
    1 ≤ ‖(((i + 1 : ℕ) : ℂ)) - (((r + 1 : ℕ) : ℂ))‖ := by
  exact one_le_norm_integral_nodes_sub_of_ne (i := r) (j := i) hir

/-- Every noncentral integer spacing loses at most a factor two on the
half-unit circle about the central node. -/
theorem half_spacing_le_norm_sub_node
    {z : ℂ} {i r : ℕ} (hir : i ≠ r)
    (hz : ‖z - (((r + 1 : ℕ) : ℂ))‖ = 1 / 2) :
    ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖ / 2 ≤
      ‖z - (((i + 1 : ℕ) : ℂ))‖ := by
  let d : ℝ := ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖
  let y : ℝ := ‖z - (((i + 1 : ℕ) : ℂ))‖
  have hd : 1 ≤ d := by
    dsimp only [d]
    simpa only [norm_sub_rev] using
      one_le_norm_positiveNode_sub_of_ne hir
  have htri : d ≤ 1 / 2 + y := by
    dsimp only [d, y]
    calc
      ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖ =
          ‖((((r + 1 : ℕ) : ℂ)) - z) +
            (z - (((i + 1 : ℕ) : ℂ)))‖ := by
          congr 1
          ring
      _ ≤ ‖(((r + 1 : ℕ) : ℂ)) - z‖ +
          ‖z - (((i + 1 : ℕ) : ℂ))‖ := norm_add_le _ _
      _ = 1 / 2 + ‖z - (((i + 1 : ℕ) : ℂ))‖ := by
        rw [norm_sub_rev, hz]
  dsimp only [d, y] at hd htri ⊢
  linarith

/-- Exact product of the integer spacings from the omitted node. -/
def finiteSpacingProduct (s : Finset ℕ) (r : ℕ) : ℝ :=
  ∏ i ∈ s.erase r,
    ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖

theorem finiteSpacingProduct_pos {s : Finset ℕ} {r : ℕ} :
    0 < finiteSpacingProduct s r := by
  unfold finiteSpacingProduct
  apply Finset.prod_pos
  intro i hi
  have hir : i ≠ r := (Finset.mem_erase.mp hi).1
  exact lt_of_lt_of_le zero_lt_one
    (one_le_norm_positiveNode_sub_of_ne (i := r) (r := i) hir.symm)

/-- The half-circle cofactor lower bound, retaining the exact spacing
product for later arithmetic cancellation. -/
theorem finiteCofactorPolynomial_norm_lower_on_half_circle
    {s : Finset ℕ} {r : ℕ} {z : ℂ}
    (hz : ‖z - (((r + 1 : ℕ) : ℂ))‖ = 1 / 2) :
    (1 / 2 : ℝ) ^ (s.erase r).card * finiteSpacingProduct s r ≤
      ‖(finiteCofactorPolynomial s r).eval z‖ := by
  rw [eval_finiteCofactorPolynomial, norm_prod]
  unfold finiteSpacingProduct
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    have hir : i ≠ r := (Finset.mem_erase.mp hi).1
    simpa [div_eq_mul_inv, mul_comm] using
      half_spacing_le_norm_sub_node hir hz

theorem finiteCofactorPolynomial_eval_ne_zero_of_mem_closedBall
    {s : Finset ℕ} {r : ℕ} {z : ℂ}
    (hz : z ∈ closedBall ((((r + 1 : ℕ) : ℂ))) (1 / 2 : ℝ)) :
    (finiteCofactorPolynomial s r).eval z ≠ 0 := by
  rw [eval_finiteCofactorPolynomial]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hir : i ≠ r := (Finset.mem_erase.mp hi).1
  have hsep := one_le_norm_positiveNode_sub_of_ne hir
  have hzhalf : ‖z - (((r + 1 : ℕ) : ℂ))‖ ≤ 1 / 2 := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  intro hzero
  have hzi : z = (((i + 1 : ℕ) : ℂ)) := sub_eq_zero.mp hzero
  subst z
  linarith

theorem finiteInverseCofactorPower_diffContOnCl_halfBall
    {s : Finset ℕ} {T r : ℕ} :
    DiffContOnCl ℂ (finiteInverseCofactorPower s T r)
      (ball ((((r + 1 : ℕ) : ℂ))) (1 / 2 : ℝ)) := by
  have hpoly : DiffContOnCl ℂ
      (fun z : ℂ ↦ (finiteCofactorPolynomial s r).eval z)
      (ball ((((r + 1 : ℕ) : ℂ))) (1 / 2 : ℝ)) :=
    (Polynomial.differentiable _).diffContOnCl
  have hinv := hpoly.inv (fun z hz ↦
    finiteCofactorPolynomial_eval_ne_zero_of_mem_closedBall (by
      exact closure_ball_subset_closedBall hz))
  induction T with
  | zero =>
      change DiffContOnCl ℂ (fun _ : ℂ ↦ (1 : ℂ)) _
      exact diffContOnCl_const
  | succ T ih =>
      change DiffContOnCl ℂ
        (fun z ↦ ((finiteCofactorPolynomial s r).eval z)⁻¹ ^ (T + 1)) _
      change DiffContOnCl ℂ
        (fun z ↦ ((finiteCofactorPolynomial s r).eval z)⁻¹ ^ T) _ at ih
      exact ⟨ih.1.mul hinv.1, ih.2.mul hinv.2⟩

/-- Cauchy's coefficient bound with the exact finite-set spacing product. -/
theorem norm_finiteInverseCofactorJet_le
    {s : Finset ℕ} {T r j : ℕ} :
    ‖finiteInverseCofactorJet s T r j‖ ≤
      (2 : ℝ) ^ ((s.erase r).card * T + j) /
        (finiteSpacingProduct s r) ^ T := by
  let D : ℝ := finiteSpacingProduct s r
  have hD : 0 < D := finiteSpacingProduct_pos
  have hC : ∀ z ∈ sphere ((((r + 1 : ℕ) : ℂ))) (1 / 2 : ℝ),
      ‖finiteInverseCofactorPower s T r z‖ ≤
        (2 : ℝ) ^ ((s.erase r).card * T) / D ^ T := by
    intro z hzSphere
    have hz : ‖z - (((r + 1 : ℕ) : ℂ))‖ = 1 / 2 := by
      simpa [mem_sphere, dist_eq_norm] using hzSphere
    have hlower : (1 / 2 : ℝ) ^ (s.erase r).card * D ≤
        ‖(finiteCofactorPolynomial s r).eval z‖ := by
      exact finiteCofactorPolynomial_norm_lower_on_half_circle hz
    have hbase : 0 < (1 / 2 : ℝ) ^ (s.erase r).card * D := by positivity
    have hnormpos : 0 < ‖(finiteCofactorPolynomial s r).eval z‖ :=
      hbase.trans_le hlower
    rw [finiteInverseCofactorPower, norm_pow, norm_inv]
    change ‖(finiteCofactorPolynomial s r).eval z‖⁻¹ ^ T ≤ _
    rw [show (2 : ℝ) ^ ((s.erase r).card * T) / D ^ T =
        ((2 : ℝ) ^ (s.erase r).card / D) ^ T by rw [div_pow, pow_mul]]
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_le_iff_one_le_mul₀' hnormpos]
    calc
      1 = ((1 / 2 : ℝ) ^ (s.erase r).card * D) *
          ((2 : ℝ) ^ (s.erase r).card / D) := by
        field_simp [hD.ne']
        rw [← mul_pow]
        norm_num
      _ ≤ ‖(finiteCofactorPolynomial s r).eval z‖ *
          ((2 : ℝ) ^ (s.erase r).card / D) := by gcongr
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j (by norm_num : (0 : ℝ) < 1 / 2)
    (finiteInverseCofactorPower_diffContOnCl_halfBall (s := s) (T := T) (r := r)) hC
  rw [finiteInverseCofactorJet, norm_div, Complex.norm_natCast]
  have hjfac : (0 : ℝ) < j.factorial := by positivity
  rw [div_le_iff₀ hjfac]
  calc
    ‖iteratedDeriv j (finiteInverseCofactorPower s T r)
        (((r + 1 : ℕ) : ℂ))‖ ≤
        (j.factorial : ℝ) *
          ((2 : ℝ) ^ ((s.erase r).card * T) / D ^ T) /
            (1 / 2 : ℝ) ^ j := hcauchy
    _ = (j.factorial : ℝ) *
        ((2 : ℝ) ^ ((s.erase r).card * T + j) / D ^ T) := by
      have hinvhalf : ((1 / 2 : ℝ) ^ j)⁻¹ = 2 ^ j := by
        rw [← inv_pow]
        norm_num
      rw [div_eq_mul_inv, hinvhalf, pow_add]
      ring
    _ = (2 : ℝ) ^ ((s.erase r).card * T + j) / D ^ T *
        (j.factorial : ℝ) := by ring

/-- Abstract factorial-cancellation consumer.  If the full target nodal
product is at most `K` times the exact local spacing product, each explicit
basis term costs only `K^T` and a power of two from the half-circle. -/
theorem norm_finiteBasisTerm_eval_le
    {s : Finset ℕ} {T r m j l : ℕ} (hr : r ∈ s)
    (hlr : l ≠ r + 1) (hmj : m + j ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hratio : ‖(finiteNodePolynomial s).eval (l : ℂ)‖ ≤
      K * finiteSpacingProduct s r) :
    ‖(finiteBasisTerm s T r m j).eval (l : ℂ)‖ ≤
      K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) := by
  let D : ℝ := finiteSpacingProduct s r
  let d : ℝ := ‖(l : ℂ) - (((r + 1 : ℕ) : ℂ))‖
  let A : ℝ := ‖(finiteCofactorPolynomial s r).eval (l : ℂ)‖
  have hD : 0 < D := finiteSpacingProduct_pos
  have hd : 1 ≤ d := by
    dsimp only [d]
    have hne : l ≠ r + 1 := hlr
    have hcastne : (l : ℂ) ≠ (((r + 1 : ℕ) : ℂ)) := by exact_mod_cast hne
    rw [show (l : ℂ) - (((r + 1 : ℕ) : ℂ)) =
      (((l : ℤ) - (r + 1 : ℤ) : ℤ) : ℂ) by push_cast; ring]
    rw [Complex.norm_intCast]
    have hintne : (l : ℤ) - (r + 1 : ℤ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hne)
    exact_mod_cast Int.one_le_abs hintne
  have hfull : ‖(finiteNodePolynomial s).eval (l : ℂ)‖ = d * A := by
    rw [finiteNodePolynomial_eval_eq_mul_cofactor hr, norm_mul]
  have hAd : A ^ T * d ^ (m + j) ≤ (K * D) ^ T := by
    calc
      A ^ T * d ^ (m + j) ≤ A ^ T * d ^ T := by gcongr
      _ = (d * A) ^ T := by rw [mul_pow]; ring
      _ ≤ (K * D) ^ T := by
        apply pow_le_pow_left₀ (by positivity)
        rw [← hfull]
        exact hratio
  have hjet := norm_finiteInverseCofactorJet_le (s := s) (T := T)
    (r := r) (j := j)
  simp only [finiteBasisTerm, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
    norm_mul, norm_pow]
  change d ^ m * A ^ T * (‖finiteInverseCofactorJet s T r j‖ * d ^ j) ≤ _
  calc
    d ^ m * A ^ T * (‖finiteInverseCofactorJet s T r j‖ * d ^ j) =
        (A ^ T * d ^ (m + j)) * ‖finiteInverseCofactorJet s T r j‖ := by
      rw [pow_add]
      ring
    _ ≤ (K * D) ^ T *
        ((2 : ℝ) ^ ((s.erase r).card * T + j) / D ^ T) := by
      exact mul_le_mul hAd hjet (norm_nonneg _)
        (pow_nonneg (mul_nonneg hK hD.le) T)
    _ = K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) := by
      rw [mul_pow]
      have hDp : D ^ T ≠ 0 := pow_ne_zero _ hD.ne'
      field_simp

/-- The termwise factorial-cancellation estimate summed over the truncated
Taylor polynomial. -/
theorem norm_finiteBasisPolynomial_eval_le_sum
    {s : Finset ℕ} {T r m l : ℕ} (hr : r ∈ s)
    (hlr : l ≠ r + 1) (hm : m ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hratio : ‖(finiteNodePolynomial s).eval (l : ℂ)‖ ≤
      K * finiteSpacingProduct s r) :
    ‖(finiteBasisPolynomial s T r m).eval (l : ℂ)‖ ≤
      ∑ j ∈ range (T - m),
        K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) := by
  rw [finiteBasisPolynomial]
  simp_rw [Polynomial.eval_finsetSum]
  calc
    ‖∑ j ∈ range (T - m), (finiteBasisTerm s T r m j).eval (l : ℂ)‖ ≤
        ∑ j ∈ range (T - m),
          ‖(finiteBasisTerm s T r m j).eval (l : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ range (T - m),
        K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      exact norm_finiteBasisTerm_eval_le hr hlr (by omega) hK hratio

/-! ### Exact finite-set jet reconstruction -/

/-- Normalized iterated derivatives turn products into a convolution. -/
theorem normalized_iteratedDeriv_mul
    {f g : ℂ → ℂ} {x : ℂ} {n : ℕ}
    (hf : ContDiffAt ℂ n f x) (hg : ContDiffAt ℂ n g x) :
    iteratedDeriv n (fun z ↦ f z * g z) x / (n.factorial : ℂ) =
      ∑ i ∈ range (n + 1),
        (iteratedDeriv i f x / (i.factorial : ℂ)) *
          (iteratedDeriv (n - i) g x / ((n - i).factorial : ℂ)) := by
  change iteratedDeriv n (f * g) x / (n.factorial : ℂ) = _
  rw [iteratedDeriv_mul hf hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using hi
  have hfac : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) *
      ((n - i).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hi0 : (i.factorial : ℂ) ≠ 0 := by
    exact_mod_cast i.factorial_ne_zero
  have hni0 : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (n - i).factorial_ne_zero
  have hn0 : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  field_simp
  rw [← hfac]
  ring

/-- Multiplication by a power of the local parameter shifts Hasse jets. -/
theorem hasseDeriv_centerPow_mul_eval
    (B : ℂ[X]) (a : ℂ) (m k : ℕ) :
    (hasseDeriv k ((X - C a) ^ m * B)).eval a =
      if m ≤ k then (hasseDeriv (k - m) B).eval a else 0 := by
  rw [← taylor_coeff]
  rw [taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C]
  simp only [add_sub_cancel_right]
  rw [coeff_X_pow_mul']
  split_ifs
  · rw [taylor_coeff]
  · rfl

theorem finiteBasisPolynomial_eq_product (s : Finset ℕ) (T r m : ℕ) :
    finiteBasisPolynomial s T r m =
      (X - C (((r + 1 : ℕ) : ℂ))) ^ m *
        (finiteCofactorPolynomial s r) ^ T *
          finiteInverseCofactorTaylor s T r (T - m) := by
  simp only [finiteBasisPolynomial, finiteBasisTerm,
    finiteInverseCofactorTaylor, mul_sum]

/-- The cofactor power and its analytic inverse have unit Taylor
convolution at the omitted finite-set node. -/
theorem finiteCofactor_inverseJet_convolution
    {s : Finset ℕ} {T r n : ℕ} :
    ∑ i ∈ range (n + 1),
        (hasseDeriv i ((finiteCofactorPolynomial s r) ^ T)).eval
            (((r + 1 : ℕ) : ℂ)) *
          finiteInverseCofactorJet s T r (n - i) =
      if n = 0 then 1 else 0 := by
  let A : ℂ[X] := (finiteCofactorPolynomial s r) ^ T
  let a : ℂ := (((r + 1 : ℕ) : ℂ))
  have hA : ContDiffAt ℂ n (fun z : ℂ ↦ A.eval z) a :=
    (Polynomial.differentiable A).contDiff.contDiffAt
  have hcof : (finiteCofactorPolynomial s r).eval a ≠ 0 :=
    finiteCofactorPolynomial_eval_ne_zero_of_mem_closedBall (by
      simp [a, mem_closedBall])
  have hA0 : A.eval a ≠ 0 := by
    dsimp only [A]
    simp only [eval_pow]
    exact pow_ne_zero _ hcof
  have hB : ContDiffAt ℂ n (finiteInverseCofactorPower s T r) a := by
    have heq : finiteInverseCofactorPower s T r =
        fun z : ℂ ↦ (A.eval z)⁻¹ := by
      funext z
      simp [finiteInverseCofactorPower, A, inv_pow]
    rw [heq]
    exact hA.inv hA0
  have hprod : Filter.EventuallyEq (nhds a)
      (fun z : ℂ ↦ A.eval z * finiteInverseCofactorPower s T r z)
      (fun _ : ℂ ↦ 1) := by
    have hne := hA.continuousAt.eventually_ne hA0
    filter_upwards [hne] with z hz
    simp only [A, eval_pow, finiteInverseCofactorPower, inv_pow]
    apply mul_inv_cancel₀
    simpa [A] using hz
  simp only [finiteInverseCofactorJet]
  simp_rw [BakerLemma4Concrete.hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
  change (∑ i ∈ range (n + 1),
    (iteratedDeriv i (fun z : ℂ ↦ A.eval z) a /
      (i.factorial : ℂ)) *
      (iteratedDeriv (n - i) (finiteInverseCofactorPower s T r) a /
        ((n - i).factorial : ℂ))) = _
  rw [← normalized_iteratedDeriv_mul hA hB]
  have hderiv := Filter.EventuallyEq.iteratedDeriv_eq n hprod
  rw [hderiv, iteratedDeriv_const]
  split_ifs with hn
  · simp [hn]
  · simp [hn]

theorem finiteInverseCofactorTaylor_hasse
    {s : Finset ℕ} {T r n k : ℕ} (hk : k < n) :
    (hasseDeriv k (finiteInverseCofactorTaylor s T r n)).eval
        (((r + 1 : ℕ) : ℂ)) =
      finiteInverseCofactorJet s T r k := by
  rw [finiteInverseCofactorTaylor, map_sum, eval_finsetSum]
  refine (Finset.sum_eq_single k (fun j hj hne ↦ ?_) ?_).trans ?_
  · rw [Finset.mem_range] at hj
    rw [mul_comm, hasseDeriv_centerPow_mul_eval]
    by_cases hjk : j ≤ k
    · have hpos : 0 < k - j := by omega
      rw [if_pos hjk, hasseDeriv_C _ _ hpos, eval_zero]
    · rw [if_neg hjk]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hk)).elim
  · rw [mul_comm, hasseDeriv_centerPow_mul_eval,
      if_pos le_rfl, Nat.sub_self, hasseDeriv_zero, LinearMap.id_apply, eval_C]

theorem finiteCofactor_mul_inverseCofactorTaylor_hasse
    {s : Finset ℕ} {T r n k : ℕ} (hk : k < n) :
    (hasseDeriv k
      ((finiteCofactorPolynomial s r) ^ T *
        finiteInverseCofactorTaylor s T r n)).eval
        (((r + 1 : ℕ) : ℂ)) = if k = 0 then 1 else 0 := by
  rw [hasseDeriv_mul, eval_finsetSum]
  simp only [eval_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    ∑ i ∈ range (k + 1),
        (hasseDeriv i ((finiteCofactorPolynomial s r) ^ T)).eval
            (((r + 1 : ℕ) : ℂ)) *
          (hasseDeriv (k - i)
            (finiteInverseCofactorTaylor s T r n)).eval
              (((r + 1 : ℕ) : ℂ)) =
      ∑ i ∈ range (k + 1),
        (hasseDeriv i ((finiteCofactorPolynomial s r) ^ T)).eval
            (((r + 1 : ℕ) : ℂ)) *
          finiteInverseCofactorJet s T r (k - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [finiteInverseCofactorTaylor_hasse]
        omega
    _ = if k = 0 then 1 else 0 :=
      finiteCofactor_inverseJet_convolution

/-- At its own finite-set node, a basis element has its prescribed single
unit Hasse jet. -/
theorem finiteBasisPolynomial_hasse_same
    {s : Finset ℕ} {T r m k : ℕ} (hm : m < T) (hk : k < T) :
    (hasseDeriv k (finiteBasisPolynomial s T r m)).eval
        (((r + 1 : ℕ) : ℂ)) = if k = m then 1 else 0 := by
  rw [finiteBasisPolynomial_eq_product, mul_assoc,
    hasseDeriv_centerPow_mul_eval]
  by_cases hmk : m ≤ k
  · rw [if_pos hmk,
      finiteCofactor_mul_inverseCofactorTaylor_hasse (by omega)]
    by_cases hkm : k = m
    · subst k
      simp
    · have hpos : 0 < k - m := by omega
      simp [hkm, hpos.ne']
  · rw [if_neg hmk]
    have hkm : k ≠ m := by omega
    simp [hkm]

theorem finiteCenterPow_dvd_cofactor_pow
    {s : Finset ℕ} {T r t : ℕ} (ht : t ∈ s) (htr : t ≠ r) :
    (X - C (((t + 1 : ℕ) : ℂ))) ^ T ∣
      (finiteCofactorPolynomial s r) ^ T := by
  apply pow_dvd_pow_of_dvd
  rw [finiteCofactorPolynomial]
  exact Finset.dvd_prod_of_mem
    (fun i ↦ X - C (((i + 1 : ℕ) : ℂ)))
    (Finset.mem_erase.mpr ⟨htr, ht⟩)

theorem hasseDeriv_eval_eq_zero_of_centerPow_dvd
    {P : ℂ[X]} {a : ℂ} {T k : ℕ}
    (hdiv : (X - C a) ^ T ∣ P) (hk : k < T) :
    (hasseDeriv k P).eval a = 0 := by
  rw [← taylor_coeff]
  apply X_pow_dvd_iff.mp (show X ^ T ∣ taylor a P by
    change X ^ T ∣ P.comp (X + C a)
    rw [← X_sub_C_pow_dvd_iff]
    exact hdiv) k hk

/-- At another node in the finite set, every Hasse jet below the common
multiplicity vanishes. -/
theorem finiteBasisPolynomial_hasse_other
    {s : Finset ℕ} {T r t m k : ℕ} (ht : t ∈ s) (htr : t ≠ r)
    (hk : k < T) :
    (hasseDeriv k (finiteBasisPolynomial s T r m)).eval
        (((t + 1 : ℕ) : ℂ)) = 0 := by
  apply hasseDeriv_eval_eq_zero_of_centerPow_dvd _ hk
  obtain ⟨Q, hQ⟩ := finiteCenterPow_dvd_cofactor_pow
    (T := T) (r := r) ht htr
  refine ⟨(X - C (((r + 1 : ℕ) : ℂ))) ^ m * Q *
    finiteInverseCofactorTaylor s T r (T - m), ?_⟩
  rw [finiteBasisPolynomial_eq_product, hQ]
  ring

/-- The explicit Hermite interpolant for arbitrary prescribed normalized
jets on a finite set of positive integer nodes. -/
def finiteHermitePolynomial (s : Finset ℕ) (T : ℕ)
    (c : ℕ → ℕ → ℂ) : ℂ[X] :=
  ∑ r ∈ s, ∑ m ∈ range T, c r m • finiteBasisPolynomial s T r m

/-- Repeated-node list associated to an arbitrary finite set of positive
integer indices. -/
def finiteRepeatedNodes (s : Finset ℕ) (T : ℕ) : List ℂ :=
  s.toList.flatMap fun i ↦ List.replicate T ((i + 1 : ℕ) : ℂ)

@[simp] theorem length_finiteRepeatedNodes (s : Finset ℕ) (T : ℕ) :
    (finiteRepeatedNodes s T).length = s.card * T := by
  simp [finiteRepeatedNodes]

/-- Exact reconstruction of every prescribed jet below the common
multiplicity. -/
theorem finiteHermitePolynomial_hasse
    {s : Finset ℕ} {T : ℕ} (c : ℕ → ℕ → ℂ)
    {t k : ℕ} (ht : t ∈ s) (hk : k < T) :
    (hasseDeriv k (finiteHermitePolynomial s T c)).eval
        (((t + 1 : ℕ) : ℂ)) = c t k := by
  rw [finiteHermitePolynomial, map_sum, eval_finsetSum]
  simp only [map_sum, map_smul, eval_finsetSum, eval_smul, smul_eq_mul]
  rw [Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single k]
    · rw [finiteBasisPolynomial_hasse_same hk hk, if_pos rfl, mul_one]
    · intro m hm hmk
      rw [finiteBasisPolynomial_hasse_same (Finset.mem_range.mp hm) hk,
        if_neg hmk.symm, mul_zero]
    · intro hknot
      exact (hknot (Finset.mem_range.mpr hk)).elim
  · intro r hr hrt
    apply Finset.sum_eq_zero
    intro m hm
    rw [finiteBasisPolynomial_hasse_other ht hrt.symm hk, mul_zero]
  · intro htnot
    exact (htnot ht).elim

theorem finiteCofactorPolynomial_monic (s : Finset ℕ) (r : ℕ) :
    (finiteCofactorPolynomial s r).Monic := by
  rw [finiteCofactorPolynomial]
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C _

theorem finiteCofactorPolynomial_natDegree (s : Finset ℕ) (r : ℕ) :
    (finiteCofactorPolynomial s r).natDegree = (s.erase r).card := by
  rw [finiteCofactorPolynomial, natDegree_prod_of_monic]
  · simp only [natDegree_X_sub_C, Finset.sum_const_nat, smul_eq_mul,
      mul_one]
  · intro i hi
    exact monic_X_sub_C _

theorem finiteInverseCofactorTaylor_natDegree_lt
    {s : Finset ℕ} {T r n : ℕ} (hn : 0 < n) :
    (finiteInverseCofactorTaylor s T r n).natDegree < n := by
  rw [finiteInverseCofactorTaylor]
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le
      (n := n - 1) (range n) (fun j ↦
        C (finiteInverseCofactorJet s T r j) *
          (X - C (((r + 1 : ℕ) : ℂ))) ^ j) ?_)
  · omega
  · intro j hj
    have hjn := Finset.mem_range.mp hj
    exact (natDegree_C_mul_le _ _).trans (by
      rw [natDegree_pow, natDegree_X_sub_C]
      simp only [mul_one]
      exact Nat.le_pred_of_lt hjn)

theorem finiteBasisPolynomial_natDegree_lt
    {s : Finset ℕ} {T r m : ℕ} (hr : r ∈ s) (hm : m < T) :
    (finiteBasisPolynomial s T r m).natDegree < s.card * T := by
  have hcof : ((finiteCofactorPolynomial s r) ^ T).natDegree =
      (s.card - 1) * T := by
    rw [natDegree_pow, finiteCofactorPolynomial_natDegree,
      Finset.card_erase_of_mem hr]
    exact Nat.mul_comm _ _
  have hinv :
      (finiteInverseCofactorTaylor s T r (T - m)).natDegree ≤ T - m - 1 :=
    Nat.le_pred_of_lt (finiteInverseCofactorTaylor_natDegree_lt (by omega))
  rw [finiteBasisPolynomial_eq_product]
  calc
    (((X - C (((r + 1 : ℕ) : ℂ))) ^ m *
        (finiteCofactorPolynomial s r) ^ T) *
          finiteInverseCofactorTaylor s T r (T - m)).natDegree ≤
      ((X - C (((r + 1 : ℕ) : ℂ))) ^ m).natDegree +
        ((finiteCofactorPolynomial s r) ^ T).natDegree +
          (finiteInverseCofactorTaylor s T r (T - m)).natDegree := by
      exact natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
    _ ≤ m + (s.card - 1) * T + (T - m - 1) := by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one, hcof]
      omega
    _ < s.card * T := by
      have hs : 1 ≤ s.card := Finset.card_pos.mpr ⟨r, hr⟩
      rw [show s.card * T = (s.card - 1) * T + T by
        have hs' : s.card = (s.card - 1) + 1 := by omega
        calc
          s.card * T = ((s.card - 1) + 1) * T :=
            congrArg (fun x : ℕ ↦ x * T) hs'
          _ = (s.card - 1) * T + T := by rw [add_mul, one_mul]]
      omega

theorem finiteHermitePolynomial_natDegree_lt
    {s : Finset ℕ} {T : ℕ} (hs : s.Nonempty) (hT : 0 < T)
    (c : ℕ → ℕ → ℂ) :
    (finiteHermitePolynomial s T c).natDegree < s.card * T := by
  rw [finiteHermitePolynomial]
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le (n := s.card * T - 1) s
      (fun r ↦ ∑ m ∈ range T, c r m • finiteBasisPolynomial s T r m) ?_)
  · have hcard : 0 < s.card := Finset.card_pos.mpr hs
    have hprod : 0 < s.card * T := Nat.mul_pos hcard hT
    omega
  · intro r hr
    apply Polynomial.natDegree_sum_le_of_forall_le (n := s.card * T - 1)
    intro m hm
    exact (natDegree_smul_le _ _).trans
      (Nat.le_pred_of_lt
        (finiteBasisPolynomial_natDegree_lt hr (Finset.mem_range.mp hm)))

/-- A polynomial below the total number of jet conditions is reconstructed
by the explicit finite-set basis. -/
theorem finiteHermite_reconstruction
    {s : Finset ℕ} {T : ℕ} (hs : s.Nonempty) (hT : 0 < T)
    {P : ℂ[X]} (hP : P.natDegree < s.card * T) :
    P = finiteHermitePolynomial s T (fun r m ↦
      (hasseDeriv m P).eval (((r + 1 : ℕ) : ℂ))) := by
  let Q : ℂ[X] := P - finiteHermitePolynomial s T (fun r m ↦
    (hasseDeriv m P).eval (((r + 1 : ℕ) : ℂ)))
  have hI := finiteHermitePolynomial_natDegree_lt hs hT (fun r m ↦
    (hasseDeriv m P).eval (((r + 1 : ℕ) : ℂ)))
  have hQdeg : Q.natDegree < s.card * T := by
    calc
      Q.natDegree ≤ max P.natDegree
          (finiteHermitePolynomial s T (fun r m ↦
            (hasseDeriv m P).eval (((r + 1 : ℕ) : ℂ)))).natDegree :=
        by dsimp only [Q]; exact natDegree_sub_le _ _
      _ < s.card * T := max_lt hP hI
  have hx : Function.Injective
      (fun r : {r // r ∈ s} ↦ (((r.1 + 1 : ℕ) : ℂ))) := by
    intro r t hrt
    apply Subtype.ext
    have hre := congrArg Complex.re hrt
    norm_num at hre
    exact_mod_cast hre
  have hsum : (∑ _r : {r // r ∈ s}, T) = s.card * T := by simp
  have hQzero : Q = 0 := by
    apply Multiplicity.eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
      (fun r : {r // r ∈ s} ↦ (((r.1 + 1 : ℕ) : ℂ)))
      (fun _ ↦ T) Q hx
    · simpa only [hsum] using hQdeg
    · intro r k hk
      dsimp only [Q]
      rw [map_sub, eval_sub,
        finiteHermitePolynomial_hasse _ r.2 hk, sub_self]
  exact sub_eq_zero.mp hQzero

/-- The Newton--Hermite polynomial on the repeated finite-set list matches
the original entire function through order `T-1` at every node. -/
theorem iteratedDeriv_eval_polynomial_finiteRepeatedNodes
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {s : Finset ℕ} {T t k : ℕ}
    (ht : t ∈ s) (hk : k < T) :
    iteratedDeriv k (fun z ↦
      (HermiteInterpolation.polynomial f (finiteRepeatedNodes s T)).eval z)
        (((t + 1 : ℕ) : ℂ)) =
      iteratedDeriv k f (((t + 1 : ℕ) : ℂ)) := by
  obtain ⟨before, after, hlist⟩ := List.append_of_mem
    (show t ∈ s.toList by simpa using ht)
  have hder := HermiteInterpolation.iteratedDeriv_eval_polynomial_eq_of_replicate_block
    hf
    (before.flatMap fun i ↦ List.replicate T ((i + 1 : ℕ) : ℂ))
    (after.flatMap fun i ↦ List.replicate T ((i + 1 : ℕ) : ℂ))
    (((t + 1 : ℕ) : ℂ)) T k hk
  simpa only [finiteRepeatedNodes, hlist, List.flatMap_append,
    List.flatMap_cons, List.append_assoc] using hder

/-- The explicit finite-set formula is exactly the Newton--Hermite
polynomial used by the analytic remainder theorem. -/
theorem polynomial_finiteRepeatedNodes_eq_finiteHermite
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Finset ℕ} {T : ℕ} (hs : s.Nonempty) (hT : 0 < T) :
    HermiteInterpolation.polynomial f (finiteRepeatedNodes s T) =
      finiteHermitePolynomial s T (fun r m ↦
        iteratedDeriv m f (((r + 1 : ℕ) : ℂ)) / (m.factorial : ℂ)) := by
  let P := HermiteInterpolation.polynomial f (finiteRepeatedNodes s T)
  have hPdeg : P.natDegree < s.card * T := by
    rcases HermiteInterpolation.polynomial_eq_zero_or_natDegree_lt
        f (finiteRepeatedNodes s T) with hzero | hdeg
    · dsimp only [P]
      rw [hzero]
      have hcard : 0 < s.card := Finset.card_pos.mpr hs
      have hprod : 0 < s.card * T := Nat.mul_pos hcard hT
      simpa using hprod
    · simpa only [length_finiteRepeatedNodes] using hdeg
  calc
    P = finiteHermitePolynomial s T (fun r m ↦
        (hasseDeriv m P).eval (((r + 1 : ℕ) : ℂ))) :=
      finiteHermite_reconstruction hs hT hPdeg
    _ = finiteHermitePolynomial s T (fun r m ↦
        iteratedDeriv m f (((r + 1 : ℕ) : ℂ)) / (m.factorial : ℂ)) := by
      rw [finiteHermitePolynomial, finiteHermitePolynomial]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro m hm
      congr 1
      rw [BakerLemma4Concrete.hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
      exact congrArg (fun z : ℂ ↦ z / (m.factorial : ℂ))
        (iteratedDeriv_eval_polynomial_finiteRepeatedNodes hf hr
          (Finset.mem_range.mp hm))

/-- Fully explicit evaluation bound for the reconstructed finite-set
Hermite polynomial.  No inverse Vandermonde constant is hidden: all losses
are displayed in the three finite sums and the exact spacing ratio. -/
theorem norm_finiteHermitePolynomial_eval_le_sum
    {s : Finset ℕ} {T l : ℕ} (c : ℕ → ℕ → ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hl : ∀ r ∈ s, l ≠ r + 1)
    (hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval (l : ℂ)‖ ≤
        K * finiteSpacingProduct s r) :
    ‖(finiteHermitePolynomial s T c).eval (l : ℂ)‖ ≤
      ∑ r ∈ s, ∑ m ∈ range T,
        ‖c r m‖ *
          (∑ j ∈ range (T - m),
            K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
  rw [finiteHermitePolynomial, Polynomial.eval_finsetSum]
  calc
    ‖∑ r ∈ s,
        (∑ m ∈ range T, c r m • finiteBasisPolynomial s T r m).eval
          (l : ℂ)‖ ≤
      ∑ r ∈ s,
        ‖(∑ m ∈ range T, c r m • finiteBasisPolynomial s T r m).eval
          (l : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ s, ∑ m ∈ range T,
        ‖c r m‖ *
          (∑ j ∈ range (T - m),
            K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [Polynomial.eval_finsetSum]
      calc
        ‖∑ m ∈ range T,
            (c r m • finiteBasisPolynomial s T r m).eval (l : ℂ)‖ ≤
          ∑ m ∈ range T,
            ‖(c r m • finiteBasisPolynomial s T r m).eval (l : ℂ)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ m ∈ range T,
            ‖c r m‖ *
              (∑ j ∈ range (T - m),
                K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [eval_smul, norm_smul]
          exact mul_le_mul_of_nonneg_left
            (norm_finiteBasisPolynomial_eval_le_sum hr (hl r hr)
              (Nat.le_of_lt (Finset.mem_range.mp hm)) hK (hratio r hr))
            (norm_nonneg _)

/-- The preceding explicit estimate for the actual Newton--Hermite
polynomial of an entire function. -/
theorem norm_polynomial_finiteRepeatedNodes_eval_le_sum
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Finset ℕ} {T l : ℕ} (hs : s.Nonempty) (hT : 0 < T)
    {K : ℝ} (hK : 0 ≤ K)
    (hl : ∀ r ∈ s, l ≠ r + 1)
    (hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval (l : ℂ)‖ ≤
        K * finiteSpacingProduct s r) :
    ‖(HermiteInterpolation.polynomial f (finiteRepeatedNodes s T)).eval
        (l : ℂ)‖ ≤
      ∑ r ∈ s, ∑ m ∈ range T,
        ‖iteratedDeriv m f (((r + 1 : ℕ) : ℂ)) / (m.factorial : ℂ)‖ *
          (∑ j ∈ range (T - m),
            K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
  rw [polynomial_finiteRepeatedNodes_eq_finiteHermite hf hs hT]
  exact norm_finiteHermitePolynomial_eval_le_sum _ hK hl hratio

/-- A convenient uniform-jet form of the explicit evaluation bound.  The
three finite sums contribute exactly `s.card * T * T`; all dependence on
the integer geometry remains in the displayed product-ratio factor. -/
theorem norm_polynomial_finiteRepeatedNodes_eval_le_uniform
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Finset ℕ} {T l : ℕ} (hs : s.Nonempty) (hT : 0 < T)
    {K delta : ℝ} (hK : 0 ≤ K) (hdelta : 0 ≤ delta)
    (hl : ∀ r ∈ s, l ≠ r + 1)
    (hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval (l : ℂ)‖ ≤
        K * finiteSpacingProduct s r)
    (hjet : ∀ r ∈ s, ∀ m < T,
      ‖iteratedDeriv m f (((r + 1 : ℕ) : ℂ)) / (m.factorial : ℂ)‖ ≤
        delta) :
    ‖(HermiteInterpolation.polynomial f (finiteRepeatedNodes s T)).eval
        (l : ℂ)‖ ≤
      delta * ((s.card : ℝ) * T * T *
        (K ^ T * (2 : ℝ) ^ (s.card * T + T))) := by
  have hbase0 : 0 ≤ K ^ T * (2 : ℝ) ^ (s.card * T + T) := by
    positivity
  have hsum := norm_polynomial_finiteRepeatedNodes_eval_le_sum
    hf hs hT hK hl hratio
  refine hsum.trans ?_
  calc
    ∑ r ∈ s, ∑ m ∈ range T,
        ‖iteratedDeriv m f (((r + 1 : ℕ) : ℂ)) / (m.factorial : ℂ)‖ *
          (∑ j ∈ range (T - m),
            K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) ≤
      ∑ _r ∈ s, ∑ _m ∈ range T,
        delta * (T * (K ^ T * (2 : ℝ) ^ (s.card * T + T))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul (hjet r hr m (Finset.mem_range.mp hm))
      · calc
          ∑ j ∈ range (T - m),
              K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) ≤
            ∑ _j ∈ range (T - m),
              K ^ T * (2 : ℝ) ^ (s.card * T + T) := by
                apply Finset.sum_le_sum
                intro j hj
                apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK T)
                apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
                have herase : (s.erase r).card ≤ s.card := card_erase_le
                have hjT : j ≤ T := by
                  have := Finset.mem_range.mp hj
                  omega
                exact Nat.add_le_add (Nat.mul_le_mul_right T herase) hjT
          _ = ((T - m : ℕ) : ℝ) *
              (K ^ T * (2 : ℝ) ^ (s.card * T + T)) := by simp
          _ ≤ (T : ℝ) *
              (K ^ T * (2 : ℝ) ^ (s.card * T + T)) := by
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast Nat.sub_le T m) hbase0
      · positivity
      · exact hdelta
    _ = delta * ((s.card : ℝ) * T * T *
        (K ^ T * (2 : ℝ) ^ (s.card * T + T))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

end Erdos240.CoprimeHermiteBasis

#print axioms Erdos240.CoprimeHermiteBasis.norm_finiteInverseCofactorJet_le
#print axioms Erdos240.CoprimeHermiteBasis.norm_finiteBasisTerm_eval_le
#print axioms Erdos240.CoprimeHermiteBasis.norm_finiteBasisPolynomial_eval_le_sum
#print axioms Erdos240.CoprimeHermiteBasis.finiteCofactor_inverseJet_convolution
#print axioms Erdos240.CoprimeHermiteBasis.finiteInverseCofactorTaylor_hasse
#print axioms Erdos240.CoprimeHermiteBasis.finiteBasisPolynomial_hasse_same
#print axioms Erdos240.CoprimeHermiteBasis.finiteBasisPolynomial_hasse_other
#print axioms Erdos240.CoprimeHermiteBasis.finiteHermitePolynomial_hasse
#print axioms Erdos240.CoprimeHermiteBasis.finiteHermitePolynomial_natDegree_lt
#print axioms Erdos240.CoprimeHermiteBasis.polynomial_finiteRepeatedNodes_eq_finiteHermite
#print axioms Erdos240.CoprimeHermiteBasis.norm_polynomial_finiteRepeatedNodes_eval_le_uniform
