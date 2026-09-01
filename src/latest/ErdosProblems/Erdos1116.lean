/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1116.
https://www.erdosproblems.com/forum/thread/1116

Informal authors:
- A. A. Gol'dberg
- Sakari Toppila

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1116.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Pairing
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Erdős Problem 1116

Toppila and Gol'dberg constructed an entire function whose counting functions
for every two distinct finite values have unbounded ratio.  The detailed
mathematical construction and the correspondence with the declarations below
are in `tex/1116.tex`.
-/

open Filter Function Metric Set
open ComplexConjugate
open scoped Topology

namespace Erdos1116

/-! ## The combinatorial and phase parameters -/

/-- `parameters n = (tₙ,Sₙ)`, where `Sₙ` is the total degree of the
preceding blocks.  The recurrence makes `tₙ/(Sₙ+1)` tend to infinity while
keeping all quantities natural-number valued. -/
private def parameters : ℕ → ℕ × ℕ
  | 0 => (4, 0)
  | n + 1 =>
      let p := parameters n
      let s' := p.2 + p.1 ^ 2
      ((n + 2) * (s' + 1) + 4, s')

private def t (n : ℕ) : ℕ := (parameters n).1

private def degree (n : ℕ) : ℕ := t n ^ 2

private def previousDegree (n : ℕ) : ℕ := (parameters n).2

@[simp] private lemma t_zero : t 0 = 4 := rfl

@[simp] private lemma previousDegree_zero : previousDegree 0 = 0 := rfl

@[simp] private lemma previousDegree_succ (n : ℕ) :
    previousDegree (n + 1) = previousDegree n + degree n := by
  simp [previousDegree, degree, t, parameters]

@[simp] private lemma t_succ (n : ℕ) :
    t (n + 1) = (n + 2) * (previousDegree (n + 1) + 1) + 4 := by
  simp [t, previousDegree, parameters]

private lemma four_le_t (n : ℕ) : 4 ≤ t n := by
  cases n with
  | zero => simp
  | succ n => simp [t_succ]

private lemma degree_pos (n : ℕ) : 0 < degree n := by
  apply pow_pos
  exact lt_of_lt_of_le (by omega) (four_le_t n)

private lemma degree_ne_zero (n : ℕ) : degree n ≠ 0 := (degree_pos n).ne'

private lemma previousDegree_eq_sum (n : ℕ) :
    previousDegree n = ∑ j ∈ Finset.range n, degree j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [previousDegree_succ, ih, Finset.sum_range_succ]

private lemma growth_bound (n : ℕ) :
    (n + 2) * (previousDegree (n + 1) + 1) < t (n + 1) := by
  rw [t_succ]
  omega

private lemma exists_large_growth (M C N : ℕ) :
    ∃ n, N < n ∧ M * (C + previousDegree n) < t n := by
  let q := max (N + 1) (M * (C + 1) + 1)
  refine ⟨q + 1, ?_, ?_⟩
  · have : N + 1 ≤ q := le_max_left _ _
    omega
  · have hMC : M * (C + 1) ≤ q := by
      exact (Nat.le_add_right _ 1).trans (le_max_right _ _)
    have hCS : C + previousDegree (q + 1) ≤
        (C + 1) * (previousDegree (q + 1) + 1) := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    calc
      M * (C + previousDegree (q + 1)) ≤
          M * ((C + 1) * (previousDegree (q + 1) + 1)) :=
        Nat.mul_le_mul_left M hCS
      _ = (M * (C + 1)) * (previousDegree (q + 1) + 1) := by ac_rfl
      _ ≤ q * (previousDegree (q + 1) + 1) :=
        Nat.mul_le_mul_right _ hMC
      _ < (q + 2) * (previousDegree (q + 1) + 1) := by
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ < t (q + 1) := growth_bound q

private lemma large_growth_of_stage (M C n : ℕ)
    (hn : M * (C + 1) + 1 < n) :
    M * (C + previousDegree n) < t n := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hMC : M * (C + 1) ≤ q := by omega
  have hCS : C + previousDegree (q + 1) ≤
      (C + 1) * (previousDegree (q + 1) + 1) := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  calc
    M * (C + previousDegree (q + 1)) ≤
        M * ((C + 1) * (previousDegree (q + 1) + 1)) :=
      Nat.mul_le_mul_left M hCS
    _ = (M * (C + 1)) * (previousDegree (q + 1) + 1) := by ac_rfl
    _ ≤ q * (previousDegree (q + 1) + 1) :=
      Nat.mul_le_mul_right _ hMC
    _ < (q + 2) * (previousDegree (q + 1) + 1) := by
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    _ < t (q + 1) := growth_bound q

/-- A dense sequence in the unit circle in which every entry of the original
dense sequence is repeated at arbitrarily large indices. -/
private noncomputable def recurrentPhase (n : ℕ) : Circle :=
  TopologicalSpace.denseSeq Circle (Nat.unpair n).1

private lemma recurrentPhase_recurrent (u : Circle) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n, N < n ∧ dist (recurrentPhase n) u < ε := by
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp
    (TopologicalSpace.denseRange_denseSeq Circle) u ε hε
  refine ⟨Nat.pair i (N + 1), ?_, ?_⟩
  · exact (Nat.lt_succ_self N).trans_le (Nat.right_le_pair i (N + 1))
  · simpa [recurrentPhase, dist_comm] using hi

private lemma previousDegree_succ_ne_zero (n : ℕ) : previousDegree (n + 1) ≠ 0 := by
  rw [previousDegree_succ]
  have ht := four_le_t n
  exact Nat.ne_of_gt (Nat.add_pos_right _ (pow_pos (by omega) _))

private lemma exists_complex_root (k : ℕ) (hk : k ≠ 0) (z : ℂ) :
    ∃ w : ℂ, w ^ k = z := by
  let _ : NeZero k := ⟨hk⟩
  exact (Complex.isOpenQuotientMap_pow k).surjective z

private noncomputable def complexRoot (k : ℕ) (hk : k ≠ 0) (z : ℂ) : ℂ :=
  Classical.choose (exists_complex_root k hk z)

private lemma complexRoot_pow (k : ℕ) (hk : k ≠ 0) (z : ℂ) :
    complexRoot k hk z ^ k = z :=
  Classical.choose_spec (exists_complex_root k hk z)

private noncomputable def circleRoot (k : ℕ) (hk : k ≠ 0) (z : Circle) : Circle := by
  refine ⟨complexRoot k hk z, ?_⟩
  apply mem_sphere_zero_iff_norm.mpr
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).mp
  rw [← norm_pow, complexRoot_pow]
  exact Circle.norm_coe z

private lemma circleRoot_pow (k : ℕ) (hk : k ≠ 0) (z : Circle) :
    circleRoot k hk z ^ k = z := by
  apply Circle.ext
  simp only [Circle.coe_pow]
  change complexRoot k hk z ^ k = (z : ℂ)
  exact complexRoot_pow k hk z

private noncomputable def aligningRoot (k : ℕ) (hk : k ≠ 0)
    (leading target : Circle) : Circle :=
  circleRoot k hk (leading⁻¹ * target)

private lemma aligningRoot_spec (k : ℕ) (hk : k ≠ 0)
    (leading target : Circle) :
    leading * aligningRoot k hk leading target ^ k = target := by
  rw [aligningRoot, circleRoot_pow]
  simp

private noncomputable def primitiveDirection (n : ℕ) : Circle :=
  Circle.exp (2 * Real.pi / degree n)

private lemma primitiveDirection_isPrimitive (n : ℕ) :
    IsPrimitiveRoot (primitiveDirection n : ℂ) (degree n) := by
  simpa [primitiveDirection, Circle.coe_exp, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    using Complex.isPrimitiveRoot_exp (degree n) (degree_ne_zero n)

private noncomputable def rootOfUnity (n : ℕ) (k : Fin (degree n)) : Circle :=
  primitiveDirection n ^ (k : ℕ)

@[simp] private lemma rootOfUnity_coe (n : ℕ) (k : Fin (degree n)) :
    (rootOfUnity n k : ℂ) = (primitiveDirection n : ℂ) ^ (k : ℕ) := rfl

private lemma prod_sub_rootOfUnity (n : ℕ) (w : ℂ) :
    ∏ k : Fin (degree n), (w - (rootOfUnity n k : ℂ)) = w ^ degree n - 1 := by
  have hpoly := X_pow_sub_C_eq_prod (primitiveDirection_isPrimitive n)
    (degree_pos n) (α := (1 : ℂ)) (a := (1 : ℂ)) (one_pow (degree n))
  have heval := congrArg (Polynomial.eval w) hpoly
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, mul_one] at heval
  calc
    ∏ k : Fin (degree n), (w - (rootOfUnity n k : ℂ)) =
        ∏ k ∈ Finset.range (degree n), (w - (primitiveDirection n : ℂ) ^ k) := by
      simpa only [rootOfUnity_coe] using
        (Finset.prod_range (fun k ↦ w - (primitiveDirection n : ℂ) ^ k)).symm
    _ = w ^ degree n - 1 := heval.symm

private lemma prod_neg_rootOfUnity (n : ℕ) :
    ∏ k : Fin (degree n), (-(rootOfUnity n k : ℂ)) = -1 := by
  simpa [zero_pow (degree_ne_zero n)] using prod_sub_rootOfUnity n 0

private lemma prod_inv_neg_rootOfUnity (n : ℕ) :
    ∏ k : Fin (degree n), (-(rootOfUnity n k : ℂ))⁻¹ = -1 := by
  calc
    ∏ k : Fin (degree n), (-(rootOfUnity n k : ℂ))⁻¹ =
        (∏ k : Fin (degree n), (-(rootOfUnity n k : ℂ)))⁻¹ :=
      Finset.prod_inv_distrib _
    _ = (-1 : ℂ)⁻¹ := congrArg Inv.inv (prod_neg_rootOfUnity n)
    _ = -1 := by simp

private lemma normalized_root_factor (n : ℕ) (k : Fin (degree n)) (w : ℂ) :
    1 - w / (rootOfUnity n k : ℂ) =
      (-(rootOfUnity n k : ℂ))⁻¹ * (w - (rootOfUnity n k : ℂ)) := by
  have hz : (rootOfUnity n k : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp
  ring

private lemma prod_normalized_rootOfUnity (n : ℕ) (w : ℂ) :
    ∏ k : Fin (degree n), (1 - w / (rootOfUnity n k : ℂ)) = 1 - w ^ degree n := by
  calc
    ∏ k : Fin (degree n), (1 - w / (rootOfUnity n k : ℂ)) =
        ∏ k : Fin (degree n),
          ((-(rootOfUnity n k : ℂ))⁻¹ * (w - (rootOfUnity n k : ℂ))) := by
      apply Finset.prod_congr rfl
      intro k _
      exact normalized_root_factor n k w
    _ = (∏ k : Fin (degree n), (-(rootOfUnity n k : ℂ))⁻¹) *
        ∏ k : Fin (degree n), (w - (rootOfUnity n k : ℂ)) := by
      exact Finset.prod_mul_distrib
    _ = 1 - w ^ degree n := by
      rw [prod_inv_neg_rootOfUnity, prod_sub_rootOfUnity]
      ring

private noncomputable def baseBlock (n : ℕ) (w : ℂ) : ℂ :=
  ∏ k : Fin (degree n), (1 - w / (rootOfUnity n k : ℂ))

@[simp] private lemma baseBlock_eq (n : ℕ) (w : ℂ) :
    baseBlock n w = 1 - w ^ degree n :=
  prod_normalized_rootOfUnity n w

private noncomputable def baseSlope (n : ℕ) (k : Fin (degree n)) : ℂ :=
  (rootOfUnity n k : ℂ)⁻¹ *
    ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase k,
      (1 - (rootOfUnity n k : ℂ) / (rootOfUnity n l : ℂ))

private lemma baseBlock_factor (n : ℕ) (k : Fin (degree n)) (w : ℂ) :
    baseBlock n w =
      (1 - w / (rootOfUnity n k : ℂ)) *
        ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase k,
          (1 - w / (rootOfUnity n l : ℂ)) := by
  exact (Finset.mul_prod_erase Finset.univ
    (fun l : Fin (degree n) ↦ 1 - w / (rootOfUnity n l : ℂ)) (Finset.mem_univ k)).symm

private lemma deriv_baseBlock_at_root (n : ℕ) (k : Fin (degree n)) :
    deriv (baseBlock n) (rootOfUnity n k : ℂ) = -baseSlope n k := by
  let z : ℂ := rootOfUnity n k
  let g : ℂ → ℂ := fun w ↦
    ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase k,
      (1 - w / (rootOfUnity n l : ℂ))
  have hf : HasDerivAt (fun w : ℂ ↦ 1 - w / z) (-z⁻¹) z := by
    simpa [one_div] using ((hasDerivAt_id z).div_const z).const_sub (1 : ℂ)
  have hg : DifferentiableAt ℂ g z := by
    dsimp only [g]
    fun_prop
  have hz : z ≠ 0 := Circle.coe_ne_zero _
  have hraw : HasDerivAt (fun w ↦ (1 - w / z) * g w)
      ((-z⁻¹) * g z + (1 - z / z) * deriv g z) z := by
    apply (hf.mul hg.hasDerivAt).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hprod : HasDerivAt (fun w ↦ (1 - w / z) * g w) (-baseSlope n k) z := by
    simpa [z, g, baseSlope, hz] using hraw
  have hfun : baseBlock n = fun w ↦ (1 - w / z) * g w := by
    funext w
    exact baseBlock_factor n k w
  rw [hfun]
  exact hprod.deriv

private lemma deriv_baseBlock (n : ℕ) (w : ℂ) :
    deriv (baseBlock n) w = -(degree n : ℂ) * w ^ (degree n - 1) := by
  have hfun : baseBlock n = fun z ↦ 1 - z ^ degree n := by
    funext z
    exact baseBlock_eq n z
  rw [hfun]
  convert (((hasDerivAt_id w).pow (degree n)).const_sub (1 : ℂ)).deriv using 1 <;> simp

private lemma rootOfUnity_pow_degree (n : ℕ) (k : Fin (degree n)) :
    (rootOfUnity n k : ℂ) ^ degree n = 1 := by
  rw [rootOfUnity_coe, ← pow_mul, mul_comm, pow_mul,
    (primitiveDirection_isPrimitive n).pow_eq_one, one_pow]

private lemma rootOfUnity_pow_degree_sub_one (n : ℕ) (k : Fin (degree n)) :
    (rootOfUnity n k : ℂ) ^ (degree n - 1) = (rootOfUnity n k : ℂ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [pow_sub_one_mul (degree_ne_zero n), rootOfUnity_pow_degree]

private lemma baseSlope_eq (n : ℕ) (k : Fin (degree n)) :
    baseSlope n k = (degree n : ℂ) * (rootOfUnity n k : ℂ)⁻¹ := by
  have h₁ := deriv_baseBlock_at_root n k
  rw [deriv_baseBlock, rootOfUnity_pow_degree_sub_one] at h₁
  have h₂ : -baseSlope n k =
      -((degree n : ℂ) * (rootOfUnity n k : ℂ)⁻¹) := by
    simpa only [neg_mul] using h₁.symm
  exact neg_injective h₂

/-! The remaining roots in a block are moved to the larger circle of radius
`δ`.  Only the first `t n` roots stay on the unit circle. -/

private def radialScale (n : ℕ) (δ : ℝ) (k : Fin (degree n)) : ℝ :=
  if (k : ℕ) < t n then 1 else δ

private noncomputable def perturbedRoot (n : ℕ) (δ : ℝ) (k : Fin (degree n)) : ℂ :=
  radialScale n δ k * (rootOfUnity n k : ℂ)

private noncomputable def perturbedBlock (n : ℕ) (δ : ℝ) (w : ℂ) : ℂ :=
  ∏ k : Fin (degree n), (1 - w / perturbedRoot n δ k)

private noncomputable def perturbedSlope (n : ℕ) (δ : ℝ) (k : Fin (degree n)) : ℂ :=
  (rootOfUnity n k : ℂ)⁻¹ *
    ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase k,
      (1 - (rootOfUnity n k : ℂ) / perturbedRoot n δ l)

@[simp] private lemma perturbedRoot_one (n : ℕ) (k : Fin (degree n)) :
    perturbedRoot n 1 k = (rootOfUnity n k : ℂ) := by
  simp [perturbedRoot, radialScale]

@[simp] private lemma perturbedBlock_one (n : ℕ) (w : ℂ) :
    perturbedBlock n 1 w = baseBlock n w := by
  simp [perturbedBlock, baseBlock]

@[simp] private lemma perturbedSlope_one (n : ℕ) (k : Fin (degree n)) :
    perturbedSlope n 1 k = baseSlope n k := by
  simp [perturbedSlope, baseSlope]

private lemma continuousAt_perturbedSlope (n : ℕ) (k : Fin (degree n)) :
    ContinuousAt (fun δ : ℝ ↦ perturbedSlope n δ k) 1 := by
  classical
  have hroot (l : Fin (degree n)) :
      ContinuousAt (fun δ : ℝ ↦ perturbedRoot n δ l) 1 := by
    by_cases hl : (l : ℕ) < t n
    · simpa [perturbedRoot, radialScale, hl] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (rootOfUnity n l : ℂ)) 1)
    · simp only [perturbedRoot, radialScale, hl, ↓reduceIte, rootOfUnity_coe]
      fun_prop
  have hfactor (l : Fin (degree n)) : ContinuousAt
      (fun δ : ℝ ↦ 1 - (rootOfUnity n k : ℂ) / perturbedRoot n δ l) 1 := by
    apply ContinuousAt.sub continuousAt_const
    exact ContinuousAt.div continuousAt_const (hroot l) (by simp)
  have hprod (s : Finset (Fin (degree n))) : ContinuousAt
      (fun δ : ℝ ↦ ∏ l ∈ s,
        (1 - (rootOfUnity n k : ℂ) / perturbedRoot n δ l)) 1 := by
    induction s using Finset.induction with
    | empty => exact continuousAt_const
    | @insert l s hls ih =>
        simp only [Finset.prod_insert hls]
        exact (hfactor l).mul ih
  exact continuousAt_const.mul (hprod ((Finset.univ : Finset (Fin (degree n))).erase k))

private lemma exists_delta (n : ℕ) : ∃ δ : ℝ,
    1 < δ ∧ δ < 2 ∧ ∀ k : Fin (degree n),
      ‖perturbedSlope n δ k - baseSlope n k‖ < (degree n : ℝ) / (n + 2) := by
  let ε : ℝ := (degree n : ℝ) / (n + 2)
  have hε : 0 < ε := by
    exact div_pos (mod_cast degree_pos n) (by positivity)
  have hk (k : Fin (degree n)) : ∀ᶠ δ : ℝ in 𝓝 1,
      ‖perturbedSlope n δ k - baseSlope n k‖ < ε := by
    have h := (continuousAt_perturbedSlope n k).eventually
      (Metric.ball_mem_nhds (perturbedSlope n 1 k) hε)
    filter_upwards [h] with δ hδ
    simpa [Metric.mem_ball, dist_eq_norm] using hδ
  have hall : ∀ᶠ δ : ℝ in 𝓝 1, ∀ k : Fin (degree n),
      ‖perturbedSlope n δ k - baseSlope n k‖ < ε := by
    simpa using (Finset.eventually_all (Finset.univ : Finset (Fin (degree n)))).2
      (fun k _ ↦ hk k)
  have hlt : ∀ᶠ δ : ℝ in 𝓝 1, δ < 2 := Iio_mem_nhds (by norm_num)
  have hwithin : ∀ᶠ δ : ℝ in 𝓝[Set.Ioi 1] 1,
      δ < 2 ∧ ∀ k : Fin (degree n),
        ‖perturbedSlope n δ k - baseSlope n k‖ < ε :=
    (hlt.and hall).filter_mono inf_le_left
  have hmem : ∀ᶠ δ : ℝ in 𝓝[Set.Ioi 1] 1, δ ∈ Set.Ioi 1 := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hδlt, hδslope⟩ := (hmem.and hwithin).exists
  exact ⟨δ, hδ, hδlt, hδslope⟩

private noncomputable def delta (n : ℕ) : ℝ := Classical.choose (exists_delta n)

private lemma one_lt_delta (n : ℕ) : 1 < delta n :=
  (Classical.choose_spec (exists_delta n)).1

private lemma delta_lt_two (n : ℕ) : delta n < 2 :=
  (Classical.choose_spec (exists_delta n)).2.1

private lemma perturbedSlope_delta_close (n : ℕ) (k : Fin (degree n)) :
    ‖perturbedSlope n (delta n) k - baseSlope n k‖ < (degree n : ℝ) / (n + 2) :=
  (Classical.choose_spec (exists_delta n)).2.2 k

private noncomputable def blockLeadingPhase (n : ℕ) (rotation : Circle) : Circle :=
  ∏ k : Fin (degree n), (-rotation * rootOfUnity n k)⁻¹

private structure PhaseData where
  leading : Circle
  rotation : Circle

/-- `phaseData n` records the phase of the leading coefficient of all earlier
blocks and a rotation for block `n`.  The rotation makes the radial linear
coefficient agree exactly with `recurrentPhase n` at the first root and
asymptotically at the whole short arc. -/
private noncomputable def phaseData : ℕ → PhaseData
  | 0 => ⟨1, 1⟩
  | n + 1 =>
      let leading := (phaseData n).leading *
        blockLeadingPhase n (phaseData n).rotation
      ⟨leading, aligningRoot (previousDegree (n + 1))
        (previousDegree_succ_ne_zero n) leading (recurrentPhase (n + 1))⟩

@[simp] private lemma phaseData_leading_succ (n : ℕ) :
    (phaseData (n + 1)).leading =
      (phaseData n).leading * blockLeadingPhase n (phaseData n).rotation := by
  simp [phaseData]

private lemma phase_alignment_succ (n : ℕ) :
    (phaseData (n + 1)).leading *
        (phaseData (n + 1)).rotation ^ previousDegree (n + 1) =
      recurrentPhase (n + 1) := by
  simp only [phaseData]
  exact aligningRoot_spec _ _ _ _

private def innerIndex (n : ℕ) (k : Fin (t n)) : Fin (degree n) :=
  ⟨k, k.isLt.trans_le (by
    rw [degree, pow_two]
    exact Nat.le_mul_of_pos_right (t n) (lt_of_lt_of_le (by omega) (four_le_t n)))⟩

@[simp] private lemma innerIndex_val (n : ℕ) (k : Fin (t n)) :
    (innerIndex n k : ℕ) = k := rfl

private noncomputable def modelRoot (n : ℕ) (k : Fin (degree n)) : ℂ :=
  (phaseData n).rotation * perturbedRoot n (delta n) k

private noncomputable def modelBlock (n : ℕ) (w : ℂ) : ℂ :=
  ∏ k : Fin (degree n), (1 - w / modelRoot n k)

private noncomputable def modelSlope (n : ℕ) (k : Fin (degree n)) : ℂ :=
  ((phaseData n).rotation : ℂ)⁻¹ * perturbedSlope n (delta n) k

private lemma radialScale_inner (n : ℕ) (k : Fin (t n)) :
    radialScale n (delta n) (innerIndex n k) = 1 := by
  simp [radialScale, k.isLt]

private lemma modelRoot_inner (n : ℕ) (k : Fin (t n)) :
    modelRoot n (innerIndex n k) =
      (phaseData n).rotation * (rootOfUnity n (innerIndex n k) : ℂ) := by
  simp [modelRoot, perturbedRoot, radialScale_inner]

private lemma radialScale_pos (n : ℕ) (k : Fin (degree n)) :
    0 < radialScale n (delta n) k := by
  simp only [radialScale]
  split_ifs
  · positivity
  · linarith [one_lt_delta n]

private lemma norm_perturbedRoot (n : ℕ) (k : Fin (degree n)) :
    ‖perturbedRoot n (delta n) k‖ = radialScale n (delta n) k := by
  have hs : ‖(radialScale n (delta n) k : ℂ)‖ = radialScale n (delta n) k := by
    calc
      ‖(radialScale n (delta n) k : ℂ)‖ = |radialScale n (delta n) k| :=
        RCLike.norm_ofReal _
      _ = radialScale n (delta n) k := abs_of_pos (radialScale_pos n k)
  have hζ : ‖(rootOfUnity n k : ℂ)‖ = 1 := Circle.norm_coe _
  rw [perturbedRoot, norm_mul, hs, hζ, mul_one]

private lemma norm_modelRoot (n : ℕ) (k : Fin (degree n)) :
    ‖modelRoot n k‖ = radialScale n (delta n) k := by
  rw [modelRoot, norm_mul, Circle.norm_coe, one_mul, norm_perturbedRoot]

private lemma modelRoot_ne_zero (n : ℕ) (k : Fin (degree n)) : modelRoot n k ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt (norm_modelRoot n k ▸ radialScale_pos n k))

private lemma rootOfUnity_injective (n : ℕ) : Injective (rootOfUnity n) := by
  intro k l h
  apply Fin.ext
  apply (primitiveDirection_isPrimitive n).pow_inj k.isLt l.isLt
  exact congrArg ((↑) : Circle → ℂ) h

private lemma modelRoot_injective (n : ℕ) : Injective (modelRoot n) := by
  intro k l h
  have hpert : perturbedRoot n (delta n) k = perturbedRoot n (delta n) l := by
    apply mul_left_cancel₀ (Circle.coe_ne_zero (phaseData n).rotation)
    exact h
  have hscale : radialScale n (delta n) k = radialScale n (delta n) l := by
    have hn := congrArg norm hpert
    simpa only [norm_perturbedRoot] using hn
  apply rootOfUnity_injective n
  apply Circle.ext
  have hscaled :
      (radialScale n (delta n) k : ℂ) * (rootOfUnity n k : ℂ) =
        (radialScale n (delta n) k : ℂ) * (rootOfUnity n l : ℂ) := by
    simpa only [perturbedRoot, hscale] using hpert
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (radialScale_pos n k).ne') hscaled

private lemma perturbedRoot_ne_zero (n : ℕ) (k : Fin (degree n)) :
    perturbedRoot n (delta n) k ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt (norm_perturbedRoot n k ▸ radialScale_pos n k))

private lemma modelRoot_ratio_inner (n : ℕ) (k : Fin (t n)) (l : Fin (degree n)) :
    modelRoot n (innerIndex n k) / modelRoot n l =
      (rootOfUnity n (innerIndex n k) : ℂ) / perturbedRoot n (delta n) l := by
  rw [modelRoot_inner, modelRoot]
  field_simp [Circle.coe_ne_zero (phaseData n).rotation, perturbedRoot_ne_zero n l]

private lemma modelBlock_factor (n : ℕ) (k : Fin (degree n)) (w : ℂ) :
    modelBlock n w =
      (1 - w / modelRoot n k) *
        ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase k,
          (1 - w / modelRoot n l) := by
  exact (Finset.mul_prod_erase Finset.univ
    (fun l : Fin (degree n) ↦ 1 - w / modelRoot n l) (Finset.mem_univ k)).symm

private lemma modelBlock_zero (n : ℕ) (k : Fin (degree n)) :
    modelBlock n (modelRoot n k) = 0 := by
  rw [modelBlock_factor n k, div_self (modelRoot_ne_zero n k)]
  simp

private lemma modelBlock_contDiff (n : ℕ) : ContDiff ℂ ⊤ (modelBlock n) := by
  unfold modelBlock
  fun_prop

private lemma continuous_deriv_modelBlock (n : ℕ) : Continuous (deriv (modelBlock n)) :=
  (modelBlock_contDiff n).continuous_deriv (by simp)

private lemma deriv_modelBlock_inner (n : ℕ) (k : Fin (t n)) :
    deriv (modelBlock n) (modelRoot n (innerIndex n k)) =
      -modelSlope n (innerIndex n k) := by
  let i := innerIndex n k
  let z := modelRoot n i
  let g : ℂ → ℂ := fun w ↦
    ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase i,
      (1 - w / modelRoot n l)
  have hz : z ≠ 0 := modelRoot_ne_zero n i
  have hf : HasDerivAt (fun w : ℂ ↦ 1 - w / z) (-z⁻¹) z := by
    simpa [one_div] using ((hasDerivAt_id z).div_const z).const_sub (1 : ℂ)
  have hg : DifferentiableAt ℂ g z := by
    dsimp only [g]
    fun_prop
  have hraw : HasDerivAt (fun w ↦ (1 - w / z) * g w)
      ((-z⁻¹) * g z + (1 - z / z) * deriv g z) z := by
    apply (hf.mul hg.hasDerivAt).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hslope : z⁻¹ * g z = modelSlope n i := by
    rw [modelSlope]
    change (modelRoot n i)⁻¹ *
        (∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase i,
          (1 - modelRoot n i / modelRoot n l)) = _
    have hprodEq :
        (∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase i,
          (1 - modelRoot n i / modelRoot n l)) =
        ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase i,
          (1 - (rootOfUnity n i : ℂ) / perturbedRoot n (delta n) l) := by
      apply Finset.prod_congr rfl
      intro l _
      rw [show modelRoot n i / modelRoot n l =
        (rootOfUnity n i : ℂ) / perturbedRoot n (delta n) l from
          modelRoot_ratio_inner n k l]
    rw [hprodEq, modelRoot_inner, mul_inv_rev, perturbedSlope]
    ring
  have hprod : HasDerivAt (fun w ↦ (1 - w / z) * g w) (-modelSlope n i) z := by
    simpa [hz, hslope] using hraw
  have hfun : modelBlock n = fun w ↦ (1 - w / z) * g w := by
    funext w
    exact modelBlock_factor n i w
  rw [hfun]
  exact hprod.deriv

private lemma exists_modelRadius (n : ℕ) : ∃ η : ℝ,
    0 < η ∧ η < 1 / 4 ∧ η < (delta n - 1) / 4 ∧
      ∀ k l : Fin (degree n), k ≠ l → 4 * η < dist (modelRoot n k) (modelRoot n l) := by
  have hp (k l : Fin (degree n)) (hkl : k ≠ l) :
      ∀ᶠ η : ℝ in 𝓝 0, 4 * η < dist (modelRoot n k) (modelRoot n l) := by
    have hroots : modelRoot n k ≠ modelRoot n l := fun h ↦ hkl (modelRoot_injective n h)
    have hd : 0 < dist (modelRoot n k) (modelRoot n l) :=
      dist_pos.mpr hroots
    have hc : ContinuousAt (fun η : ℝ ↦ 4 * η) 0 := continuousAt_const.mul continuousAt_id
    have hd' : (fun η : ℝ ↦ 4 * η) 0 < dist (modelRoot n k) (modelRoot n l) := by
      simpa using hd
    simpa using hc.eventually (Iio_mem_nhds hd')
  have hall : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ k l : Fin (degree n), k ≠ l →
        4 * η < dist (modelRoot n k) (modelRoot n l) := by
    have hpair (k l : Fin (degree n)) : ∀ᶠ η : ℝ in 𝓝 0,
        k ≠ l → 4 * η < dist (modelRoot n k) (modelRoot n l) := by
      by_cases hkl : k = l
      · exact Filter.Eventually.of_forall (fun _ h ↦ (h hkl).elim)
      · exact (hp k l hkl).mono (fun _ h _ ↦ h)
    have hk (k : Fin (degree n)) : ∀ᶠ η : ℝ in 𝓝 0,
        ∀ l : Fin (degree n), k ≠ l →
          4 * η < dist (modelRoot n k) (modelRoot n l) := by
      simpa only [Finset.mem_univ, true_implies] using
        (Finset.eventually_all (Finset.univ : Finset (Fin (degree n)))).2
          (fun l _ ↦ hpair k l)
    simpa only [Finset.mem_univ, true_implies] using
      (Finset.eventually_all (Finset.univ : Finset (Fin (degree n)))).2
        (fun k _ ↦ hk k)
  have hquarter : ∀ᶠ η : ℝ in 𝓝 0, η < 1 / 4 :=
    Iio_mem_nhds (by norm_num)
  have hgap : ∀ᶠ η : ℝ in 𝓝 0, η < (delta n - 1) / 4 :=
    Iio_mem_nhds (div_pos (sub_pos.mpr (one_lt_delta n)) (by norm_num))
  have hwithin : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0,
      η < 1 / 4 ∧ η < (delta n - 1) / 4 ∧
        ∀ k l : Fin (degree n), k ≠ l →
          4 * η < dist (modelRoot n k) (modelRoot n l) :=
    (hquarter.and (hgap.and hall)).filter_mono inf_le_left
  have hmem : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0, η ∈ Set.Ioi 0 := self_mem_nhdsWithin
  obtain ⟨η, hη, hηquarter, hηgap, hηsep⟩ := (hmem.and hwithin).exists
  exact ⟨η, hη, hηquarter, hηgap, hηsep⟩

private noncomputable def modelRadius (n : ℕ) : ℝ := Classical.choose (exists_modelRadius n)

private lemma modelRadius_pos (n : ℕ) : 0 < modelRadius n :=
  (Classical.choose_spec (exists_modelRadius n)).1

private lemma modelRadius_lt_quarter (n : ℕ) : modelRadius n < 1 / 4 :=
  (Classical.choose_spec (exists_modelRadius n)).2.1

private lemma modelRadius_lt_gap (n : ℕ) : modelRadius n < (delta n - 1) / 4 :=
  (Classical.choose_spec (exists_modelRadius n)).2.2.1

private lemma modelRoot_separated (n : ℕ) (k l : Fin (degree n)) (hkl : k ≠ l) :
    4 * modelRadius n < dist (modelRoot n k) (modelRoot n l) :=
  (Classical.choose_spec (exists_modelRadius n)).2.2.2 k l hkl

private lemma exists_localRadius (n : ℕ) : ∃ η : ℝ,
    0 < η ∧ η < modelRadius n ∧
      ∀ k : Fin (t n), ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
        ‖deriv (modelBlock n) w + modelSlope n (innerIndex n k)‖ <
          (degree n : ℝ) / (n + 2) := by
  let ε : ℝ := (degree n : ℝ) / (n + 2)
  have hε : 0 < ε := div_pos (mod_cast degree_pos n) (by positivity)
  have hk (k : Fin (t n)) : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
        ‖deriv (modelBlock n) w + modelSlope n (innerIndex n k)‖ < ε := by
    let U := {w : ℂ |
      ‖deriv (modelBlock n) w + modelSlope n (innerIndex n k)‖ < ε}
    have hUopen : IsOpen U := isOpen_lt
      ((continuous_deriv_modelBlock n).add continuous_const).norm continuous_const
    have hroot : modelRoot n (innerIndex n k) ∈ U := by
      simp only [U, Set.mem_ofPred_eq, deriv_modelBlock_inner, neg_add_cancel, norm_zero]
      exact hε
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hUopen _ hroot
    filter_upwards [Iio_mem_nhds hd] with η hη w hw
    apply hball
    exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hη)
  have hall : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ k : Fin (t n), ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
        ‖deriv (modelBlock n) w + modelSlope n (innerIndex n k)‖ < ε := by
    simpa only [Finset.mem_univ, true_implies] using
      (Finset.eventually_all (Finset.univ : Finset (Fin (t n)))).2 (fun k _ ↦ hk k)
  have hsmall : ∀ᶠ η : ℝ in 𝓝 0, η < modelRadius n :=
    Iio_mem_nhds (modelRadius_pos n)
  have hwithin : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0,
      η < modelRadius n ∧
        ∀ k : Fin (t n), ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
          ‖deriv (modelBlock n) w + modelSlope n (innerIndex n k)‖ < ε :=
    (hsmall.and hall).filter_mono inf_le_left
  have hmem : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0, η ∈ Set.Ioi 0 := self_mem_nhdsWithin
  obtain ⟨η, hη, hηsmall, hηderiv⟩ := (hmem.and hwithin).exists
  exact ⟨η, hη, hηsmall, hηderiv⟩

private noncomputable def localRadius (n : ℕ) : ℝ := Classical.choose (exists_localRadius n)

private lemma localRadius_pos (n : ℕ) : 0 < localRadius n :=
  (Classical.choose_spec (exists_localRadius n)).1

private lemma localRadius_lt_modelRadius (n : ℕ) : localRadius n < modelRadius n :=
  (Classical.choose_spec (exists_localRadius n)).2.1

private lemma modelBlock_deriv_close (n : ℕ) (k : Fin (t n))
    {w : ℂ} (hw : w ∈ closedBall (modelRoot n (innerIndex n k)) (localRadius n)) :
    ‖deriv (modelBlock n) w + modelSlope n (innerIndex n k)‖ <
      (degree n : ℝ) / (n + 2) :=
  (Classical.choose_spec (exists_localRadius n)).2.2 k w hw

private lemma norm_modelRoot_inner (n : ℕ) (k : Fin (t n)) :
    ‖modelRoot n (innerIndex n k)‖ = 1 := by
  rw [modelRoot_inner, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul]

private lemma modelSlope_inner_close (n : ℕ) (k : Fin (t n)) :
    ‖modelSlope n (innerIndex n k) -
        (degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹‖ <
      (degree n : ℝ) / (n + 2) := by
  have hclose := perturbedSlope_delta_close n (innerIndex n k)
  rw [baseSlope_eq] at hclose
  rw [modelSlope, modelRoot_inner, mul_inv_rev, ← mul_assoc]
  have hfactor :
      ((phaseData n).rotation : ℂ)⁻¹ * perturbedSlope n (delta n) (innerIndex n k) -
          (degree n : ℂ) * (rootOfUnity n (innerIndex n k) : ℂ)⁻¹ *
            ((phaseData n).rotation : ℂ)⁻¹ =
        ((phaseData n).rotation : ℂ)⁻¹ *
          (perturbedSlope n (delta n) (innerIndex n k) -
            (degree n : ℂ) * (rootOfUnity n (innerIndex n k) : ℂ)⁻¹) := by
    ring
  rw [hfactor, norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul]
  exact hclose

private lemma modelSlope_inner_ne_zero (n : ℕ) (k : Fin (t n)) :
    modelSlope n (innerIndex n k) ≠ 0 := by
  let v : ℂ := (degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹
  have hvnorm : ‖v‖ = (degree n : ℝ) := by
    simp [v, norm_inv, norm_modelRoot_inner, degree]
  have hclose : ‖modelSlope n (innerIndex n k) - v‖ < (degree n : ℝ) / (n + 2) :=
    modelSlope_inner_close n k
  have hfrac : (degree n : ℝ) / (n + 2) < degree n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : (1 : ℝ) < (n : ℝ) + 2 := by linarith
    exact div_lt_self (mod_cast degree_pos n) hden
  have htri := norm_le_norm_add_norm_sub' v (modelSlope n (innerIndex n k))
  rw [hvnorm] at htri
  have htri' : (degree n : ℝ) ≤ ‖modelSlope n (innerIndex n k)‖ +
      ‖modelSlope n (innerIndex n k) - v‖ := by
    simpa only [norm_sub_rev] using htri
  exact norm_ne_zero_iff.mp (by nlinarith [norm_nonneg (modelSlope n (innerIndex n k))])

private noncomputable def idealSlope (n : ℕ) (k : Fin (t n)) : ℂ :=
  modelRoot n (innerIndex n k) ^ previousDegree n * modelSlope n (innerIndex n k)

private lemma idealSlope_ne_zero (n : ℕ) (k : Fin (t n)) : idealSlope n k ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (modelRoot_ne_zero n (innerIndex n k)))
    (modelSlope_inner_ne_zero n k)

private noncomputable def limitingDerivative (n : ℕ) (w : ℂ) : ℂ :=
  (previousDegree n : ℂ) * w ^ (previousDegree n - 1) * modelBlock n w +
    w ^ previousDegree n * deriv (modelBlock n) w

private lemma continuous_limitingDerivative (n : ℕ) : Continuous (limitingDerivative n) := by
  unfold limitingDerivative
  exact ((continuous_const.mul (continuous_id.pow _)).mul (modelBlock_contDiff n).continuous).add
    ((continuous_id.pow _).mul (continuous_deriv_modelBlock n))

private lemma limitingDerivative_at_inner (n : ℕ) (k : Fin (t n)) :
    limitingDerivative n (modelRoot n (innerIndex n k)) = -idealSlope n k := by
  rw [limitingDerivative, modelBlock_zero, deriv_modelBlock_inner]
  simp [idealSlope]

private lemma exists_affineRadius (n : ℕ) : ∃ η : ℝ,
    0 < η ∧ η < localRadius n ∧
      ∀ k : Fin (t n), ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
        ‖limitingDerivative n w + idealSlope n k‖ <
          ‖idealSlope n k‖ / (8 * (n + 2)) := by
  have hk (k : Fin (t n)) : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
        ‖limitingDerivative n w + idealSlope n k‖ <
          ‖idealSlope n k‖ / (8 * (n + 2)) := by
    let U := {w : ℂ |
      ‖limitingDerivative n w + idealSlope n k‖ <
        ‖idealSlope n k‖ / (8 * (n + 2))}
    have hUopen : IsOpen U := isOpen_lt
      ((continuous_limitingDerivative n).add continuous_const).norm continuous_const
    have hroot : modelRoot n (innerIndex n k) ∈ U := by
      simp only [U, Set.mem_ofPred_eq, limitingDerivative_at_inner, neg_add_cancel, norm_zero]
      positivity [idealSlope_ne_zero n k]
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hUopen _ hroot
    filter_upwards [Iio_mem_nhds hd] with η hη w hw
    apply hball
    exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hη)
  have hall : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ k : Fin (t n), ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
        ‖limitingDerivative n w + idealSlope n k‖ <
          ‖idealSlope n k‖ / (8 * (n + 2)) := by
    simpa only [Finset.mem_univ, true_implies] using
      (Finset.eventually_all (Finset.univ : Finset (Fin (t n)))).2 (fun k _ ↦ hk k)
  have hsmall : ∀ᶠ η : ℝ in 𝓝 0, η < localRadius n :=
    Iio_mem_nhds (localRadius_pos n)
  have hwithin : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0,
      η < localRadius n ∧
        ∀ k : Fin (t n), ∀ w ∈ closedBall (modelRoot n (innerIndex n k)) η,
          ‖limitingDerivative n w + idealSlope n k‖ <
            ‖idealSlope n k‖ / (8 * (n + 2)) :=
    (hsmall.and hall).filter_mono inf_le_left
  have hmem : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0, η ∈ Set.Ioi 0 := self_mem_nhdsWithin
  obtain ⟨η, hη, hηsmall, hηderiv⟩ := (hmem.and hwithin).exists
  exact ⟨η, hη, hηsmall, hηderiv⟩

private noncomputable def affineRadius (n : ℕ) : ℝ := Classical.choose (exists_affineRadius n)

private lemma affineRadius_pos (n : ℕ) : 0 < affineRadius n :=
  (Classical.choose_spec (exists_affineRadius n)).1

private lemma affineRadius_lt_localRadius (n : ℕ) : affineRadius n < localRadius n :=
  (Classical.choose_spec (exists_affineRadius n)).2.1

private lemma limitingDerivative_close (n : ℕ) (k : Fin (t n))
    {w : ℂ} (hw : w ∈ closedBall (modelRoot n (innerIndex n k)) (affineRadius n)) :
    ‖limitingDerivative n w + idealSlope n k‖ <
      ‖idealSlope n k‖ / (8 * (n + 2)) :=
  (Classical.choose_spec (exists_affineRadius n)).2.2 k w hw

/-! Every model root, not only the distinguished inner arc, gets a smaller
localization disk.  These disks are used for the global upper count. -/

private noncomputable def generalModelSlope (n : ℕ) (k : Fin (degree n)) : ℂ :=
  (modelRoot n k)⁻¹ *
    ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase k,
      (1 - modelRoot n k / modelRoot n l)

private lemma generalModelSlope_ne_zero (n : ℕ) (k : Fin (degree n)) :
    generalModelSlope n k ≠ 0 := by
  apply mul_ne_zero (inv_ne_zero (modelRoot_ne_zero n k))
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  rw [Finset.mem_erase] at hl
  intro hzero
  have hdiv : modelRoot n k / modelRoot n l = 1 := (sub_eq_zero.mp hzero).symm
  have hroot : modelRoot n k = modelRoot n l := (div_eq_one_iff_eq (modelRoot_ne_zero n l)).mp hdiv
  exact hl.1 (modelRoot_injective n hroot.symm)

private lemma deriv_modelBlock_at_root (n : ℕ) (k : Fin (degree n)) :
    deriv (modelBlock n) (modelRoot n k) = -generalModelSlope n k := by
  let z := modelRoot n k
  let g : ℂ → ℂ := fun w ↦
    ∏ l ∈ (Finset.univ : Finset (Fin (degree n))).erase k,
      (1 - w / modelRoot n l)
  have hz : z ≠ 0 := modelRoot_ne_zero n k
  have hf : HasDerivAt (fun w : ℂ ↦ 1 - w / z) (-z⁻¹) z := by
    simpa [one_div] using ((hasDerivAt_id z).div_const z).const_sub (1 : ℂ)
  have hg : DifferentiableAt ℂ g z := by
    dsimp only [g]
    fun_prop
  have hraw : HasDerivAt (fun w ↦ (1 - w / z) * g w)
      ((-z⁻¹) * g z + (1 - z / z) * deriv g z) z := by
    apply (hf.mul hg.hasDerivAt).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hderiv : HasDerivAt (fun w ↦ (1 - w / z) * g w)
      (-generalModelSlope n k) z := by
    simpa [hz, g, z, generalModelSlope] using hraw
  have hfun : modelBlock n = fun w ↦ (1 - w / z) * g w := by
    funext w
    exact modelBlock_factor n k w
  rw [hfun]
  exact hderiv.deriv

private noncomputable def generalIdealSlope (n : ℕ) (k : Fin (degree n)) : ℂ :=
  modelRoot n k ^ previousDegree n * generalModelSlope n k

private lemma generalIdealSlope_ne_zero (n : ℕ) (k : Fin (degree n)) :
    generalIdealSlope n k ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (modelRoot_ne_zero n k)) (generalModelSlope_ne_zero n k)

private lemma limitingDerivative_at_root (n : ℕ) (k : Fin (degree n)) :
    limitingDerivative n (modelRoot n k) = -generalIdealSlope n k := by
  rw [limitingDerivative, modelBlock_zero, deriv_modelBlock_at_root]
  simp [generalIdealSlope]

private lemma generalIdealSlope_inner (n : ℕ) (k : Fin (t n)) :
    generalIdealSlope n (innerIndex n k) = idealSlope n k := by
  have hslope : generalModelSlope n (innerIndex n k) =
      modelSlope n (innerIndex n k) := by
    have h₁ := deriv_modelBlock_at_root n (innerIndex n k)
    have h₂ := deriv_modelBlock_inner n k
    rw [h₂] at h₁
    exact neg_injective h₁.symm
  simp only [generalIdealSlope, idealSlope, hslope]

private lemma exists_globalRadius (n : ℕ) : ∃ η : ℝ,
    0 < η ∧ η < affineRadius n ∧
      ∀ k : Fin (degree n), ∀ w ∈ closedBall (modelRoot n k) η,
        ‖limitingDerivative n w + generalIdealSlope n k‖ <
          ‖generalIdealSlope n k‖ / (8 * (n + 2)) := by
  have hk (k : Fin (degree n)) : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ w ∈ closedBall (modelRoot n k) η,
        ‖limitingDerivative n w + generalIdealSlope n k‖ <
          ‖generalIdealSlope n k‖ / (8 * (n + 2)) := by
    let U := {w : ℂ |
      ‖limitingDerivative n w + generalIdealSlope n k‖ <
        ‖generalIdealSlope n k‖ / (8 * (n + 2))}
    have hUopen : IsOpen U := isOpen_lt
      ((continuous_limitingDerivative n).add continuous_const).norm continuous_const
    have hroot : modelRoot n k ∈ U := by
      simp only [U, Set.mem_ofPred_eq, limitingDerivative_at_root, neg_add_cancel, norm_zero]
      positivity [generalIdealSlope_ne_zero n k]
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hUopen _ hroot
    filter_upwards [Iio_mem_nhds hd] with η hη w hw
    exact hball (mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hη))
  have hall : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ k : Fin (degree n), ∀ w ∈ closedBall (modelRoot n k) η,
        ‖limitingDerivative n w + generalIdealSlope n k‖ <
          ‖generalIdealSlope n k‖ / (8 * (n + 2)) := by
    simpa only [Finset.mem_univ, true_implies] using
      (Finset.eventually_all (Finset.univ : Finset (Fin (degree n)))).2 (fun k _ ↦ hk k)
  have hsmall : ∀ᶠ η : ℝ in 𝓝 0, η < affineRadius n :=
    Iio_mem_nhds (affineRadius_pos n)
  have hwithin : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0,
      η < affineRadius n ∧
        ∀ k : Fin (degree n), ∀ w ∈ closedBall (modelRoot n k) η,
          ‖limitingDerivative n w + generalIdealSlope n k‖ <
            ‖generalIdealSlope n k‖ / (8 * (n + 2)) :=
    (hsmall.and hall).filter_mono inf_le_left
  have hmem : ∀ᶠ η : ℝ in 𝓝[Set.Ioi 0] 0, η ∈ Set.Ioi 0 := self_mem_nhdsWithin
  obtain ⟨η, hη, hηsmall, hηderiv⟩ := (hmem.and hwithin).exists
  exact ⟨η, hη, hηsmall, hηderiv⟩

private noncomputable def globalRadius (n : ℕ) : ℝ :=
  Classical.choose (exists_globalRadius n)

private lemma globalRadius_pos (n : ℕ) : 0 < globalRadius n :=
  (Classical.choose_spec (exists_globalRadius n)).1

private lemma globalRadius_lt_affineRadius (n : ℕ) : globalRadius n < affineRadius n :=
  (Classical.choose_spec (exists_globalRadius n)).2.1

private lemma limitingDerivative_close_global (n : ℕ) (k : Fin (degree n))
    {w : ℂ} (hw : w ∈ closedBall (modelRoot n k) (globalRadius n)) :
    ‖limitingDerivative n w + generalIdealSlope n k‖ <
      ‖generalIdealSlope n k‖ / (8 * (n + 2)) :=
  (Classical.choose_spec (exists_globalRadius n)).2.2 k w hw

private def globalModelSet (n : ℕ) : Set ℂ :=
  ⋃ k : Fin (degree n), closedBall (modelRoot n k) (globalRadius n)

private lemma isCompact_globalModelSet (n : ℕ) : IsCompact (globalModelSet n) := by
  unfold globalModelSet
  exact isCompact_iUnion (fun k ↦ isCompact_closedBall (modelRoot n k) (globalRadius n))

private lemma mem_globalModelSet_iff (n : ℕ) (w : ℂ) :
    w ∈ globalModelSet n ↔ ∃ k : Fin (degree n),
      w ∈ closedBall (modelRoot n k) (globalRadius n) := by
  simp [globalModelSet]

private lemma globalModelSet_nonzero (n : ℕ) {w : ℂ} (hw : w ∈ globalModelSet n) : w ≠ 0 := by
  obtain ⟨k, hk⟩ := (mem_globalModelSet_iff n w).mp hw
  intro hwzero
  rw [hwzero, mem_closedBall, dist_zero_left, norm_modelRoot] at hk
  have hroot : 1 ≤ radialScale n (delta n) k := by
    simp only [radialScale]
    split_ifs
    · exact le_rfl
    · exact (one_lt_delta n).le
  have hradius : globalRadius n < 1 / 4 :=
    (globalRadius_lt_affineRadius n).trans
      ((affineRadius_lt_localRadius n).trans
        ((localRadius_lt_modelRadius n).trans (modelRadius_lt_quarter n)))
  linarith

/-! ## Compact normalized models and the rapid-radius recursion -/

private def localModelSet (n : ℕ) : Set ℂ :=
  ⋃ k : Fin (t n), closedBall (modelRoot n (innerIndex n k)) (affineRadius n)

private lemma isCompact_localModelSet (n : ℕ) : IsCompact (localModelSet n) := by
  unfold localModelSet
  exact isCompact_iUnion (fun k ↦ isCompact_closedBall
    (modelRoot n (innerIndex n k)) (affineRadius n))

private lemma mem_localModelSet_iff (n : ℕ) (w : ℂ) :
    w ∈ localModelSet n ↔ ∃ k : Fin (t n),
      w ∈ closedBall (modelRoot n (innerIndex n k)) (affineRadius n) := by
  simp [localModelSet]

private lemma localModelSet_nonzero (n : ℕ) {w : ℂ} (hw : w ∈ localModelSet n) : w ≠ 0 := by
  obtain ⟨k, hk⟩ := (mem_localModelSet_iff n w).mp hw
  intro hwzero
  rw [hwzero, mem_closedBall, dist_zero_left, norm_modelRoot_inner] at hk
  have hlt : affineRadius n < 1 / 4 :=
    (affineRadius_lt_localRadius n).trans
      ((localRadius_lt_modelRadius n).trans (modelRadius_lt_quarter n))
  linarith

private def extendedModelSet (n : ℕ) : Set ℂ := localModelSet n ∪ globalModelSet n

private lemma isCompact_extendedModelSet (n : ℕ) : IsCompact (extendedModelSet n) :=
  (isCompact_localModelSet n).union (isCompact_globalModelSet n)

private lemma localModelSet_subset_extended (n : ℕ) :
    localModelSet n ⊆ extendedModelSet n := fun _ hw ↦ Or.inl hw

private lemma globalModelSet_subset_extended (n : ℕ) :
    globalModelSet n ⊆ extendedModelSet n := fun _ hw ↦ Or.inr hw

private lemma extendedModelSet_nonzero (n : ℕ) {w : ℂ}
    (hw : w ∈ extendedModelSet n) : w ≠ 0 := by
  rcases hw with hw | hw
  · exact localModelSet_nonzero n hw
  · exact globalModelSet_nonzero n hw

private lemma modelBlock_eq_zero_iff (n : ℕ) (w : ℂ) :
    modelBlock n w = 0 ↔ ∃ k : Fin (degree n), w = modelRoot n k := by
  classical
  rw [modelBlock, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro k
  have hk := modelRoot_ne_zero n k
  constructor
  · intro h
    have hdiv : w / modelRoot n k = 1 := (sub_eq_zero.mp h).symm
    exact (div_eq_one_iff_eq hk).mp hdiv
  · rintro rfl
    simp [hk]

private def modelAnnulus : Set ℂ := closedBall 0 4 \ ball 0 (1 / 4)

private lemma isCompact_modelAnnulus : IsCompact modelAnnulus :=
  (isCompact_closedBall (0 : ℂ) 4).diff (isOpen_ball : IsOpen (ball (0 : ℂ) (1 / 4)))

private lemma modelAnnulus_nonzero {w : ℂ} (hw : w ∈ modelAnnulus) : w ≠ 0 := by
  intro h
  subst w
  exact hw.2 (mem_ball_self (by norm_num))

private def exceptionalModelSet (n : ℕ) : Set ℂ :=
  ⋃ k : Fin (degree n), ball (modelRoot n k) (globalRadius n)

private lemma isOpen_exceptionalModelSet (n : ℕ) : IsOpen (exceptionalModelSet n) := by
  unfold exceptionalModelSet
  exact isOpen_iUnion (fun _ ↦ isOpen_ball)

private def escapeModelSet (n : ℕ) : Set ℂ :=
  modelAnnulus \ exceptionalModelSet n

private lemma isCompact_escapeModelSet (n : ℕ) : IsCompact (escapeModelSet n) :=
  isCompact_modelAnnulus.diff (isOpen_exceptionalModelSet n)

private lemma modelBlock_ne_zero_on_escape (n : ℕ) {w : ℂ}
    (hw : w ∈ escapeModelSet n) : modelBlock n w ≠ 0 := by
  intro hz
  obtain ⟨k, rfl⟩ := (modelBlock_eq_zero_iff n w).mp hz
  exact hw.2 (Set.mem_iUnion.2 ⟨k, mem_ball_self (globalRadius_pos n)⟩)

private lemma exists_pos_lower_bound_on_compact {K : Set ℂ} (hK : IsCompact K)
    (g : ℂ → ℂ) (hg : ContinuousOn g K) (hgne : ∀ w ∈ K, g w ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ K, c ≤ ‖g w‖ := by
  by_cases hne : K.Nonempty
  · obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne (continuous_norm.comp_continuousOn hg)
    refine ⟨‖g w‖, norm_pos_iff.mpr (hgne w hw), fun z hz ↦ hmin hz⟩
  · refine ⟨1, by norm_num, fun w hw ↦ ?_⟩
    exact (hne ⟨w, hw⟩).elim

private noncomputable def limitingValue (n : ℕ) (w : ℂ) : ℂ :=
  w ^ previousDegree n * modelBlock n w

private lemma exists_escapeMinimum (n : ℕ) : ∃ c : ℝ, 0 < c ∧
    ∀ w ∈ escapeModelSet n, c ≤ ‖limitingValue n w‖ := by
  have hcont : Continuous (limitingValue n) := by
    unfold limitingValue
    exact (continuous_id.pow _).mul (modelBlock_contDiff n).continuous
  apply exists_pos_lower_bound_on_compact (isCompact_escapeModelSet n)
    (limitingValue n) hcont.continuousOn
  intro w hw
  exact mul_ne_zero (pow_ne_zero _ (modelAnnulus_nonzero hw.1))
    (modelBlock_ne_zero_on_escape n hw)

private noncomputable def escapeMinimum (n : ℕ) : ℝ :=
  Classical.choose (exists_escapeMinimum n)

private lemma escapeMinimum_pos (n : ℕ) : 0 < escapeMinimum n :=
  (Classical.choose_spec (exists_escapeMinimum n)).1

private lemma escapeMinimum_le (n : ℕ) {w : ℂ} (hw : w ∈ escapeModelSet n) :
    escapeMinimum n ≤ ‖limitingValue n w‖ :=
  (Classical.choose_spec (exists_escapeMinimum n)).2 w hw

private lemma exists_insideMinimum (n : ℕ) : ∃ c : ℝ, 0 < c ∧
    ∀ w ∈ closedBall (0 : ℂ) (1 / 2), c ≤ ‖modelBlock n w‖ := by
  apply exists_pos_lower_bound_on_compact (isCompact_closedBall (0 : ℂ) (1 / 2))
    (modelBlock n) (modelBlock_contDiff n).continuous.continuousOn
  intro w hw hz
  obtain ⟨k, hk⟩ := (modelBlock_eq_zero_iff n w).mp hz
  have hrootNorm : 1 ≤ ‖modelRoot n k‖ := by
    rw [norm_modelRoot]
    simp only [radialScale]
    split_ifs
    · exact le_rfl
    · exact (one_lt_delta n).le
  rw [hk, mem_closedBall, dist_zero_right] at hw
  linarith

private noncomputable def insideMinimum (n : ℕ) : ℝ :=
  Classical.choose (exists_insideMinimum n)

private lemma insideMinimum_pos (n : ℕ) : 0 < insideMinimum n :=
  (Classical.choose_spec (exists_insideMinimum n)).1

private lemma insideMinimum_le (n : ℕ) {w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) (1 / 2)) :
    insideMinimum n ≤ ‖modelBlock n w‖ :=
  (Classical.choose_spec (exists_insideMinimum n)).2 w hw

private structure RadiusState where
  radius : ℕ → ℝ
  budget : ℕ → ℝ

private abbrev PreviousIndex (n : ℕ) := Σ j : Fin n, Fin (degree j)

private noncomputable instance previousIndexFintype (n : ℕ) : Fintype (PreviousIndex n) :=
  inferInstanceAs (Fintype (Σ j : Fin n, Fin (degree j)))

private noncomputable instance previousIndexDecidableEq (n : ℕ) : DecidableEq (PreviousIndex n) :=
  Classical.decEq _

private noncomputable def previousRoot (s : RadiusState) (n : ℕ)
    (i : PreviousIndex n) : ℂ :=
  s.radius i.1 * modelRoot i.1 i.2

private noncomputable def correction (s : RadiusState) (n : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  ∏ i : PreviousIndex n, (1 - (x : ℂ) * previousRoot s n i / w)

private noncomputable def correctionDerivative
    (s : RadiusState) (n : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  ∑ i : PreviousIndex n,
    ((x : ℂ) * previousRoot s n i / w ^ 2) *
      ∏ l ∈ (Finset.univ : Finset (PreviousIndex n)).erase i,
        (1 - (x : ℂ) * previousRoot s n l / w)

private noncomputable def normalizedDerivative
    (s : RadiusState) (n : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  (previousDegree n : ℂ) * w ^ (previousDegree n - 1) * correction s n x w *
      modelBlock n w +
    w ^ previousDegree n * correctionDerivative s n x w * modelBlock n w +
    w ^ previousDegree n * correction s n x w * deriv (modelBlock n) w

@[simp] private lemma correction_zero (s : RadiusState) (n : ℕ) (w : ℂ) :
    correction s n 0 w = 1 := by simp [correction]

@[simp] private lemma correctionDerivative_zero (s : RadiusState) (n : ℕ) (w : ℂ) :
    correctionDerivative s n 0 w = 0 := by simp [correctionDerivative]

@[simp] private lemma normalizedDerivative_zero (s : RadiusState) (n : ℕ) (w : ℂ) :
    normalizedDerivative s n 0 w = limitingDerivative n w := by
  simp [normalizedDerivative, limitingDerivative]

private lemma continuousOn_normalizedDerivative (s : RadiusState) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℂ ↦ normalizedDerivative s n p.1 p.2)
      (Set.Icc (-1) 1 ×ˢ extendedModelSet n) := by
  have hne : ∀ p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ extendedModelSet n, p.2 ≠ 0 := by
    intro p hp
    exact extendedModelSet_nonzero n hp.2
  let K : Set (ℝ × ℂ) := Set.Icc (-1) 1 ×ˢ extendedModelSet n
  have hx : ContinuousOn (fun p : ℝ × ℂ ↦ (p.1 : ℂ)) K :=
    Complex.continuous_ofReal.comp continuous_fst |>.continuousOn
  have hw : ContinuousOn (fun p : ℝ × ℂ ↦ p.2) K := continuous_snd.continuousOn
  have hfactor (i : PreviousIndex n) : ContinuousOn
      (fun p : ℝ × ℂ ↦ 1 - (p.1 : ℂ) * previousRoot s n i / p.2) K := by
    exact continuousOn_const.sub ((hx.mul continuousOn_const).div hw hne)
  have hprod (t : Finset (PreviousIndex n)) : ContinuousOn
      (fun p : ℝ × ℂ ↦ ∏ i ∈ t, (1 - (p.1 : ℂ) * previousRoot s n i / p.2)) K := by
    induction t using Finset.induction with
    | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × ℂ ↦ (1 : ℂ)) K)
    | @insert i t hit ih =>
        simp only [Finset.prod_insert hit]
        exact (hfactor i).mul ih
  have hcorr : ContinuousOn (fun p : ℝ × ℂ ↦ correction s n p.1 p.2) K := by
    simpa [correction] using hprod (Finset.univ : Finset (PreviousIndex n))
  have hfirst (i : PreviousIndex n) : ContinuousOn
      (fun p : ℝ × ℂ ↦ (p.1 : ℂ) * previousRoot s n i / p.2 ^ 2) K := by
    exact (hx.mul continuousOn_const).div (hw.pow 2) (fun p hp ↦ pow_ne_zero _ (hne p hp))
  have hterm (i : PreviousIndex n) : ContinuousOn
      (fun p : ℝ × ℂ ↦
        ((p.1 : ℂ) * previousRoot s n i / p.2 ^ 2) *
          ∏ l ∈ (Finset.univ : Finset (PreviousIndex n)).erase i,
            (1 - (p.1 : ℂ) * previousRoot s n l / p.2)) K :=
    (hfirst i).mul (hprod ((Finset.univ : Finset (PreviousIndex n)).erase i))
  have hsum (t : Finset (PreviousIndex n)) : ContinuousOn
      (fun p : ℝ × ℂ ↦ ∑ i ∈ t,
        ((p.1 : ℂ) * previousRoot s n i / p.2 ^ 2) *
          ∏ l ∈ (Finset.univ : Finset (PreviousIndex n)).erase i,
            (1 - (p.1 : ℂ) * previousRoot s n l / p.2)) K := by
    induction t using Finset.induction with
    | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × ℂ ↦ (0 : ℂ)) K)
    | @insert i t hit ih =>
        simp only [Finset.sum_insert hit]
        exact (hterm i).add ih
  have hcorrDeriv : ContinuousOn
      (fun p : ℝ × ℂ ↦ correctionDerivative s n p.1 p.2) K := by
    simpa [correctionDerivative] using hsum (Finset.univ : Finset (PreviousIndex n))
  have hb : ContinuousOn (fun p : ℝ × ℂ ↦ modelBlock n p.2) K :=
    (modelBlock_contDiff n).continuous.comp_continuousOn continuous_snd.continuousOn
  have hdb : ContinuousOn (fun p : ℝ × ℂ ↦ deriv (modelBlock n) p.2) K :=
    (continuous_deriv_modelBlock n).comp_continuousOn continuous_snd.continuousOn
  unfold normalizedDerivative
  exact ((((continuousOn_const.mul (hw.pow _)).mul hcorr).mul hb).add
    (((hw.pow _).mul hcorrDeriv).mul hb)).add
      (((hw.pow _).mul hcorr).mul hdb)

private lemma normalizedDerivative_uniform_at_zero (s : RadiusState) (n : ℕ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x| < δ → ∀ w ∈ extendedModelSet n,
      ‖normalizedDerivative s n x w - limitingDerivative n w‖ < ε := by
  intro ε hε
  let K : Set (ℝ × ℂ) := Set.Icc (-1) 1 ×ˢ extendedModelSet n
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_extendedModelSet n)
  have hu : UniformContinuousOn (fun p : ℝ × ℂ ↦ normalizedDerivative s n p.1 p.2) K :=
    hK.uniformContinuousOn_of_continuous (continuousOn_normalizedDerivative s n)
  obtain ⟨δ₀, hδ₀, hδ₀spec⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let δ := min δ₀ 1
  refine ⟨δ, lt_min hδ₀ (by norm_num), fun x hx w hw ↦ ?_⟩
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hx1 : |x| < 1 := hx.trans_le (min_le_right _ _)
    exact abs_le.mp hx1.le
  have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
  have hdist : dist (x, w) ((0 : ℝ), w) < δ₀ := by
    rw [dist_prod_same_right, Real.dist_0_eq_abs]
    exact hx.trans_le (min_le_left _ _)
  have := hδ₀spec (x, w) ⟨hxIcc, hw⟩ (0, w) ⟨hzeroIcc, hw⟩ hdist
  simpa [dist_eq_norm] using this

private noncomputable def normalizedValue
    (s : RadiusState) (n : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  w ^ previousDegree n * correction s n x w * modelBlock n w

@[simp] private lemma normalizedValue_zero (s : RadiusState) (n : ℕ) (w : ℂ) :
    normalizedValue s n 0 w = limitingValue n w := by
  simp [normalizedValue, limitingValue]

private lemma continuousOn_normalizedValue (s : RadiusState) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℂ ↦ normalizedValue s n p.1 p.2)
      (Set.Icc (-1) 1 ×ˢ extendedModelSet n) := by
  let K : Set (ℝ × ℂ) := Set.Icc (-1) 1 ×ˢ extendedModelSet n
  have hne : ∀ p ∈ K, p.2 ≠ 0 := fun p hp ↦ extendedModelSet_nonzero n hp.2
  have hx : ContinuousOn (fun p : ℝ × ℂ ↦ (p.1 : ℂ)) K :=
    Complex.continuous_ofReal.comp continuous_fst |>.continuousOn
  have hw : ContinuousOn (fun p : ℝ × ℂ ↦ p.2) K := continuous_snd.continuousOn
  have hfactor (i : PreviousIndex n) : ContinuousOn
      (fun p : ℝ × ℂ ↦ 1 - (p.1 : ℂ) * previousRoot s n i / p.2) K :=
    continuousOn_const.sub ((hx.mul continuousOn_const).div hw hne)
  have hprod (t : Finset (PreviousIndex n)) : ContinuousOn
      (fun p : ℝ × ℂ ↦ ∏ i ∈ t, (1 - (p.1 : ℂ) * previousRoot s n i / p.2)) K := by
    induction t using Finset.induction with
    | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × ℂ ↦ (1 : ℂ)) K)
    | @insert i t hit ih =>
        simp only [Finset.prod_insert hit]
        exact (hfactor i).mul ih
  have hcorr : ContinuousOn (fun p : ℝ × ℂ ↦ correction s n p.1 p.2) K := by
    simpa [correction] using hprod (Finset.univ : Finset (PreviousIndex n))
  have hb : ContinuousOn (fun p : ℝ × ℂ ↦ modelBlock n p.2) K :=
    (modelBlock_contDiff n).continuous.comp_continuousOn continuous_snd.continuousOn
  unfold normalizedValue
  exact ((hw.pow _).mul hcorr).mul hb

private lemma normalizedValue_uniform_at_zero (s : RadiusState) (n : ℕ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x| < δ → ∀ w ∈ extendedModelSet n,
      ‖normalizedValue s n x w - limitingValue n w‖ < ε := by
  intro ε hε
  let K : Set (ℝ × ℂ) := Set.Icc (-1) 1 ×ˢ extendedModelSet n
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_extendedModelSet n)
  have hu : UniformContinuousOn (fun p : ℝ × ℂ ↦ normalizedValue s n p.1 p.2) K :=
    hK.uniformContinuousOn_of_continuous (continuousOn_normalizedValue s n)
  obtain ⟨δ₀, hδ₀, hδ₀spec⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let δ := min δ₀ 1
  refine ⟨δ, lt_min hδ₀ (by norm_num), fun x hx w hw ↦ ?_⟩
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hx1 : |x| < 1 := hx.trans_le (min_le_right _ _)
    exact abs_le.mp hx1.le
  have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
  have hdist : dist (x, w) ((0 : ℝ), w) < δ₀ := by
    rw [dist_prod_same_right, Real.dist_0_eq_abs]
    exact hx.trans_le (min_le_left _ _)
  have := hδ₀spec (x, w) ⟨hxIcc, hw⟩ (0, w) ⟨hzeroIcc, hw⟩ hdist
  simpa [dist_eq_norm] using this

private lemma continuousOn_normalizedValue_annulus (s : RadiusState) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℂ ↦ normalizedValue s n p.1 p.2)
      (Set.Icc (-1) 1 ×ˢ modelAnnulus) := by
  let K : Set (ℝ × ℂ) := Set.Icc (-1) 1 ×ˢ modelAnnulus
  have hne : ∀ p ∈ K, p.2 ≠ 0 := fun p hp ↦ modelAnnulus_nonzero hp.2
  have hx : ContinuousOn (fun p : ℝ × ℂ ↦ (p.1 : ℂ)) K :=
    Complex.continuous_ofReal.comp continuous_fst |>.continuousOn
  have hw : ContinuousOn (fun p : ℝ × ℂ ↦ p.2) K := continuous_snd.continuousOn
  have hfactor (i : PreviousIndex n) : ContinuousOn
      (fun p : ℝ × ℂ ↦ 1 - (p.1 : ℂ) * previousRoot s n i / p.2) K :=
    continuousOn_const.sub ((hx.mul continuousOn_const).div hw hne)
  have hprod (t : Finset (PreviousIndex n)) : ContinuousOn
      (fun p : ℝ × ℂ ↦ ∏ i ∈ t, (1 - (p.1 : ℂ) * previousRoot s n i / p.2)) K := by
    induction t using Finset.induction with
    | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × ℂ ↦ (1 : ℂ)) K)
    | @insert i t hit ih =>
        simp only [Finset.prod_insert hit]
        exact (hfactor i).mul ih
  have hcorr : ContinuousOn (fun p : ℝ × ℂ ↦ correction s n p.1 p.2) K := by
    simpa [correction] using hprod (Finset.univ : Finset (PreviousIndex n))
  have hb : ContinuousOn (fun p : ℝ × ℂ ↦ modelBlock n p.2) K :=
    (modelBlock_contDiff n).continuous.comp_continuousOn continuous_snd.continuousOn
  unfold normalizedValue
  exact ((hw.pow _).mul hcorr).mul hb

private lemma normalizedValue_uniform_on_annulus (s : RadiusState) (n : ℕ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x| < δ → ∀ w ∈ modelAnnulus,
      ‖normalizedValue s n x w - limitingValue n w‖ < ε := by
  intro ε hε
  let K : Set (ℝ × ℂ) := Set.Icc (-1) 1 ×ˢ modelAnnulus
  have hK : IsCompact K := isCompact_Icc.prod isCompact_modelAnnulus
  have hu : UniformContinuousOn (fun p : ℝ × ℂ ↦ normalizedValue s n p.1 p.2) K :=
    hK.uniformContinuousOn_of_continuous (continuousOn_normalizedValue_annulus s n)
  obtain ⟨δ₀, hδ₀, hδ₀spec⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let δ := min δ₀ 1
  refine ⟨δ, lt_min hδ₀ (by norm_num), fun x hx w hw ↦ ?_⟩
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hx1 : |x| < 1 := hx.trans_le (min_le_right _ _)
    exact abs_le.mp hx1.le
  have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
  have hdist : dist (x, w) ((0 : ℝ), w) < δ₀ := by
    rw [dist_prod_same_right, Real.dist_0_eq_abs]
    exact hx.trans_le (min_le_left _ _)
  have := hδ₀spec (x, w) ⟨hxIcc, hw⟩ (0, w) ⟨hzeroIcc, hw⟩ hdist
  simpa [dist_eq_norm] using this

private lemma exists_derivativeMargin (n : ℕ) : ∃ ε : ℝ, 0 < ε ∧
    (∀ k : Fin (t n), ε < ‖idealSlope n k‖ / (8 * (n + 2))) ∧
    (∀ k : Fin (degree n), ε < ‖generalIdealSlope n k‖ / (8 * (n + 2))) := by
  have hk (k : Fin (t n)) : ∀ᶠ ε : ℝ in 𝓝 0,
      ε < ‖idealSlope n k‖ / (8 * (n + 2)) :=
    Iio_mem_nhds (by positivity [idealSlope_ne_zero n k])
  have hall : ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ k : Fin (t n), ε < ‖idealSlope n k‖ / (8 * (n + 2)) := by
    simpa only [Finset.mem_univ, true_implies] using
      (Finset.eventually_all (Finset.univ : Finset (Fin (t n)))).2 (fun k _ ↦ hk k)
  have hkg (k : Fin (degree n)) : ∀ᶠ ε : ℝ in 𝓝 0,
      ε < ‖generalIdealSlope n k‖ / (8 * (n + 2)) :=
    Iio_mem_nhds (by positivity [generalIdealSlope_ne_zero n k])
  have hallg : ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ k : Fin (degree n), ε < ‖generalIdealSlope n k‖ / (8 * (n + 2)) := by
    simpa only [Finset.mem_univ, true_implies] using
      (Finset.eventually_all (Finset.univ : Finset (Fin (degree n)))).2 (fun k _ ↦ hkg k)
  have hmem : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ε ∈ Set.Ioi 0 := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεall, hεallg⟩ :=
    (hmem.and ((hall.and hallg).filter_mono inf_le_left)).exists
  exact ⟨ε, hε, hεall, hεallg⟩

private noncomputable def derivativeMargin (n : ℕ) : ℝ :=
  Classical.choose (exists_derivativeMargin n)

private lemma derivativeMargin_pos (n : ℕ) : 0 < derivativeMargin n :=
  (Classical.choose_spec (exists_derivativeMargin n)).1

private lemma derivativeMargin_lt (n : ℕ) (k : Fin (t n)) :
    derivativeMargin n < ‖idealSlope n k‖ / (8 * (n + 2)) :=
  (Classical.choose_spec (exists_derivativeMargin n)).2.1 k

private lemma derivativeMargin_lt_global (n : ℕ) (k : Fin (degree n)) :
    derivativeMargin n < ‖generalIdealSlope n k‖ / (8 * (n + 2)) :=
  (Classical.choose_spec (exists_derivativeMargin n)).2.2 k

private lemma exists_pos_norm_bound_on_compact {K : Set ℂ} (hK : IsCompact K)
    (g : ℂ → ℂ) (hg : ContinuousOn g K) :
    ∃ B : ℝ, 0 < B ∧ ∀ w ∈ K, ‖g w‖ < B := by
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn hg).isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun w hw ↦ ?_⟩
  have hmem := hR ⟨w, hw, rfl⟩
  rw [mem_closedBall, dist_zero_right] at hmem
  exact hmem.trans_lt (lt_of_le_of_lt (le_abs_self R) (lt_add_one |R|))

private lemma exists_modelBound (n : ℕ) : ∃ B : ℝ, 0 < B ∧
    derivativeMargin n < B ∧ 1 < B ∧
    (∀ w ∈ extendedModelSet n, ‖limitingDerivative n w‖ < B) ∧
    (∀ w ∈ extendedModelSet n, ‖limitingValue n w‖ < B) := by
  obtain ⟨B₁, hB₁, hderiv⟩ := exists_pos_norm_bound_on_compact
    (isCompact_extendedModelSet n) (limitingDerivative n)
      (continuous_limitingDerivative n).continuousOn
  have hvalueCont : Continuous (limitingValue n) := by
    unfold limitingValue
    exact (continuous_id.pow _).mul (modelBlock_contDiff n).continuous
  obtain ⟨B₂, hB₂, hvalue⟩ := exists_pos_norm_bound_on_compact
    (isCompact_extendedModelSet n) (limitingValue n) hvalueCont.continuousOn
  let B := max (max B₁ B₂) (derivativeMargin n + 1)
  refine ⟨B, lt_of_lt_of_le hB₁ ((le_max_left B₁ B₂).trans (le_max_left _ _)),
    ?_, ?_, ?_, ?_⟩
  · exact (lt_add_one (derivativeMargin n)).trans_le (le_max_right _ _)
  · have := derivativeMargin_pos n
    exact (by linarith : 1 < derivativeMargin n + 1).trans_le (le_max_right _ _)
  · exact fun w hw ↦ (hderiv w hw).trans_le
      ((le_max_left B₁ B₂).trans (le_max_left _ _))
  · exact fun w hw ↦ (hvalue w hw).trans_le
      ((le_max_right B₁ B₂).trans (le_max_left _ _))

private noncomputable def modelBound (n : ℕ) : ℝ := Classical.choose (exists_modelBound n)

private lemma modelBound_pos (n : ℕ) : 0 < modelBound n :=
  (Classical.choose_spec (exists_modelBound n)).1

private lemma derivativeMargin_lt_modelBound (n : ℕ) : derivativeMargin n < modelBound n :=
  (Classical.choose_spec (exists_modelBound n)).2.1

private lemma one_lt_modelBound (n : ℕ) : 1 < modelBound n :=
  (Classical.choose_spec (exists_modelBound n)).2.2.1

private lemma norm_limitingDerivative_lt_modelBound (n : ℕ) {w : ℂ}
    (hw : w ∈ extendedModelSet n) : ‖limitingDerivative n w‖ < modelBound n :=
  (Classical.choose_spec (exists_modelBound n)).2.2.2.1 w hw

private lemma norm_limitingValue_lt_modelBound (n : ℕ) {w : ℂ}
    (hw : w ∈ extendedModelSet n) : ‖limitingValue n w‖ < modelBound n :=
  (Classical.choose_spec (exists_modelBound n)).2.2.2.2 w hw

private lemma exists_tailTolerance (n : ℕ) : ∃ ε : ℝ,
    0 < ε ∧ ε < 1 / 2 ∧ ε * (2 * modelBound n + 3) < derivativeMargin n := by
  have hmul : ∀ᶠ ε : ℝ in 𝓝 0,
      ε * (2 * modelBound n + 3) < derivativeMargin n := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ε * (2 * modelBound n + 3)) 0 :=
      continuousAt_id.mul continuousAt_const
    have hzero : (fun ε : ℝ ↦ ε * (2 * modelBound n + 3)) 0 < derivativeMargin n := by
      simpa using derivativeMargin_pos n
    exact hc.eventually (Iio_mem_nhds hzero)
  have hhalf : ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 / 2 := Iio_mem_nhds (by norm_num)
  have hwithin : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0,
      ε < 1 / 2 ∧ ε * (2 * modelBound n + 3) < derivativeMargin n :=
    (hhalf.and hmul).filter_mono inf_le_left
  have hmem : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ε ∈ Set.Ioi 0 := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεhalf, hεmul⟩ := (hmem.and hwithin).exists
  exact ⟨ε, hε, hεhalf, hεmul⟩

private noncomputable def tailTolerance (n : ℕ) : ℝ :=
  Classical.choose (exists_tailTolerance n)

private lemma tailTolerance_pos (n : ℕ) : 0 < tailTolerance n :=
  (Classical.choose_spec (exists_tailTolerance n)).1

private lemma tailTolerance_lt_half (n : ℕ) : tailTolerance n < 1 / 2 :=
  (Classical.choose_spec (exists_tailTolerance n)).2.1

private lemma tailTolerance_mul_bound (n : ℕ) :
    tailTolerance n * (2 * modelBound n + 3) < derivativeMargin n :=
  (Classical.choose_spec (exists_tailTolerance n)).2.2

private noncomputable def tailBudget (n : ℕ) : ℝ := Real.log (1 + tailTolerance n)

private lemma tailBudget_pos (n : ℕ) : 0 < tailBudget n := by
  rw [tailBudget, Real.log_pos_iff]
  all_goals linarith [tailTolerance_pos n]

private lemma exists_uniformScaleBound (s : RadiusState) (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧
    (∀ x : ℝ, |x| < δ → ∀ w ∈ extendedModelSet n,
      ‖normalizedDerivative s n x w - limitingDerivative n w‖ < derivativeMargin n) ∧
    (∀ x : ℝ, |x| < δ → ∀ w ∈ extendedModelSet n,
      ‖normalizedValue s n x w - limitingValue n w‖ < 1) ∧
    (∀ x : ℝ, |x| < δ → ∀ w ∈ modelAnnulus,
      ‖normalizedValue s n x w - limitingValue n w‖ < escapeMinimum n / 2) := by
  obtain ⟨δ₁, hδ₁, hderiv⟩ := normalizedDerivative_uniform_at_zero s n
    (derivativeMargin n) (derivativeMargin_pos n)
  obtain ⟨δ₂, hδ₂, hvalue⟩ := normalizedValue_uniform_at_zero s n 1 (by norm_num)
  obtain ⟨δ₃, hδ₃, hshell⟩ := normalizedValue_uniform_on_annulus s n
    (escapeMinimum n / 2) (by positivity [escapeMinimum_pos n])
  let δ := min (min δ₁ δ₂) δ₃
  refine ⟨δ, lt_min (lt_min hδ₁ hδ₂) hδ₃, ?_, ?_, ?_⟩
  · exact fun x hx ↦ hderiv x (hx.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  · exact fun x hx ↦ hvalue x (hx.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  · exact fun x hx ↦ hshell x (hx.trans_le (min_le_right _ _))

private noncomputable def uniformScaleBound (s : RadiusState) (n : ℕ) : ℝ :=
  Classical.choose (exists_uniformScaleBound s n)

private lemma uniformScaleBound_pos (s : RadiusState) (n : ℕ) :
    0 < uniformScaleBound s n :=
  (Classical.choose_spec (exists_uniformScaleBound s n)).1

private lemma normalizedDerivative_scale_close (s : RadiusState) (n : ℕ)
    {x : ℝ} (hx : |x| < uniformScaleBound s n) {w : ℂ} (hw : w ∈ extendedModelSet n) :
    ‖normalizedDerivative s n x w - limitingDerivative n w‖ < derivativeMargin n :=
  (Classical.choose_spec (exists_uniformScaleBound s n)).2.1 x hx w hw

private lemma normalizedValue_scale_close (s : RadiusState) (n : ℕ)
    {x : ℝ} (hx : |x| < uniformScaleBound s n) {w : ℂ} (hw : w ∈ extendedModelSet n) :
    ‖normalizedValue s n x w - limitingValue n w‖ < 1 :=
  (Classical.choose_spec (exists_uniformScaleBound s n)).2.2.1 x hx w hw

private lemma normalizedValue_shell_close (s : RadiusState) (n : ℕ)
    {x : ℝ} (hx : |x| < uniformScaleBound s n) {w : ℂ} (hw : w ∈ modelAnnulus) :
    ‖normalizedValue s n x w - limitingValue n w‖ < escapeMinimum n / 2 :=
  (Classical.choose_spec (exists_uniformScaleBound s n)).2.2.2 x hx w hw

private noncomputable def leadingCoefficient (s : RadiusState) (n : ℕ) : ℂ :=
  ∏ i : PreviousIndex n, (-previousRoot s n i)⁻¹

private noncomputable def modelLeadingMagnitude (n : ℕ) : ℝ :=
  ∏ k : Fin (degree n), ‖modelRoot n k‖⁻¹

private lemma modelLeadingMagnitude_pos (n : ℕ) : 0 < modelLeadingMagnitude n := by
  apply Finset.prod_pos
  intro k _
  positivity [modelRoot_ne_zero n k]

private noncomputable def gapConstant (n : ℕ) : ℝ :=
  modelLeadingMagnitude n * 2 ^ (previousDegree n + degree n)

private lemma gapConstant_pos (n : ℕ) : 0 < gapConstant n := by
  exact mul_pos (modelLeadingMagnitude_pos n) (by positivity)

private def StateValid (n : ℕ) (s : RadiusState) : Prop :=
  ∀ i : ℕ, i < n → 0 < s.radius i

private lemma previousRoot_ne_zero_of_valid {n : ℕ} {s : RadiusState}
    (hs : StateValid n s) (i : PreviousIndex n) : previousRoot s n i ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (hs i.1 i.1.isLt).ne'
  · exact modelRoot_ne_zero i.1 i.2

private lemma leadingCoefficient_ne_zero_of_valid {n : ℕ} {s : RadiusState}
    (hs : StateValid n s) : leadingCoefficient s n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact inv_ne_zero (neg_ne_zero.mpr (previousRoot_ne_zero_of_valid hs i))

private noncomputable def tailControl (s : RadiusState) (i : ℕ) : ℝ :=
  8 * (modelBound i + 1) * |s.radius i| + 1

private def RadiusAdmissible (s : RadiusState) (n : ℕ) (R : ℝ) : Prop :=
  1 < R ∧
  1 / R < uniformScaleBound s n ∧
  (degree n : ℝ) / R < (1 / 2 : ℝ) ^ n ∧
  (∀ i : ℕ, i < n → 32 * |s.radius i| + 32 < R) ∧
  (∀ i : ℕ, i < n →
    (degree n : ℝ) * tailControl s i / R <
      tailBudget i / (2 : ℝ) ^ (n + 1)) ∧
  (n ≠ 0 →
    (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
      derivativeMargin n * affineRadius n) ∧
  (n ≠ 0 →
    (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
      derivativeMargin n * globalRadius n) ∧
  (n ≠ 0 →
    4 * (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
      escapeMinimum n) ∧
  (n ≠ 0 →
    4 * (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
      gapConstant n * insideMinimum (n + 1))

private lemma eventually_const_mul_pow_gt {C N : ℝ} {m : ℕ}
    (hC : 0 < C) (hm : 0 < m) : ∀ᶠ R : ℝ in atTop, N < C * R ^ m := by
  filter_upwards [eventually_gt_atTop (max 1 (N / C + 1))] with R hR
  have hRone : 1 < R := (le_max_left _ _).trans_lt hR
  have hRN : N / C + 1 < R := (le_max_right _ _).trans_lt hR
  have hlin : N < C * R := by
    have : N / C < R := by linarith
    rw [div_lt_iff₀ hC] at this
    simpa [mul_comm] using this
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [pow_succ]
  have hpow : 1 ≤ R ^ q := one_le_pow₀ hRone.le
  have hnonneg : 0 ≤ C * R ^ q :=
    mul_nonneg hC.le (pow_nonneg (zero_le_one.trans hRone.le) q)
  have hRpow : R ≤ R ^ q * R := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hpow (zero_le_one.trans hRone.le))
  exact hlin.trans_le (mul_le_mul_of_nonneg_left hRpow hC.le)

private lemma exists_admissibleRadius (s : RadiusState) (n : ℕ) (hs : StateValid n s) :
    ∃ R : ℝ, RadiusAdmissible s n R := by
  have hRone : ∀ᶠ R : ℝ in atTop, 1 < R := eventually_gt_atTop 1
  have hinv : ∀ᶠ R : ℝ in atTop, 1 / R < uniformScaleBound s n := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero.eventually (Iio_mem_nhds (uniformScaleBound_pos s n)))
  have hdegree : ∀ᶠ R : ℝ in atTop,
      (degree n : ℝ) / R < (1 / 2 : ℝ) ^ n := by
    have hlim : Tendsto (fun R : ℝ ↦ (degree n : ℝ) * R⁻¹) atTop (𝓝 0) :=
      by
        simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (degree n : ℝ)) atTop
          (𝓝 (degree n : ℝ))).mul tendsto_inv_atTop_zero)
    simpa only [div_eq_mul_inv] using
      hlim.eventually (Iio_mem_nhds (by positivity : 0 < (1 / 2 : ℝ) ^ n))
  have hsep : ∀ᶠ R : ℝ in atTop,
      ∀ i : ℕ, i < n → 32 * |s.radius i| + 32 < R := by
    have hi (i : Fin n) : ∀ᶠ R : ℝ in atTop, 32 * |s.radius i| + 32 < R :=
      eventually_gt_atTop _
    have hall : ∀ᶠ R : ℝ in atTop, ∀ i : Fin n, 32 * |s.radius i| + 32 < R := by
      simpa only [Finset.mem_univ, true_implies] using
        (Finset.eventually_all (Finset.univ : Finset (Fin n))).2 (fun i _ ↦ hi i)
    exact hall.mono fun R h i hi ↦ h ⟨i, hi⟩
  have htail : ∀ᶠ R : ℝ in atTop, ∀ i : ℕ, i < n →
      (degree n : ℝ) * tailControl s i / R <
        tailBudget i / (2 : ℝ) ^ (n + 1) := by
    have hi (i : Fin n) : ∀ᶠ R : ℝ in atTop,
        (degree n : ℝ) * tailControl s i / R <
          tailBudget i / (2 : ℝ) ^ (n + 1) := by
      have hlim : Tendsto
          (fun R : ℝ ↦ ((degree n : ℝ) * tailControl s i) * R⁻¹)
          atTop (𝓝 0) := by
        simpa using ((tendsto_const_nhds : Tendsto
          (fun _ : ℝ ↦ (degree n : ℝ) * tailControl s i) atTop
          (𝓝 ((degree n : ℝ) * tailControl s i))).mul tendsto_inv_atTop_zero)
      simpa only [div_eq_mul_inv] using hlim.eventually
        (Iio_mem_nhds (div_pos (tailBudget_pos i) (by positivity)))
    have hall : ∀ᶠ R : ℝ in atTop, ∀ i : Fin n,
        (degree n : ℝ) * tailControl s i / R <
          tailBudget i / (2 : ℝ) ^ (n + 1) := by
      simpa only [Finset.mem_univ, true_implies] using
        (Finset.eventually_all (Finset.univ : Finset (Fin n))).2 (fun i _ ↦ hi i)
    exact hall.mono fun R h i hi ↦ h ⟨i, hi⟩
  have hlocal : ∀ᶠ R : ℝ in atTop, n ≠ 0 →
      (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
        derivativeMargin n * affineRadius n := by
    by_cases hn : n = 0
    · exact Filter.Eventually.of_forall (fun _ h ↦ (h hn).elim)
    · have hS : 0 < previousDegree n := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact Nat.pos_of_ne_zero (previousDegree_succ_ne_zero q)
      have hC : 0 < ‖leadingCoefficient s n‖ * derivativeMargin n * affineRadius n := by
        positivity [leadingCoefficient_ne_zero_of_valid hs, derivativeMargin_pos n,
          affineRadius_pos n]
      have h := eventually_const_mul_pow_gt (N := (n + 1 : ℝ)) hC hS
      filter_upwards [h] with R hR
      intro _
      convert hR using 1 ; ring
  have hglobal : ∀ᶠ R : ℝ in atTop, n ≠ 0 →
      (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
        derivativeMargin n * globalRadius n := by
    by_cases hn : n = 0
    · exact Filter.Eventually.of_forall (fun _ h ↦ (h hn).elim)
    · have hS : 0 < previousDegree n := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact Nat.pos_of_ne_zero (previousDegree_succ_ne_zero q)
      have hC : 0 < ‖leadingCoefficient s n‖ * derivativeMargin n * globalRadius n := by
        positivity [leadingCoefficient_ne_zero_of_valid hs, derivativeMargin_pos n,
          globalRadius_pos n]
      have h := eventually_const_mul_pow_gt (N := (n + 1 : ℝ)) hC hS
      filter_upwards [h] with R hR
      intro _
      convert hR using 1 ; ring
  have hshell : ∀ᶠ R : ℝ in atTop, n ≠ 0 →
      4 * (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
        escapeMinimum n := by
    by_cases hn : n = 0
    · exact Filter.Eventually.of_forall (fun _ h ↦ (h hn).elim)
    · have hS : 0 < previousDegree n := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact Nat.pos_of_ne_zero (previousDegree_succ_ne_zero q)
      have hC : 0 < ‖leadingCoefficient s n‖ * escapeMinimum n := by
        positivity [leadingCoefficient_ne_zero_of_valid hs, escapeMinimum_pos n]
      have h := eventually_const_mul_pow_gt (N := 4 * (n + 1 : ℝ)) hC hS
      filter_upwards [h] with R hR
      intro _
      convert hR using 1 ; ring
  have hgap : ∀ᶠ R : ℝ in atTop, n ≠ 0 →
      4 * (n + 1 : ℝ) < ‖leadingCoefficient s n‖ * R ^ previousDegree n *
        gapConstant n * insideMinimum (n + 1) := by
    by_cases hn : n = 0
    · exact Filter.Eventually.of_forall (fun _ h ↦ (h hn).elim)
    · have hS : 0 < previousDegree n := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact Nat.pos_of_ne_zero (previousDegree_succ_ne_zero q)
      have hC : 0 < ‖leadingCoefficient s n‖ * gapConstant n * insideMinimum (n + 1) := by
        positivity [leadingCoefficient_ne_zero_of_valid hs, gapConstant_pos n,
          insideMinimum_pos (n + 1)]
      have h := eventually_const_mul_pow_gt (N := 4 * (n + 1 : ℝ)) hC hS
      filter_upwards [h] with R hR
      intro _
      convert hR using 1 ; ring
  exact (hRone.and (hinv.and (hdegree.and (hsep.and (htail.and
    (hlocal.and (hglobal.and (hshell.and hgap)))))))).exists

private noncomputable def chooseRadius (s : RadiusState) (n : ℕ) (hs : StateValid n s) : ℝ :=
  Classical.choose (exists_admissibleRadius s n hs)

private lemma chooseRadius_admissible (s : RadiusState) (n : ℕ) (hs : StateValid n s) :
    RadiusAdmissible s n (chooseRadius s n hs) :=
  Classical.choose_spec (exists_admissibleRadius s n hs)

private noncomputable def constructionState : (n : ℕ) → {s : RadiusState // StateValid n s}
  | 0 => ⟨⟨fun _ ↦ 0, fun _ ↦ 0⟩, by simp [StateValid]⟩
  | n + 1 => by
      let old := constructionState n
      let R := chooseRadius old n old.2
      let next : RadiusState :=
        ⟨Function.update old.1.radius n R,
          Function.update old.1.budget n (tailBudget n)⟩
      refine ⟨next, ?_⟩
      intro i hi
      by_cases hin : i = n
      · subst i
        have hR : 0 < R := lt_trans zero_lt_one (chooseRadius_admissible old n old.2).1
        simpa [next] using hR
      · have hinlt : i < n := by omega
        simpa [next, hin] using old.2 i hinlt

private noncomputable def radius (n : ℕ) : ℝ :=
  (constructionState (n + 1)).1.radius n

private lemma constructionState_radius_stable {i m : ℕ} (him : i < m) :
    (constructionState m).1.radius i = radius i := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases him_eq : i = m
      · subst i
        rfl
      · have himlt : i < m := by omega
        rw [constructionState]
        simpa [Function.update, him_eq] using ih himlt

private lemma radius_eq_chooseRadius (n : ℕ) :
    radius n = chooseRadius (constructionState n) n (constructionState n).2 := by
  simp [radius, constructionState]

private lemma radius_admissible (n : ℕ) :
    RadiusAdmissible (constructionState n) n (radius n) := by
  rw [radius_eq_chooseRadius]
  exact chooseRadius_admissible (constructionState n) n (constructionState n).2

private lemma radius_pos (n : ℕ) : 0 < radius n :=
  lt_trans zero_lt_one (radius_admissible n).1

private lemma radius_tends (n : ℕ) : (n : ℝ) < radius n := by
  induction n with
  | zero => simpa using radius_pos 0
  | succ n ih =>
      have hsep := (radius_admissible (n + 1)).2.2.2.1 n (by omega)
      have hprev : 0 < radius n := radius_pos n
      rw [constructionState_radius_stable (show n < n + 1 by omega), abs_of_pos hprev] at hsep
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith

private lemma previousRoot_constructionState (n : ℕ) (i : PreviousIndex n) :
    previousRoot (constructionState n) n i = radius i.1 * modelRoot i.1 i.2 := by
  rw [previousRoot, constructionState_radius_stable i.1.isLt]

private noncomputable def actualRoot (n : ℕ) (k : Fin (degree n)) : ℂ :=
  radius n * modelRoot n k

private lemma actualRoot_ne_zero (n : ℕ) (k : Fin (degree n)) : actualRoot n k ≠ 0 := by
  exact mul_ne_zero (by exact_mod_cast (radius_pos n).ne') (modelRoot_ne_zero n k)

private lemma norm_actualRoot (n : ℕ) (k : Fin (degree n)) :
    ‖actualRoot n k‖ = radius n * radialScale n (delta n) k := by
  have hr : ‖(radius n : ℂ)‖ = radius n := by
    calc
      ‖(radius n : ℂ)‖ = |radius n| := RCLike.norm_ofReal _
      _ = radius n := abs_of_pos (radius_pos n)
  rw [actualRoot, norm_mul, hr, norm_modelRoot]

private lemma leadingCoefficient_construction_eq (n : ℕ) :
    leadingCoefficient (constructionState n) n =
      ∏ j : Fin n, ∏ k : Fin (degree j), (-actualRoot j k)⁻¹ := by
  rw [leadingCoefficient, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro k _
  rw [previousRoot_constructionState]
  rfl

private lemma leadingCoefficient_succ_eq (n : ℕ) :
    leadingCoefficient (constructionState (n + 1)) (n + 1) =
      leadingCoefficient (constructionState n) n *
        ∏ k : Fin (degree n), (-actualRoot n k)⁻¹ := by
  rw [leadingCoefficient_construction_eq, leadingCoefficient_construction_eq]
  rw [Fin.prod_univ_castSucc]
  rfl

private lemma norm_current_block_leading (n : ℕ) :
    ‖∏ k : Fin (degree n), (-actualRoot n k)⁻¹‖ =
      (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n := by
  rw [norm_prod]
  simp_rw [norm_inv, norm_neg, norm_actualRoot, mul_inv_rev]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, modelLeadingMagnitude, norm_modelRoot]
  rw [Finset.card_univ, Fintype.card_fin, inv_pow]
  ring

private lemma norm_leadingCoefficient_succ (n : ℕ) :
    ‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ =
      ‖leadingCoefficient (constructionState n) n‖ *
        (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n := by
  rw [leadingCoefficient_succ_eq, norm_mul, norm_current_block_leading]
  ring

private lemma current_block_leading_eq (n : ℕ) :
    (∏ k : Fin (degree n), (-actualRoot n k)⁻¹) =
      ((radius n ^ degree n)⁻¹ * modelLeadingMagnitude n : ℝ) *
        (blockLeadingPhase n (phaseData n).rotation : ℂ) := by
  have hfactor (k : Fin (degree n)) :
      (-actualRoot n k)⁻¹ =
        (((radius n * radialScale n (delta n) k)⁻¹ : ℝ) : ℂ) *
          (-((phaseData n).rotation : ℂ) * (rootOfUnity n k : ℂ))⁻¹ := by
    rw [actualRoot, modelRoot, perturbedRoot]
    push_cast
    have hR : (radius n : ℂ) ≠ 0 := by exact_mod_cast (radius_pos n).ne'
    have hs : (radialScale n (delta n) k : ℂ) ≠ 0 := by
      exact_mod_cast (radialScale_pos n k).ne'
    field_simp [hR, hs, Circle.coe_ne_zero (phaseData n).rotation,
      Circle.coe_ne_zero (rootOfUnity n k)]
  calc
    (∏ k : Fin (degree n), (-actualRoot n k)⁻¹) =
        ∏ k : Fin (degree n),
          ((((radius n * radialScale n (delta n) k)⁻¹ : ℝ) : ℂ) *
            (-((phaseData n).rotation : ℂ) * (rootOfUnity n k : ℂ))⁻¹) := by
      apply Finset.prod_congr rfl
      intro k _
      exact hfactor k
    _ = (∏ k : Fin (degree n),
          (((radius n * radialScale n (delta n) k)⁻¹ : ℝ) : ℂ)) *
        (∏ k : Fin (degree n),
          (-((phaseData n).rotation : ℂ) * (rootOfUnity n k : ℂ))⁻¹) := by
      rw [Finset.prod_mul_distrib]
    _ = ((radius n ^ degree n)⁻¹ * modelLeadingMagnitude n : ℝ) *
        (blockLeadingPhase n (phaseData n).rotation : ℂ) := by
      have hmagReal : (∏ k : Fin (degree n),
          (radius n * radialScale n (delta n) k)⁻¹) =
          (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n := by
        simp_rw [mul_inv_rev]
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, modelLeadingMagnitude, norm_modelRoot]
        rw [Finset.card_univ, Fintype.card_fin, inv_pow]
        ring
      have hmag : (∏ k : Fin (degree n),
          (((radius n * radialScale n (delta n) k)⁻¹ : ℝ) : ℂ)) =
          (((radius n ^ degree n)⁻¹ * modelLeadingMagnitude n : ℝ) : ℂ) := by
        exact_mod_cast hmagReal
      have hphase : (∏ k : Fin (degree n),
          (-((phaseData n).rotation : ℂ) * (rootOfUnity n k : ℂ))⁻¹) =
          (blockLeadingPhase n (phaseData n).rotation : ℂ) := by
        rw [blockLeadingPhase]
        let F : Fin (degree n) → Circle := fun k ↦
          (-(phaseData n).rotation * rootOfUnity n k)⁻¹
        have hcircle : (∏ k : Fin (degree n), (F k : ℂ)) =
            ((∏ k : Fin (degree n), F k : Circle) : ℂ) := by
          exact (map_prod Circle.coeHom F (Finset.univ : Finset (Fin (degree n)))).symm
        calc
          (∏ k : Fin (degree n),
              (-((phaseData n).rotation : ℂ) * (rootOfUnity n k : ℂ))⁻¹) =
              ∏ k : Fin (degree n), (F k : ℂ) := by
                apply Finset.prod_congr rfl
                intro k _
                simp [F]
          _ = ((∏ k : Fin (degree n), F k : Circle) : ℂ) := hcircle
      rw [hmag, hphase]

private lemma leadingCoefficient_phase (n : ℕ) :
    leadingCoefficient (constructionState n) n =
      (‖leadingCoefficient (constructionState n) n‖ : ℂ) *
        (phaseData n).leading := by
  induction n with
  | zero => simp [leadingCoefficient, phaseData]
  | succ n ih =>
      have hnorm := norm_leadingCoefficient_succ n
      calc
        leadingCoefficient (constructionState (n + 1)) (n + 1) =
            leadingCoefficient (constructionState n) n *
              ((((radius n ^ degree n)⁻¹ * modelLeadingMagnitude n : ℝ) : ℂ) *
                (blockLeadingPhase n (phaseData n).rotation : ℂ)) := by
          rw [leadingCoefficient_succ_eq, current_block_leading_eq]
        _ =
            ((‖leadingCoefficient (constructionState n) n‖ : ℝ) : ℂ) *
                ((phaseData n).leading : ℂ) *
              ((((radius n ^ degree n)⁻¹ * modelLeadingMagnitude n : ℝ) : ℂ) *
                (blockLeadingPhase n (phaseData n).rotation : ℂ)) := by
          conv_lhs => rw [ih]
        _ = ((‖leadingCoefficient (constructionState n) n‖ *
              (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n : ℝ) : ℂ) *
            (((phaseData n).leading : ℂ) *
              (blockLeadingPhase n (phaseData n).rotation : ℂ)) := by
          push_cast
          ring
        _ = (‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ : ℂ) *
            (phaseData (n + 1)).leading := by
          rw [hnorm, phaseData_leading_succ]
          rfl

private lemma correction_constructionState (n : ℕ) (x : ℝ) (w : ℂ) :
    correction (constructionState n) n x w =
      ∏ i : PreviousIndex n, (1 - (x : ℂ) * actualRoot i.1 i.2 / w) := by
  apply Finset.prod_congr rfl
  intro i _
  rw [previousRoot_constructionState]
  rfl

private lemma radial_phase_identity (n : ℕ) (k : Fin (t (n + 1))) :
    (phaseData (n + 1)).leading *
        (((phaseData (n + 1)).rotation * rootOfUnity (n + 1) (innerIndex (n + 1) k)) ^
          previousDegree (n + 1)) =
      recurrentPhase (n + 1) *
        rootOfUnity (n + 1) (innerIndex (n + 1) k) ^ previousDegree (n + 1) := by
  rw [mul_pow, ← mul_assoc, phase_alignment_succ]

/-! ## The canonical product

The rapid-radius condition makes the sum of the reciprocals of all roots
finite.  Consequently the genus-zero product converges locally uniformly on
the plane and its limit is entire. -/

private abbrev RootIndex := Σ n : ℕ, Fin (degree n)

private noncomputable instance rootIndexDecidableEq : DecidableEq RootIndex := Classical.decEq _

private noncomputable def rootWeight (i : RootIndex) : ℝ := 1 / radius i.1

private lemma one_le_radialScale (n : ℕ) (k : Fin (degree n)) :
    1 ≤ radialScale n (delta n) k := by
  simp only [radialScale]
  split_ifs
  · exact le_rfl
  · exact (one_lt_delta n).le

private lemma radius_le_norm_actualRoot (n : ℕ) (k : Fin (degree n)) :
    radius n ≤ ‖actualRoot n k‖ := by
  rw [norm_actualRoot]
  exact (le_mul_iff_one_le_right (radius_pos n)).2 (one_le_radialScale n k)

private lemma summable_rootWeight : Summable rootWeight := by
  rw [summable_sigma_of_nonneg (fun i ↦ by
    rw [rootWeight]
    positivity [radius_pos i.1])]
  constructor
  · intro n
    apply summable_of_hasFiniteSupport
    exact Set.toFinite _
  · have houter : Summable (fun n : ℕ ↦ (degree n : ℝ) / radius n) :=
      Summable.of_nonneg_of_le (fun n ↦ by positivity [radius_pos n])
        (fun n ↦ (radius_admissible n).2.2.1.le) summable_geometric_two
    convert houter using 1
    funext n
    rw [tsum_fintype]
    simp [rootWeight, div_eq_mul_inv]

private noncomputable def rootTerm (i : RootIndex) (z : ℂ) : ℂ :=
  -z / actualRoot i.1 i.2

private lemma differentiable_rootTerm (i : RootIndex) : Differentiable ℂ (rootTerm i) := by
  unfold rootTerm
  fun_prop

private lemma summable_norm_rootTerm (z : ℂ) :
    Summable (fun i : RootIndex ↦ ‖rootTerm i z‖) := by
  have hmajor : Summable (fun i : RootIndex ↦ ‖z‖ * rootWeight i) :=
    summable_rootWeight.mul_left ‖z‖
  apply hmajor.of_nonneg_of_le (fun i ↦ norm_nonneg _)
  intro i
  rw [rootTerm, norm_div, norm_neg]
  have hden : 0 < ‖actualRoot i.1 i.2‖ := norm_pos_iff.mpr (actualRoot_ne_zero _ _)
  have hr : 0 < radius i.1 := radius_pos i.1
  calc
    ‖z‖ / ‖actualRoot i.1 i.2‖ ≤ ‖z‖ / radius i.1 := by
      exact div_le_div_of_nonneg_left (norm_nonneg z) hr (radius_le_norm_actualRoot _ _)
    _ = ‖z‖ * rootWeight i := by
      change ‖z‖ / radius i.1 = ‖z‖ * (1 / radius i.1)
      rw [div_eq_mul_inv, one_div]

private noncomputable def constructedFunction (z : ℂ) : ℂ :=
  ∏' i : RootIndex, (1 + rootTerm i z)

private lemma canonicalProduct_hasProdLocallyUniformlyOn :
    HasProdLocallyUniformlyOn (fun i z ↦ 1 + rootTerm i z)
      constructedFunction univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hCpos, hC⟩ := hK.isBounded.exists_pos_norm_le
  apply Summable.hasProdUniformlyOn_one_add hK (summable_rootWeight.mul_left C)
  · exact Filter.Eventually.of_forall fun i z hz ↦ by
      rw [rootTerm, norm_div, norm_neg]
      have hden : 0 < ‖actualRoot i.1 i.2‖ := norm_pos_iff.mpr (actualRoot_ne_zero _ _)
      have hr : 0 < radius i.1 := radius_pos i.1
      calc
        ‖z‖ / ‖actualRoot i.1 i.2‖ ≤ C / ‖actualRoot i.1 i.2‖ :=
          div_le_div_of_nonneg_right (hC z hz) hden.le
        _ ≤ C / radius i.1 := by
          exact div_le_div_of_nonneg_left hCpos.le hr (radius_le_norm_actualRoot _ _)
        _ = C * rootWeight i := by
          change C / radius i.1 = C * (1 / radius i.1)
          rw [div_eq_mul_inv, one_div]
  · intro i
    exact (differentiable_rootTerm i).continuous.continuousOn

private lemma differentiable_constructedFunction : Differentiable ℂ constructedFunction := by
  have hfin (s : Finset RootIndex) :
      Differentiable ℂ (fun z ↦ ∏ i ∈ s, (1 + rootTerm i z)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        simp only [Finset.prod_insert his]
        exact ((differentiable_const (c := 1)).add (differentiable_rootTerm i)).mul ih
  rw [← differentiableOn_univ]
  exact canonicalProduct_hasProdLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall fun s ↦ (hfin s).differentiableOn) isOpen_univ

private lemma multipliable_rootFactors (z : ℂ) :
    Multipliable (fun i : RootIndex ↦ 1 + rootTerm i z) :=
  (canonicalProduct_hasProdLocallyUniformlyOn.hasProd (mem_univ z)).multipliable

private lemma rootFactor_eq_modelFactor (n : ℕ) (k : Fin (degree n)) (z : ℂ) :
    1 + rootTerm ⟨n, k⟩ z = 1 - (z / radius n) / modelRoot n k := by
  rw [rootTerm, actualRoot]
  push_cast
  field_simp [show (radius n : ℂ) ≠ 0 by exact_mod_cast (radius_pos n).ne']
  ring

private lemma blockProduct_eq_modelBlock (n : ℕ) (z : ℂ) :
    (∏ k : Fin (degree n), (1 + rootTerm ⟨n, k⟩ z)) =
      modelBlock n (z / radius n) := by
  rw [modelBlock]
  apply Finset.prod_congr rfl
  intro k _
  exact rootFactor_eq_modelFactor n k z

private def previousEmbedding (n : ℕ) : PreviousIndex n ↪ RootIndex :=
  Function.Embedding.sigmaMap Fin.valEmbedding fun _ ↦ Function.Embedding.refl _

private def currentEmbedding (n : ℕ) : Fin (degree n) ↪ RootIndex where
  toFun k := ⟨n, k⟩
  inj' := by
    intro k l h
    exact Fin.ext (by simpa using congrArg (fun i : RootIndex ↦ i.2.val) h)

private noncomputable def previousRootFinset (n : ℕ) : Finset RootIndex :=
  (Finset.univ : Finset (PreviousIndex n)).map (previousEmbedding n)

private noncomputable def currentRootFinset (n : ℕ) : Finset RootIndex :=
  (Finset.univ : Finset (Fin (degree n))).map (currentEmbedding n)

private noncomputable def rootsThrough (n : ℕ) : Finset RootIndex :=
  previousRootFinset n ∪ currentRootFinset n

private lemma mem_previousRootFinset_iff (n : ℕ) (i : RootIndex) :
    i ∈ previousRootFinset n ↔ i.1 < n := by
  constructor
  · intro hi
    rw [previousRootFinset, Finset.mem_map] at hi
    obtain ⟨j, _, hj⟩ := hi
    have hfirst := congrArg Sigma.fst hj
    change (j.1 : ℕ) = i.1 at hfirst
    have hval : (j.1 : ℕ) = i.1 := hfirst
    omega
  · intro hi
    let j : PreviousIndex n := ⟨⟨i.1, hi⟩, i.2⟩
    rw [previousRootFinset, Finset.mem_map]
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Sigma.ext rfl
    exact heq_of_eq rfl

private lemma mem_currentRootFinset_iff (n : ℕ) (i : RootIndex) :
    i ∈ currentRootFinset n ↔ i.1 = n := by
  constructor
  · intro hi
    rw [currentRootFinset, Finset.mem_map] at hi
    obtain ⟨k, _, hk⟩ := hi
    have hfirst := congrArg Sigma.fst hk
    change n = i.1 at hfirst
    exact hfirst.symm
  · intro hi
    subst n
    rw [currentRootFinset, Finset.mem_map]
    refine ⟨i.2, Finset.mem_univ _, ?_⟩
    apply Sigma.ext rfl
    exact heq_of_eq rfl

private lemma mem_rootsThrough_iff (n : ℕ) (i : RootIndex) :
    i ∈ rootsThrough n ↔ i.1 ≤ n := by
  rw [rootsThrough, Finset.mem_union, mem_previousRootFinset_iff,
    mem_currentRootFinset_iff]
  omega

private lemma not_mem_rootsThrough_iff (n : ℕ) (i : RootIndex) :
    i ∉ rootsThrough n ↔ n < i.1 := by
  rw [mem_rootsThrough_iff]
  omega

private lemma previous_current_disjoint (n : ℕ) :
    Disjoint (previousRootFinset n) (currentRootFinset n) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [previousRootFinset, Finset.mem_map] at hx
  rw [currentRootFinset, Finset.mem_map] at hy
  obtain ⟨i, _, rfl⟩ := hx
  obtain ⟨k, _, hk⟩ := hy
  have hfirst := congrArg Sigma.fst hk
  simp only [previousEmbedding, currentEmbedding] at hfirst
  exact (Nat.ne_of_lt i.1.isLt) hfirst.symm

private lemma card_previousIndex (n : ℕ) :
    Fintype.card (PreviousIndex n) = previousDegree n := by
  rw [previousDegree_eq_sum]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun j ↦ degree j) n

private lemma previousProduct_scaled (n : ℕ) (w : ℂ) (hw : w ≠ 0) :
    (∏ i : PreviousIndex n,
        (1 + rootTerm (previousEmbedding n i) ((radius n : ℂ) * w))) =
      leadingCoefficient (constructionState n) n * (radius n : ℂ) ^ previousDegree n *
        w ^ previousDegree n * correction (constructionState n) n (1 / radius n) w := by
  have hR : (radius n : ℂ) ≠ 0 := by exact_mod_cast (radius_pos n).ne'
  have hfactor (i : PreviousIndex n) :
      1 + rootTerm (previousEmbedding n i) ((radius n : ℂ) * w) =
        (-previousRoot (constructionState n) n i)⁻¹ * ((radius n : ℂ) * w) *
          (1 - ((1 / radius n : ℝ) : ℂ) * previousRoot (constructionState n) n i / w) := by
    rw [rootTerm]
    change 1 + -((radius n : ℂ) * w) / actualRoot i.1 i.2 = _
    have hp : actualRoot i.1 i.2 = previousRoot (constructionState n) n i := by
      rw [actualRoot, previousRoot_constructionState]
    rw [hp]
    push_cast
    field_simp [previousRoot_ne_zero_of_valid (constructionState n).2 i, hR, hw]
    ring
  calc
    (∏ i : PreviousIndex n,
        (1 + rootTerm (previousEmbedding n i) ((radius n : ℂ) * w))) =
        ∏ i : PreviousIndex n,
          ((-previousRoot (constructionState n) n i)⁻¹ * ((radius n : ℂ) * w) *
            (1 - ((1 / radius n : ℝ) : ℂ) *
              previousRoot (constructionState n) n i / w)) := by
          apply Finset.prod_congr rfl
          intro i _
          exact hfactor i
    _ = leadingCoefficient (constructionState n) n *
        ((radius n : ℂ) * w) ^ previousDegree n *
          correction (constructionState n) n (1 / radius n) w := by
          rw [leadingCoefficient, correction]
          conv_lhs =>
            enter [2, i]
            rw [mul_assoc]
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          rw [Finset.prod_const]
          rw [show (Finset.univ : Finset (PreviousIndex n)).card = previousDegree n by
            simpa using card_previousIndex n]
          ring
    _ = leadingCoefficient (constructionState n) n * (radius n : ℂ) ^ previousDegree n *
        w ^ previousDegree n * correction (constructionState n) n (1 / radius n) w := by
          rw [mul_pow]
          ring

private lemma product_rootsThrough_scaled (n : ℕ) (w : ℂ) (hw : w ≠ 0) :
    (∏ i ∈ rootsThrough n,
        (1 + rootTerm i ((radius n : ℂ) * w))) =
      leadingCoefficient (constructionState n) n * (radius n : ℂ) ^ previousDegree n *
        normalizedValue (constructionState n) n (1 / radius n) w := by
  rw [rootsThrough, Finset.prod_union (previous_current_disjoint n)]
  rw [previousRootFinset, currentRootFinset]
  simp only [Finset.prod_map]
  rw [previousProduct_scaled n w hw]
  have hcurrent :
      (∏ x : Fin (degree n),
        (1 + rootTerm (currentEmbedding n x) ((radius n : ℂ) * w))) =
          modelBlock n (((radius n : ℂ) * w) / radius n) := by
    rw [modelBlock]
    apply Finset.prod_congr rfl
    intro k _
    exact rootFactor_eq_modelFactor n k ((radius n : ℂ) * w)
  rw [hcurrent]
  have hR : (radius n : ℂ) ≠ 0 := by exact_mod_cast (radius_pos n).ne'
  rw [show (radius n : ℂ) * w / radius n = w by field_simp]
  simp only [normalizedValue]
  ring

private noncomputable def complementaryProduct (s : Finset RootIndex) (z : ℂ) : ℂ :=
  ∏' i : ↑((s : Set RootIndex)ᶜ), (1 + rootTerm i.1 z)

private lemma rootFactors_raw_factorization (s : Finset RootIndex) (z : ℂ) :
    (∏ i ∈ s, (1 + rootTerm i z)) *
        (∏' i : ↑((s : Set RootIndex)ᶜ), (1 + rootTerm i.1 z)) =
      ∏' i : RootIndex, (1 + rootTerm i z) := by
  classical
  have hsNorm : Summable (fun i : (s : Set RootIndex) ↦ ‖rootTerm i.1 z‖) := by
    apply summable_of_hasFiniteSupport
    exact Set.toFinite _
  have hs : Multipliable (fun i : (s : Set RootIndex) ↦ 1 + rootTerm i.1 z) :=
    multipliable_one_add_of_summable hsNorm
  have hscNorm :
      Summable (fun i : ↑((s : Set RootIndex)ᶜ) ↦ ‖rootTerm i.1 z‖) :=
    (summable_norm_rootTerm z).comp_injective Subtype.coe_injective
  have hsc : Multipliable
      (fun i : ↑((s : Set RootIndex)ᶜ) ↦ 1 + rootTerm i.1 z) :=
    multipliable_one_add_of_summable hscNorm
  have hsplit := Multipliable.tprod_mul_tprod_compl
    (f := fun i : RootIndex ↦ 1 + rootTerm i z)
    (s := (s : Set RootIndex)) hs hsc
  rw [← Finset.tprod_subtype' s (fun i : RootIndex ↦ 1 + rootTerm i z)]
  exact hsplit

private noncomputable def futureProduct (n : ℕ) (z : ℂ) : ℂ :=
  complementaryProduct (rootsThrough n) z

private lemma constructedFunction_factorization (n : ℕ) (z : ℂ) :
    (∏ i ∈ rootsThrough n, (1 + rootTerm i z)) * futureProduct n z =
      constructedFunction z := by
  unfold futureProduct complementaryProduct constructedFunction
  exact rootFactors_raw_factorization (rootsThrough n) z

private noncomputable def actualTailControl (n : ℕ) : ℝ :=
  8 * (modelBound n + 1) * radius n + 1

private lemma actualTailControl_pos (n : ℕ) : 0 < actualTailControl n := by
  unfold actualTailControl
  positivity [modelBound_pos n, radius_pos n]

private noncomputable def tailRootMajorant (n : ℕ) (i : RootIndex) : ℝ :=
  if n < i.1 then actualTailControl n / radius i.1 else 0

private noncomputable def tailLevelMajorant (n j : ℕ) : ℝ :=
  if n < j then (degree j : ℝ) * actualTailControl n / radius j else 0

private lemma future_level_bound (n j : ℕ) (hnj : n < j) :
    (degree j : ℝ) * actualTailControl n / radius j <
      tailBudget n / 2 / (2 : ℝ) ^ j := by
  have h := (radius_admissible j).2.2.2.2.1 n hnj
  have hcontrol : tailControl (constructionState j) n = actualTailControl n := by
    rw [tailControl, actualTailControl, constructionState_radius_stable hnj,
      abs_of_pos (radius_pos n)]
  rw [hcontrol] at h
  rw [pow_succ] at h
  convert h using 1 ; ring

private lemma tailFiber_tsum (n j : ℕ) :
    (∑' k : Fin (degree j), tailRootMajorant n ⟨j, k⟩) =
      tailLevelMajorant n j := by
  rw [tsum_fintype]
  by_cases h : n < j
  · simp [tailRootMajorant, tailLevelMajorant, h, div_eq_mul_inv]
    ring
  · simp [tailRootMajorant, tailLevelMajorant, h]

private lemma summable_tailLevelMajorant (n : ℕ) :
    Summable (tailLevelMajorant n) := by
  apply (summable_geometric_two' (tailBudget n)).of_nonneg_of_le
  · intro j
    rw [tailLevelMajorant]
    split_ifs
    · exact div_nonneg
        (mul_nonneg (by positivity) (actualTailControl_pos n).le) (radius_pos j).le
    · exact le_rfl
  · intro j
    by_cases h : n < j
    · simp only [tailLevelMajorant, if_pos h]
      exact (future_level_bound n j h).le
    · simp only [tailLevelMajorant, if_neg h]
      positivity [tailBudget_pos n]

private lemma summable_tailRootMajorant (n : ℕ) :
    Summable (tailRootMajorant n) := by
  rw [summable_sigma_of_nonneg]
  · constructor
    · intro j
      apply summable_of_hasFiniteSupport
      exact Set.toFinite _
    · convert summable_tailLevelMajorant n using 1
      funext j
      exact tailFiber_tsum n j
  · intro i
    rw [tailRootMajorant]
    split_ifs
    · exact div_nonneg (actualTailControl_pos n).le (radius_pos i.1).le
    · exact le_rfl

private lemma tsum_tailRootMajorant_le (n : ℕ) :
    (∑' i : RootIndex, tailRootMajorant n i) ≤ tailBudget n := by
  rw [(summable_tailRootMajorant n).tsum_sigma]
  simp_rw [tailFiber_tsum]
  calc
    (∑' j : ℕ, tailLevelMajorant n j) ≤
        ∑' j : ℕ, tailBudget n / 2 / (2 : ℝ) ^ j := by
      apply Summable.tsum_le_tsum
      · intro j
        by_cases h : n < j
        · simpa only [tailLevelMajorant, if_pos h] using (future_level_bound n j h).le
        · simp only [tailLevelMajorant, if_neg h]
          positivity [tailBudget_pos n]
      · exact summable_tailLevelMajorant n
      · exact summable_geometric_two' (tailBudget n)
    _ = tailBudget n := tsum_geometric_two' (tailBudget n)

private lemma future_norm_sum_le (n : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ actualTailControl n) :
    (∑' i : ↑((rootsThrough n : Set RootIndex)ᶜ), ‖rootTerm i.1 z‖) ≤
      tailBudget n := by
  let e : ↑((rootsThrough n : Set RootIndex)ᶜ) → RootIndex := Subtype.val
  have hmajorSub : Summable
      (fun i : ↑((rootsThrough n : Set RootIndex)ᶜ) ↦ tailRootMajorant n i.1) :=
    (summable_tailRootMajorant n).comp_injective Subtype.coe_injective
  have hnormSub : Summable
      (fun i : ↑((rootsThrough n : Set RootIndex)ᶜ) ↦ ‖rootTerm i.1 z‖) :=
    (summable_norm_rootTerm z).comp_injective Subtype.coe_injective
  calc
    (∑' i : ↑((rootsThrough n : Set RootIndex)ᶜ), ‖rootTerm i.1 z‖) ≤
        ∑' i : ↑((rootsThrough n : Set RootIndex)ᶜ), tailRootMajorant n i.1 := by
      apply Summable.tsum_le_tsum _ hnormSub hmajorSub
      intro i
      have hfuture : n < i.1.1 := (not_mem_rootsThrough_iff n i.1).mp i.2
      rw [rootTerm, norm_div, norm_neg, tailRootMajorant, if_pos hfuture]
      have hr : 0 < radius i.1.1 := radius_pos i.1.1
      calc
        ‖z‖ / ‖actualRoot i.1.1 i.1.2‖ ≤ ‖z‖ / radius i.1.1 := by
          exact div_le_div_of_nonneg_left (norm_nonneg z) hr
            (radius_le_norm_actualRoot _ _)
        _ ≤ actualTailControl n / radius i.1.1 :=
          div_le_div_of_nonneg_right hz hr.le
    _ ≤ ∑' i : RootIndex, tailRootMajorant n i := by
      exact tsum_comp_le_tsum_of_inj (summable_tailRootMajorant n)
        (fun i ↦ by
          rw [tailRootMajorant]
          split_ifs
          · exact div_nonneg (actualTailControl_pos n).le (radius_pos i.1).le
          · exact le_rfl)
        Subtype.coe_injective
    _ ≤ tailBudget n := tsum_tailRootMajorant_le n

private lemma norm_tprod_one_add_sub_one_le_exp_tsum
    {ι : Type*} (u : ι → ℂ) (hu : Summable (fun i ↦ ‖u i‖)) :
    ‖(∏' i, (1 + u i)) - 1‖ ≤ Real.exp (∑' i, ‖u i‖) - 1 := by
  have hp : Tendsto (fun s : Finset ι ↦ ∏ i ∈ s, (1 + u i)) atTop
      (𝓝 (∏' i, (1 + u i))) := (multipliable_one_add_of_summable hu).hasProd
  have hpNorm : Tendsto (fun s : Finset ι ↦ ‖(∏ i ∈ s, (1 + u i)) - 1‖) atTop
      (𝓝 ‖(∏' i, (1 + u i)) - 1‖) :=
    continuous_norm.continuousAt.tendsto.comp (hp.sub_const 1)
  have hsExp : Tendsto (fun s : Finset ι ↦ Real.exp (∑ i ∈ s, ‖u i‖) - 1) atTop
      (𝓝 (Real.exp (∑' i, ‖u i‖) - 1)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp hu.hasSum).sub_const 1
  exact le_of_tendsto_of_tendsto' hpNorm hsExp fun s ↦
    Finset.norm_prod_one_add_sub_one_le s u

private lemma futureProduct_close_to_one (n : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ actualTailControl n) :
    ‖futureProduct n z - 1‖ ≤ tailTolerance n := by
  let u : ↑((rootsThrough n : Set RootIndex)ᶜ) → ℂ := fun i ↦ rootTerm i.1 z
  have hu : Summable (fun i ↦ ‖u i‖) :=
    (summable_norm_rootTerm z).comp_injective Subtype.coe_injective
  unfold futureProduct complementaryProduct
  calc
    ‖(∏' i, (1 + u i)) - 1‖ ≤ Real.exp (∑' i, ‖u i‖) - 1 :=
      norm_tprod_one_add_sub_one_le_exp_tsum u hu
    _ ≤ Real.exp (tailBudget n) - 1 := by
      exact sub_le_sub_right (Real.exp_le_exp.mpr (future_norm_sum_le n z hz)) 1
    _ = tailTolerance n := by
      rw [tailBudget, Real.exp_log (by positivity [tailTolerance_pos n])]
      ring

private lemma futureProduct_hasProdLocallyUniformlyOn (n : ℕ) :
    HasProdLocallyUniformlyOn
      (fun i : ↑((rootsThrough n : Set RootIndex)ᶜ) ↦ fun z ↦ 1 + rootTerm i.1 z)
      (futureProduct n) univ := by
  unfold futureProduct complementaryProduct
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hCpos, hC⟩ := hK.isBounded.exists_pos_norm_le
  have hw : Summable
      (fun i : ↑((rootsThrough n : Set RootIndex)ᶜ) ↦ C * rootWeight i.1) :=
    (summable_rootWeight.comp_injective Subtype.coe_injective).mul_left C
  apply Summable.hasProdUniformlyOn_one_add hK hw
  · exact Filter.Eventually.of_forall fun i z hz ↦ by
      rw [rootTerm, norm_div, norm_neg]
      have hden : 0 < ‖actualRoot i.1.1 i.1.2‖ :=
        norm_pos_iff.mpr (actualRoot_ne_zero _ _)
      have hr : 0 < radius i.1.1 := radius_pos i.1.1
      calc
        ‖z‖ / ‖actualRoot i.1.1 i.1.2‖ ≤ C / ‖actualRoot i.1.1 i.1.2‖ :=
          div_le_div_of_nonneg_right (hC z hz) hden.le
        _ ≤ C / radius i.1.1 := by
          exact div_le_div_of_nonneg_left hCpos.le hr (radius_le_norm_actualRoot _ _)
        _ = C * rootWeight i.1 := by
          change C / radius i.1.1 = C * (1 / radius i.1.1)
          rw [div_eq_mul_inv, one_div]
  · intro i
    exact (differentiable_rootTerm i.1).continuous.continuousOn

private lemma differentiable_futureProduct (n : ℕ) : Differentiable ℂ (futureProduct n) := by
  have hfin (s : Finset ↑((rootsThrough n : Set RootIndex)ᶜ)) :
      Differentiable ℂ (fun z ↦ ∏ i ∈ s, (1 + rootTerm i.1 z)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        simp only [Finset.prod_insert his]
        exact ((differentiable_const (c := 1)).add (differentiable_rootTerm i.1)).mul ih
  rw [← differentiableOn_univ]
  exact (futureProduct_hasProdLocallyUniformlyOn n).differentiableOn
    (Filter.Eventually.of_forall fun s ↦ (hfin s).differentiableOn) isOpen_univ

private lemma futureProduct_deriv_bound (n : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ 3 * radius n) :
    ‖deriv (futureProduct n) z‖ ≤
      tailTolerance n / (4 * (modelBound n + 1) * radius n) := by
  let g : ℂ → ℂ := fun y ↦ futureProduct n y - 1
  have hg : Differentiable ℂ g := (differentiable_futureProduct n).sub
    (differentiable_const (c := 1))
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := z) (R := 4 * (modelBound n + 1) * radius n) (C := tailTolerance n)
    (by positivity [modelBound_pos n, radius_pos n]) hg.diffContOnCl (fun y hy ↦ ?_)
  · simpa [g, deriv_sub_const] using hCauchy
  · apply futureProduct_close_to_one n y
    have hsphere : ‖z - y‖ = 4 * (modelBound n + 1) * radius n := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using mem_sphere.mp hy
    calc
      ‖y‖ ≤ ‖z‖ + ‖z - y‖ := norm_le_norm_add_norm_sub z y
      _ ≤ 3 * radius n + 4 * (modelBound n + 1) * radius n :=
        add_le_add hz hsphere.le
      _ ≤ actualTailControl n := by
        rw [actualTailControl]
        nlinarith [modelBound_pos n, radius_pos n]

private lemma deriv_correction (s : RadiusState) (n : ℕ) (x : ℝ) (w : ℂ)
    (hw : w ≠ 0) :
    deriv (correction s n x) w = correctionDerivative s n x w := by
  let fac : PreviousIndex n → ℂ → ℂ := fun i y ↦
    1 - (x : ℂ) * previousRoot s n i / y
  have hfac (i : PreviousIndex n) :
      HasDerivAt (fac i) ((x : ℂ) * previousRoot s n i / w ^ 2) w := by
    have hdiff : DifferentiableAt ℂ (fac i) w := by
      dsimp only [fac]
      fun_prop
    have hquot := (hasDerivAt_const w ((x : ℂ) * previousRoot s n i)).div
      (hasDerivAt_id w) hw
    have hsub := (hasDerivAt_const w (1 : ℂ)).sub hquot
    have hcoef :
        0 - (0 * id w - (x : ℂ) * previousRoot s n i * 1) / id w ^ 2 =
          (x : ℂ) * previousRoot s n i / w ^ 2 := by
      simp only [id_eq, zero_mul, zero_sub]
      ring
    have hderiv : deriv (fac i) w = (x : ℂ) * previousRoot s n i / w ^ 2 := by
      rw [show fac i = (fun y : ℂ ↦ 1 - (x : ℂ) * previousRoot s n i / y) by rfl]
      have heq := hsub.deriv
      rw [hcoef] at heq
      exact heq
    have hf := hdiff.hasDerivAt
    rwa [hderiv] at hf
  have hp := HasDerivAt.fun_finsetProd
    (u := (Finset.univ : Finset (PreviousIndex n)))
    (f := fac) (fun i _ ↦ hfac i)
  unfold correction correctionDerivative
  simpa only [fac, Finset.mem_univ, smul_eq_mul, mul_comm] using hp.deriv

private lemma deriv_normalizedValue (s : RadiusState) (n : ℕ) (x : ℝ) (w : ℂ)
    (hw : w ≠ 0) :
    deriv (normalizedValue s n x) w = normalizedDerivative s n x w := by
  have hcorrDiff : DifferentiableAt ℂ (correction s n x) w := by
    unfold correction
    fun_prop
  have hcorr := hcorrDiff.hasDerivAt
  rw [deriv_correction s n x w hw] at hcorr
  have hblock : HasDerivAt (modelBlock n) (deriv (modelBlock n) w) w :=
    ((modelBlock_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt
  have hpow := (hasDerivAt_id w).pow (previousDegree n)
  have hprod := (hpow.mul hcorr).mul hblock
  have hfun : id ^ previousDegree n * correction s n x * modelBlock n =
      normalizedValue s n x := by
    funext y
    simp [normalizedValue]
  rw [← hfun, hprod.deriv]
  unfold normalizedDerivative
  simp [id_eq]
  ring

private noncomputable def stageFunction (n : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ rootsThrough n, (1 + rootTerm i z)

private lemma differentiable_stageFunction (n : ℕ) : Differentiable ℂ (stageFunction n) := by
  have hfin (s : Finset RootIndex) :
      Differentiable ℂ (fun z ↦ ∏ i ∈ s, (1 + rootTerm i z)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        simp only [Finset.prod_insert his]
        exact ((differentiable_const (c := 1)).add (differentiable_rootTerm i)).mul ih
  exact hfin (rootsThrough n)

private lemma stageFunction_scaled (n : ℕ) (w : ℂ) (hw : w ≠ 0) :
    stageFunction n ((radius n : ℂ) * w) =
      leadingCoefficient (constructionState n) n * (radius n : ℂ) ^ previousDegree n *
        normalizedValue (constructionState n) n (1 / radius n) w :=
  product_rootsThrough_scaled n w hw

private lemma previousDegree_ne_zero_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    previousDegree n ≠ 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact previousDegree_succ_ne_zero q

private lemma deriv_stageFunction_scaled (n : ℕ) (hn : n ≠ 0) (w : ℂ) (hw : w ≠ 0) :
    deriv (stageFunction n) ((radius n : ℂ) * w) =
      leadingCoefficient (constructionState n) n *
        (radius n : ℂ) ^ (previousDegree n - 1) *
          normalizedDerivative (constructionState n) n (1 / radius n) w := by
  let A : ℂ := leadingCoefficient (constructionState n) n
  let R : ℂ := radius n
  let N : ℕ := previousDegree n
  have hR : R ≠ 0 := by
    change (radius n : ℂ) ≠ 0
    exact_mod_cast (radius_pos n).ne'
  have hEq :
      (fun u : ℂ ↦ stageFunction n (R * u)) =ᶠ[𝓝 w]
        (fun u : ℂ ↦ A * R ^ N *
          normalizedValue (constructionState n) n (1 / radius n) u) := by
    filter_upwards [eventually_ne_nhds hw] with u hu
    exact stageFunction_scaled n u hu
  have hleft : HasDerivAt (fun u : ℂ ↦ stageFunction n (R * u))
      (deriv (stageFunction n) (R * w) * R) w :=
    ((differentiable_stageFunction n (R * w)).hasDerivAt).comp w
      (hasDerivAt_const_mul R)
  let raw : ℂ → ℂ := fun y ↦
    y ^ previousDegree n * correction (constructionState n) n (1 / radius n) y *
      modelBlock n y
  have hrawDiff : DifferentiableAt ℂ raw w := by
    have hc : DifferentiableAt ℂ
        (correction (constructionState n) n (1 / radius n)) w := by
      unfold correction
      fun_prop
    have hb : DifferentiableAt ℂ (modelBlock n) w :=
      ((modelBlock_contDiff n).differentiable (by simp)).differentiableAt
    exact ((differentiableAt_id.pow _).mul hc).mul hb
  have hnorm0 := hrawDiff.hasDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ show
      normalizedValue (constructionState n) n (1 / radius n) y = raw y by rfl)
  have hcoef := hnorm0.deriv
  rw [deriv_normalizedValue (constructionState n) n (1 / radius n) w hw] at hcoef
  have hnorm := hnorm0.congr_deriv hcoef.symm
  have hright : HasDerivAt
      (fun u : ℂ ↦ A * R ^ N * normalizedValue (constructionState n) n (1 / radius n) u)
      (A * R ^ N * normalizedDerivative (constructionState n) n (1 / radius n) w) w := by
    exact hnorm.const_mul (A * R ^ N)
  have heqDeriv :
      A * R ^ N * normalizedDerivative (constructionState n) n (1 / radius n) w =
        deriv (stageFunction n) (R * w) * R :=
    hright.unique (hleft.congr_of_eventuallyEq hEq.symm)
  have hN : N ≠ 0 := previousDegree_ne_zero_of_ne_zero n hn
  change deriv (stageFunction n) (R * w) = A * R ^ (N - 1) *
    normalizedDerivative (constructionState n) n (1 / radius n) w
  apply (mul_right_cancel₀ hR)
  rw [← heqDeriv]
  rw [← pow_sub_one_mul hN]
  ring

private lemma localModelSet_norm_lt_three (n : ℕ) {w : ℂ}
    (hw : w ∈ localModelSet n) : ‖w‖ < 3 := by
  obtain ⟨k, hk⟩ := (mem_localModelSet_iff n w).mp hw
  have hdist : ‖modelRoot n (innerIndex n k) - w‖ ≤ affineRadius n := by
    rw [← dist_eq_norm, dist_comm]
    exact mem_closedBall.mp hk
  have hroot : ‖modelRoot n (innerIndex n k)‖ = 1 := norm_modelRoot_inner n k
  have haff : affineRadius n < 1 / 4 :=
    (affineRadius_lt_localRadius n).trans
      ((localRadius_lt_modelRadius n).trans (modelRadius_lt_quarter n))
  calc
    ‖w‖ ≤ ‖modelRoot n (innerIndex n k)‖ +
        ‖modelRoot n (innerIndex n k) - w‖ := norm_le_norm_add_norm_sub _ _
    _ ≤ 1 + affineRadius n := by rw [hroot]; gcongr
    _ < 3 := by linarith

private lemma globalModelSet_norm_lt_three (n : ℕ) {w : ℂ}
    (hw : w ∈ globalModelSet n) : ‖w‖ < 3 := by
  obtain ⟨k, hk⟩ := (mem_globalModelSet_iff n w).mp hw
  have hdist : ‖modelRoot n k - w‖ ≤ globalRadius n := by
    rw [← dist_eq_norm, dist_comm]
    exact mem_closedBall.mp hk
  have hroot : ‖modelRoot n k‖ < 2 := by
    rw [norm_modelRoot]
    simp only [radialScale]
    split_ifs
    · exact one_lt_two
    · exact delta_lt_two n
  have hradius : globalRadius n < 1 / 4 :=
    (globalRadius_lt_affineRadius n).trans
      ((affineRadius_lt_localRadius n).trans
        ((localRadius_lt_modelRadius n).trans (modelRadius_lt_quarter n)))
  calc
    ‖w‖ ≤ ‖modelRoot n k‖ + ‖modelRoot n k - w‖ :=
      norm_le_norm_add_norm_sub _ _
    _ ≤ ‖modelRoot n k‖ + globalRadius n := by gcongr
    _ < 3 := by linarith

private lemma extendedModelSet_norm_lt_three (n : ℕ) {w : ℂ}
    (hw : w ∈ extendedModelSet n) : ‖w‖ < 3 := by
  rcases hw with hw | hw
  · exact localModelSet_norm_lt_three n hw
  · exact globalModelSet_norm_lt_three n hw

private lemma deriv_constructedFunction_scaled (n : ℕ) (hn : n ≠ 0) (w : ℂ) (hw : w ≠ 0) :
    deriv constructedFunction ((radius n : ℂ) * w) =
      (leadingCoefficient (constructionState n) n *
        (radius n : ℂ) ^ (previousDegree n - 1)) *
      (normalizedDerivative (constructionState n) n (1 / radius n) w *
          futureProduct n ((radius n : ℂ) * w) +
        (radius n : ℂ) * normalizedValue (constructionState n) n (1 / radius n) w *
          deriv (futureProduct n) ((radius n : ℂ) * w)) := by
  have hfun : (fun z ↦ stageFunction n z * futureProduct n z) = constructedFunction := by
    funext z
    exact constructedFunction_factorization n z
  rw [← hfun]
  change deriv (stageFunction n * futureProduct n) ((radius n : ℂ) * w) = _
  rw [deriv_mul (differentiable_stageFunction n ((radius n : ℂ) * w))
    (differentiable_futureProduct n ((radius n : ℂ) * w))]
  rw [deriv_stageFunction_scaled n hn w hw, stageFunction_scaled n w hw]
  have hS : previousDegree n ≠ 0 := previousDegree_ne_zero_of_ne_zero n hn
  rw [← pow_sub_one_mul hS]
  ring

private noncomputable def fullNormalizedDerivative (n : ℕ) (w : ℂ) : ℂ :=
  normalizedDerivative (constructionState n) n (1 / radius n) w *
      futureProduct n ((radius n : ℂ) * w) +
    (radius n : ℂ) * normalizedValue (constructionState n) n (1 / radius n) w *
      deriv (futureProduct n) ((radius n : ℂ) * w)

private lemma deriv_constructedFunction_eq_scale_mul (n : ℕ) (hn : n ≠ 0) (w : ℂ)
    (hw : w ≠ 0) :
    deriv constructedFunction ((radius n : ℂ) * w) =
      (leadingCoefficient (constructionState n) n *
        (radius n : ℂ) ^ (previousDegree n - 1)) * fullNormalizedDerivative n w := by
  exact deriv_constructedFunction_scaled n hn w hw

private lemma fullNormalizedDerivative_tail_close (n : ℕ) {w : ℂ}
    (hw : w ∈ extendedModelSet n) :
    ‖fullNormalizedDerivative n w -
      normalizedDerivative (constructionState n) n (1 / radius n) w‖ <
        derivativeMargin n := by
  let ND := normalizedDerivative (constructionState n) n (1 / radius n) w
  let LD := limitingDerivative n w
  let NV := normalizedValue (constructionState n) n (1 / radius n) w
  let LV := limitingValue n w
  let P := futureProduct n ((radius n : ℂ) * w)
  let DP := deriv (futureProduct n) ((radius n : ℂ) * w)
  let B := modelBound n
  let ε := tailTolerance n
  let R := radius n
  have hx : |1 / radius n| < uniformScaleBound (constructionState n) n := by
    rw [abs_of_pos (by positivity [radius_pos n] : 0 < 1 / radius n)]
    exact (radius_admissible n).2.1
  have hNDclose : ‖ND - LD‖ < derivativeMargin n :=
    normalizedDerivative_scale_close (constructionState n) n hx hw
  have hNVclose : ‖NV - LV‖ < 1 :=
    normalizedValue_scale_close (constructionState n) n hx hw
  have hLD : ‖LD‖ < B := norm_limitingDerivative_lt_modelBound n hw
  have hLV : ‖LV‖ < B := norm_limitingValue_lt_modelBound n hw
  have hmarginB : derivativeMargin n < B := derivativeMargin_lt_modelBound n
  have hND : ‖ND‖ < 2 * B := by
    calc
      ‖ND‖ = ‖(ND - LD) + LD‖ := by rw [sub_add_cancel]
      _ ≤ ‖ND - LD‖ + ‖LD‖ := norm_add_le _ _
      _ < 2 * B := by linarith
  have hNV : ‖NV‖ < B + 1 := by
    calc
      ‖NV‖ = ‖(NV - LV) + LV‖ := by rw [sub_add_cancel]
      _ ≤ ‖NV - LV‖ + ‖LV‖ := norm_add_le _ _
      _ < B + 1 := by linarith
  have hwNorm : ‖w‖ < 3 := extendedModelSet_norm_lt_three n hw
  have hzNorm : ‖(radius n : ℂ) * w‖ ≤ 3 * radius n := by
    have hnormR : ‖(radius n : ℂ)‖ = radius n := by
      calc
        ‖(radius n : ℂ)‖ = |radius n| := RCLike.norm_ofReal _
        _ = radius n := abs_of_pos (radius_pos n)
    rw [norm_mul, hnormR]
    nlinarith [radius_pos n]
  have hP : ‖P - 1‖ ≤ ε := by
    apply futureProduct_close_to_one n
    exact hzNorm.trans (by
      rw [actualTailControl]
      nlinarith [modelBound_pos n, radius_pos n])
  have hDP : ‖DP‖ ≤ ε / (4 * (B + 1) * R) :=
    futureProduct_deriv_bound n ((radius n : ℂ) * w) hzNorm
  have hterm₁ : ‖ND * (P - 1)‖ ≤ 2 * B * ε := by
    rw [norm_mul]
    exact mul_le_mul hND.le hP (norm_nonneg _) (by positivity [modelBound_pos n])
  have hden : 0 < 4 * (B + 1) * R := by
    positivity [modelBound_pos n, radius_pos n]
  have hR0 : R ≠ 0 := by exact (radius_pos n).ne'
  have hB0 : B + 1 ≠ 0 := by
    have : 0 < B + 1 := by dsimp only [B]; positivity [modelBound_pos n]
    exact this.ne'
  have hterm₂ : ‖(R : ℂ) * NV * DP‖ ≤ ε := by
    calc
      ‖(R : ℂ) * NV * DP‖ = R * ‖NV‖ * ‖DP‖ := by
        have hnormR : ‖(R : ℂ)‖ = R := by
          dsimp only [R]
          calc
            ‖(radius n : ℂ)‖ = |radius n| := RCLike.norm_ofReal _
            _ = radius n := abs_of_pos (radius_pos n)
        rw [norm_mul, norm_mul, hnormR]
      _ ≤ R * (B + 1) * (ε / (4 * (B + 1) * R)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hNV.le (radius_pos n).le
        · exact hDP
        · exact norm_nonneg _
        · exact mul_nonneg (radius_pos n).le (by
            dsimp only [B]
            positivity [modelBound_pos n])
      _ = ε / 4 := by field_simp [hR0, hB0]
      _ ≤ ε := by linarith [tailTolerance_pos n]
  have hrewrite : fullNormalizedDerivative n w - ND =
      ND * (P - 1) + (R : ℂ) * NV * DP := by
    simp only [fullNormalizedDerivative, ND, NV, P, DP, R]
    ring
  rw [hrewrite]
  calc
    ‖ND * (P - 1) + (R : ℂ) * NV * DP‖ ≤
        ‖ND * (P - 1)‖ + ‖(R : ℂ) * NV * DP‖ := norm_add_le _ _
    _ ≤ 2 * B * ε + ε := add_le_add hterm₁ hterm₂
    _ < ε * (2 * B + 3) := by nlinarith [tailTolerance_pos n]
    _ < derivativeMargin n := tailTolerance_mul_bound n

private lemma fullNormalizedDerivative_close_ideal (n : ℕ) (k : Fin (t n)) {w : ℂ}
    (hw : w ∈ closedBall (modelRoot n (innerIndex n k)) (affineRadius n)) :
    ‖fullNormalizedDerivative n w + idealSlope n k‖ <
      ‖idealSlope n k‖ / (2 * (n + 2)) := by
  have hwLocal : w ∈ localModelSet n :=
    (mem_localModelSet_iff n w).mpr ⟨k, hw⟩
  have hwExt := localModelSet_subset_extended n hwLocal
  have htail := fullNormalizedDerivative_tail_close n hwExt
  have hx : |1 / radius n| < uniformScaleBound (constructionState n) n := by
    rw [abs_of_pos (by positivity [radius_pos n] : 0 < 1 / radius n)]
    exact (radius_admissible n).2.1
  have hscale := normalizedDerivative_scale_close (constructionState n) n hx hwExt
  have hlimit := limitingDerivative_close n k hw
  have hmargin := derivativeMargin_lt n k
  have hrewrite : fullNormalizedDerivative n w + idealSlope n k =
      (fullNormalizedDerivative n w -
          normalizedDerivative (constructionState n) n (1 / radius n) w) +
        (normalizedDerivative (constructionState n) n (1 / radius n) w -
          limitingDerivative n w) +
        (limitingDerivative n w + idealSlope n k) := by ring
  rw [hrewrite]
  calc
    ‖(fullNormalizedDerivative n w -
          normalizedDerivative (constructionState n) n (1 / radius n) w) +
        (normalizedDerivative (constructionState n) n (1 / radius n) w -
          limitingDerivative n w) +
        (limitingDerivative n w + idealSlope n k)‖ ≤
      ‖fullNormalizedDerivative n w -
          normalizedDerivative (constructionState n) n (1 / radius n) w‖ +
        ‖normalizedDerivative (constructionState n) n (1 / radius n) w -
          limitingDerivative n w‖ +
        ‖limitingDerivative n w + idealSlope n k‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ < derivativeMargin n + derivativeMargin n +
        ‖idealSlope n k‖ / (8 * (n + 2)) := by
      exact add_lt_add (add_lt_add htail hscale) hlimit
    _ < ‖idealSlope n k‖ / (2 * (n + 2)) := by
      have hpiece : 0 < ‖idealSlope n k‖ / (8 * (n + 2)) := by
        positivity [idealSlope_ne_zero n k]
      have htarget : ‖idealSlope n k‖ / (2 * (n + 2)) =
          4 * (‖idealSlope n k‖ / (8 * (n + 2))) := by
        field_simp ; ring
      rw [htarget]
      linarith

/-! ## A quantitative local inverse lemma

This is the Banach fixed-point replacement for Rouché's theorem.  It is
stated for an arbitrary entire function so that the later canonical-product
estimates only have to supply a derivative bound. -/

private lemma quantitative_local_inverse
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c C a : ℂ) (d : ℝ) (q : NNReal)
    (hd : 0 < d) (hq : q < 1) (hC : C ≠ 0) (hfc : f c = 0)
    (hderiv : ∀ z ∈ closedBall c d, ‖deriv f z + C‖ ≤ (q : ℝ) * ‖C‖)
    (ha : ‖a / C‖ ≤ (1 - (q : ℝ)) * d) :
    ∃! z : ℂ, z ∈ closedBall c d ∧ f z = a := by
  let T : ℂ → ℂ := fun z ↦ z + (f z - a) / C
  have hT_hasDeriv (z : ℂ) : HasDerivAt T ((deriv f z + C) / C) z := by
    have hbase := (hasDerivAt_id z).add (((hf z).hasDerivAt.sub_const a).div_const C)
    have h' : HasDerivAt T (1 + deriv f z / C) z :=
      hbase.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ by simp [T])
    simpa [add_div, div_self hC, add_comm] using h'
  have hTdiff (z : ℂ) : DifferentiableAt ℂ T z := (hT_hasDeriv z).differentiableAt
  have hTderiv (z : ℂ) : deriv T z = (deriv f z + C) / C := (hT_hasDeriv z).deriv
  have hLip : LipschitzOnWith q T (closedBall c d) := by
    apply (convex_closedBall c d).lipschitzOnWith_of_nnnorm_deriv_le
    · exact fun z _ ↦ hTdiff z
    · intro z hz
      rw [hTderiv, nnnorm_div]
      apply (div_le_iff₀ (nnnorm_pos.2 hC)).2
      exact_mod_cast hderiv z hz
  have hTc : T c = c - a / C := by simp [T, hfc]; ring
  have hmap : MapsTo T (closedBall c d) (closedBall c d) := by
    intro z hz
    rw [mem_closedBall]
    calc
      dist (T z) c ≤ dist (T z) (T c) + dist (T c) c := dist_triangle _ _ _
      _ ≤ (q : ℝ) * dist z c + dist (T c) c := by
        gcongr
        exact hLip.dist_le_mul z hz c (mem_closedBall_self hd.le)
      _ ≤ (q : ℝ) * d + ‖a / C‖ := by
        have hdist : dist (c - a / C) c = ‖a / C‖ := by
          rw [dist_eq_norm]
          rw [show c - a / C - c = -(a / C) by ring, norm_neg]
        rw [hTc, hdist]
        gcongr
        exact mem_closedBall.mp hz
      _ ≤ d := by linarith
  have hcontract : ContractingWith q
      (hmap.restrict T (closedBall c d) (closedBall c d)) := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul (fun x y ↦ ?_)⟩
    exact hLip.dist_le_mul x x.2 y y.2
  obtain ⟨z, hz, hfixed, -⟩ := hcontract.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmap (mem_closedBall_self hd.le) (edist_ne_top _ _)
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · have h := hfixed
    simp only [IsFixedPt, T] at h
    have hdiv : (f z - a) / C = 0 := by linear_combination h
    exact sub_eq_zero.mp ((div_eq_zero_iff).mp hdiv |>.resolve_right hC)
  · rintro y ⟨hy, hfy⟩
    have hTy : T y = y := by simp [T, hfy]
    have hdist := hLip.dist_le_mul y hy z hz
    rw [hTy, hfixed.eq] at hdist
    have hq' : (q : ℝ) < 1 := by exact_mod_cast hq
    have hzero : dist y z = 0 := by
      have hnonneg : 0 ≤ dist y z := dist_nonneg
      nlinarith
    exact dist_eq_zero.mp hzero

/-! ## The distinguished local inverse branches -/

private noncomputable def scaledFunction (n : ℕ) (w : ℂ) : ℂ :=
  constructedFunction ((radius n : ℂ) * w)

private lemma differentiable_scaledFunction (n : ℕ) : Differentiable ℂ (scaledFunction n) := by
  exact differentiable_constructedFunction.fun_comp
    ((differentiable_const (c := (radius n : ℂ))).mul differentiable_id)

private noncomputable def activeSlope (n : ℕ) (k : Fin (t n)) : ℂ :=
  leadingCoefficient (constructionState n) n * (radius n : ℂ) ^ previousDegree n *
    idealSlope n k

private lemma activeSlope_ne_zero (n : ℕ) (k : Fin (t n)) : activeSlope n k ≠ 0 := by
  unfold activeSlope
  exact mul_ne_zero
    (mul_ne_zero (leadingCoefficient_ne_zero_of_valid (constructionState n).2)
      (pow_ne_zero _ (by exact_mod_cast (radius_pos n).ne')))
    (idealSlope_ne_zero n k)

private lemma norm_activeSlope (n : ℕ) (k : Fin (t n)) :
    ‖activeSlope n k‖ =
      ‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n *
        ‖idealSlope n k‖ := by
  have hR : ‖(radius n : ℂ)‖ = radius n := by
    calc
      ‖(radius n : ℂ)‖ = |radius n| := RCLike.norm_ofReal _
      _ = radius n := abs_of_pos (radius_pos n)
  simp only [activeSlope, norm_mul, norm_pow, hR]

private lemma scaledFunction_zero (n : ℕ) (k : Fin (t n)) :
    scaledFunction n (modelRoot n (innerIndex n k)) = 0 := by
  let w := modelRoot n (innerIndex n k)
  have hw : w ≠ 0 := modelRoot_ne_zero n (innerIndex n k)
  have hstage : stageFunction n ((radius n : ℂ) * w) = 0 := by
    rw [stageFunction_scaled n w hw]
    unfold normalizedValue
    rw [modelBlock_zero n (innerIndex n k)]
    ring
  change constructedFunction ((radius n : ℂ) * w) = 0
  calc
    constructedFunction ((radius n : ℂ) * w) =
        stageFunction n ((radius n : ℂ) * w) *
          futureProduct n ((radius n : ℂ) * w) :=
      (constructedFunction_factorization n _).symm
    _ = 0 := by rw [hstage, zero_mul]

private lemma deriv_scaledFunction (n : ℕ) (hn : n ≠ 0) {w : ℂ}
    (hw : w ∈ extendedModelSet n) :
    deriv (scaledFunction n) w =
      leadingCoefficient (constructionState n) n * (radius n : ℂ) ^ previousDegree n *
        fullNormalizedDerivative n w := by
  have hw0 : w ≠ 0 := extendedModelSet_nonzero n hw
  change deriv (fun u ↦ constructedFunction ((radius n : ℂ) * u)) w = _
  rw [deriv_comp_mul_left]
  rw [deriv_constructedFunction_eq_scale_mul n hn w hw0]
  have hS := previousDegree_ne_zero_of_ne_zero n hn
  rw [← pow_sub_one_mul hS]
  ring

private noncomputable def localError (n : ℕ) : NNReal :=
  ⟨1 / (2 * ((n : ℝ) + 2)), by positivity⟩

@[simp] private lemma localError_coe (n : ℕ) :
    (localError n : ℝ) = 1 / (2 * ((n : ℝ) + 2)) := rfl

private lemma localError_lt_one (n : ℕ) : localError n < 1 := by
  rw [← NNReal.coe_lt_coe]
  simp only [localError_coe, NNReal.coe_one]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact (div_lt_one (by linarith : 0 < 2 * ((n : ℝ) + 2))).2 (by linarith)

private lemma scaledFunction_deriv_close (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    {w : ℂ} (hw : w ∈ closedBall (modelRoot n (innerIndex n k)) (affineRadius n)) :
    ‖deriv (scaledFunction n) w + activeSlope n k‖ <
      (localError n : ℝ) * ‖activeSlope n k‖ := by
  let A : ℂ := leadingCoefficient (constructionState n) n *
    (radius n : ℂ) ^ previousDegree n
  have hwLocal : w ∈ localModelSet n := (mem_localModelSet_iff n w).mpr ⟨k, hw⟩
  rw [deriv_scaledFunction n hn (localModelSet_subset_extended n hwLocal)]
  change ‖A * fullNormalizedDerivative n w + A * idealSlope n k‖ <
    (localError n : ℝ) * ‖A * idealSlope n k‖
  rw [← mul_add, localError_coe]
  rw [norm_mul A (fullNormalizedDerivative n w + idealSlope n k),
    norm_mul A (idealSlope n k)]
  have hA : 0 < ‖A‖ := norm_pos_iff.mpr (mul_ne_zero
    (leadingCoefficient_ne_zero_of_valid (constructionState n).2)
    (pow_ne_zero _ (by exact_mod_cast (radius_pos n).ne')))
  have hclose := fullNormalizedDerivative_close_ideal n k hw
  calc
    ‖A‖ * ‖fullNormalizedDerivative n w + idealSlope n k‖ <
        ‖A‖ * (‖idealSlope n k‖ / (2 * ((n : ℝ) + 2))) :=
      mul_lt_mul_of_pos_left hclose hA
    _ = 1 / (2 * ((n : ℝ) + 2)) * (‖A‖ * ‖idealSlope n k‖) := by ring

private lemma local_target_admissible (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    ‖a / activeSlope n k‖ ≤
      (1 - (localError n : ℝ)) * affineRadius n := by
  let X : ℝ := ‖leadingCoefficient (constructionState n) n‖ *
    radius n ^ previousDegree n
  let I : ℝ := ‖idealSlope n k‖
  let d : ℝ := affineRadius n
  let x : ℝ := (n : ℝ) + 2
  have hX : 0 < X := by
    dsimp only [X]
    positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2, radius_pos n]
  have hI : 0 < I := by
    dsimp only [I]
    positivity [idealSlope_ne_zero n k]
  have hd : 0 < d := by exact affineRadius_pos n
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hcapacity := (radius_admissible n).2.2.2.2.2.1 hn
  have hmargin := derivativeMargin_lt n k
  have hstrong : (n + 1 : ℝ) < X * (I / (8 * x)) * d := by
    apply hcapacity.trans
    dsimp only [X, I, d, x] at hmargin ⊢
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hmargin (by
      positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2,
        radius_pos n])) (affineRadius_pos n)
  have hratio : 1 / (8 * x) < 1 - 1 / (2 * x) := by
    rw [div_lt_iff₀ (by positivity : 0 < 8 * x)]
    field_simp
    nlinarith
  have hsmall : ‖a‖ < X * I * ((1 - 1 / (2 * x)) * d) := by
    calc
      ‖a‖ ≤ (n + 1 : ℝ) := ha
      _ < X * (I / (8 * x)) * d := hstrong
      _ = X * I * ((1 / (8 * x)) * d) := by ring
      _ < X * I * ((1 - 1 / (2 * x)) * d) := by
        gcongr
  rw [norm_div]
  have hC : 0 < ‖activeSlope n k‖ := norm_pos_iff.mpr (activeSlope_ne_zero n k)
  apply (div_le_iff₀ hC).2
  rw [norm_activeSlope]
  change ‖a‖ ≤ (1 - 1 / (2 * x)) * d * (X * I)
  nlinarith [hsmall]

private lemma existsUnique_localPoint (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    ∃! w : ℂ,
      w ∈ closedBall (modelRoot n (innerIndex n k)) (affineRadius n) ∧
        scaledFunction n w = a := by
  apply quantitative_local_inverse (scaledFunction n) (differentiable_scaledFunction n)
    (modelRoot n (innerIndex n k)) (activeSlope n k) a (affineRadius n) (localError n)
  · exact affineRadius_pos n
  · exact localError_lt_one n
  · exact activeSlope_ne_zero n k
  · exact scaledFunction_zero n k
  · exact fun w hw ↦ (scaledFunction_deriv_close n hn k hw).le
  · exact local_target_admissible n hn k a ha

private noncomputable def localPoint (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) : ℂ :=
  Classical.choose (existsUnique_localPoint n hn k a ha)

private lemma localPoint_mem (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    localPoint n hn k a ha ∈
      closedBall (modelRoot n (innerIndex n k)) (affineRadius n) :=
  (Classical.choose_spec (existsUnique_localPoint n hn k a ha)).1.1

private lemma localPoint_value (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    scaledFunction n (localPoint n hn k a ha) = a :=
  (Classical.choose_spec (existsUnique_localPoint n hn k a ha)).1.2

private lemma localPoint_zero (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (hzero : ‖(0 : ℂ)‖ ≤ n + 1) :
    localPoint n hn k 0 hzero = modelRoot n (innerIndex n k) := by
  symm
  apply (Classical.choose_spec (existsUnique_localPoint n hn k 0 hzero)).2
  exact ⟨mem_closedBall_self (affineRadius_pos n).le, scaledFunction_zero n k⟩

private lemma localPoint_secant_error (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a b : ℂ) (ha : ‖a‖ ≤ n + 1) (hb : ‖b‖ ≤ n + 1) :
    ‖(localPoint n hn k a ha - localPoint n hn k b hb) +
        (a - b) / activeSlope n k‖ ≤
      (localError n : ℝ) *
        ‖localPoint n hn k a ha - localPoint n hn k b hb‖ := by
  let C := activeSlope n k
  let g : ℂ → ℂ := fun w ↦ scaledFunction n w + C * w
  let K := closedBall (modelRoot n (innerIndex n k)) (affineRadius n)
  let wa := localPoint n hn k a ha
  let wb := localPoint n hn k b hb
  have hdiff (w : ℂ) : DifferentiableAt ℂ g w := by
    exact (differentiable_scaledFunction n w).add
      ((differentiableAt_const (c := C)).mul differentiableAt_id)
  have hderiv (w : ℂ) : deriv g w = deriv (scaledFunction n) w + C := by
    have hlinear : HasDerivAt (fun u : ℂ ↦ C * u) C w := by
      simpa using (hasDerivAt_id w).const_mul C
    exact ((differentiable_scaledFunction n w).hasDerivAt.add hlinear).deriv
  have hbound (w : ℂ) (hw : w ∈ K) :
      ‖deriv g w‖ ≤ (localError n : ℝ) * ‖C‖ := by
    rw [hderiv]
    exact (scaledFunction_deriv_close n hn k hw).le
  have hwa : wa ∈ K := localPoint_mem n hn k a ha
  have hwb : wb ∈ K := localPoint_mem n hn k b hb
  have hsec := Convex.norm_image_sub_le_of_norm_deriv_le (fun w _ ↦ hdiff w) hbound
    (convex_closedBall (modelRoot n (innerIndex n k)) (affineRadius n)) hwb hwa
  have hgdiff : g wa - g wb = (a - b) + C * (wa - wb) := by
    dsimp only [g]
    rw [show scaledFunction n wa = a from localPoint_value n hn k a ha,
      show scaledFunction n wb = b from localPoint_value n hn k b hb]
    ring
  rw [hgdiff] at hsec
  have hC : 0 < ‖C‖ := norm_pos_iff.mpr (activeSlope_ne_zero n k)
  have hC0 : C ≠ 0 := activeSlope_ne_zero n k
  have hid : (wa - wb) + (a - b) / C = ((a - b) + C * (wa - wb)) / C := by
    field_simp [hC0]
    ring
  rw [hid, norm_div]
  apply (div_le_iff₀ hC).2
  nlinarith

private lemma localPoint_displacement_bound (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    ‖localPoint n hn k a ha - modelRoot n (innerIndex n k)‖ ≤
      ‖a / activeSlope n k‖ / (1 - (localError n : ℝ)) := by
  have hzero : ‖(0 : ℂ)‖ ≤ n + 1 := by
    simp only [norm_zero]
    positivity
  have herr := localPoint_secant_error n hn k a 0 ha hzero
  rw [localPoint_zero n hn k hzero, sub_zero] at herr
  let d := localPoint n hn k a ha - modelRoot n (innerIndex n k)
  let u := a / activeSlope n k
  have htri : ‖d‖ ≤ ‖d + u‖ + ‖u‖ := by
    have := norm_sub_le (d + u) u
    simpa using this
  have hq : (localError n : ℝ) < 1 := by exact_mod_cast localError_lt_one n
  apply (le_div_iff₀ (sub_pos.mpr hq)).2
  nlinarith [htri, herr]

/-! The active linear coefficient, after multiplication by the radial unit
vector, has the recurrently dense phase prescribed at that level. -/

private noncomputable def activeMagnitude (n : ℕ) : ℝ :=
  ‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n * degree n

private lemma activeMagnitude_pos (n : ℕ) : 0 < activeMagnitude n := by
  unfold activeMagnitude
  positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2,
    radius_pos n, degree_pos n]

private noncomputable def radialUnit (n : ℕ) (k : Fin (t n)) : ℂ :=
  (recurrentPhase n : ℂ) *
    (rootOfUnity n (innerIndex n k) : ℂ) ^ previousDegree n

private lemma norm_radialUnit (n : ℕ) (k : Fin (t n)) : ‖radialUnit n k‖ = 1 := by
  simp [radialUnit, Circle.norm_coe]

private lemma activeSlope_radial_close (n : ℕ) (k : Fin (t (n + 1))) :
    ‖activeSlope (n + 1) k * modelRoot (n + 1) (innerIndex (n + 1) k) -
        (activeMagnitude (n + 1) : ℂ) * radialUnit (n + 1) k‖ <
      activeMagnitude (n + 1) / (n + 3) := by
  let q := n + 1
  let c := modelRoot q (innerIndex q k)
  let A := leadingCoefficient (constructionState q) q
  let R := radius q
  let S := previousDegree q
  let m := degree q
  have hc : ‖c‖ = 1 := norm_modelRoot_inner q k
  have hc0 : c ≠ 0 := modelRoot_ne_zero q (innerIndex q k)
  have hphaseCircle := radial_phase_identity n k
  have hphase := congrArg (fun u : Circle ↦ (u : ℂ)) hphaseCircle
  simp only [Circle.coe_mul, Circle.coe_pow] at hphase
  have hreference : A * (R : ℂ) ^ S * (m : ℂ) * c ^ S =
      (activeMagnitude q : ℂ) * radialUnit q k := by
    dsimp only [q, c, A, R, S, m]
    rw [leadingCoefficient_phase]
    unfold activeMagnitude radialUnit
    rw [modelRoot_inner]
    push_cast
    let Q : ℂ :=
      (‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ : ℂ) *
        (radius (n + 1) : ℂ) ^ previousDegree (n + 1) *
          (degree (n + 1) : ℂ)
    calc
      (‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ : ℂ) *
              ((phaseData (n + 1)).leading : ℂ) *
            (radius (n + 1) : ℂ) ^ previousDegree (n + 1) *
          (degree (n + 1) : ℂ) *
        (((phaseData (n + 1)).rotation : ℂ) *
          (rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ)) ^
            previousDegree (n + 1) =
          Q * (((phaseData (n + 1)).leading : ℂ) *
            (((phaseData (n + 1)).rotation : ℂ) *
              (rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ)) ^
                previousDegree (n + 1)) := by ring
      _ = Q * ((recurrentPhase (n + 1) : ℂ) *
          (rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ) ^
            previousDegree (n + 1)) := congrArg (fun x : ℂ ↦ Q * x) hphase
      _ = (‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ *
            radius (n + 1) ^ previousDegree (n + 1) * degree (n + 1) : ℝ) *
          ((recurrentPhase (n + 1) : ℂ) *
            (rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ) ^
              previousDegree (n + 1)) := by
        dsimp only [Q]
        have hcoefcast :
            ((‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ *
                radius (n + 1) ^ previousDegree (n + 1) *
                  (degree (n + 1) : ℝ) : ℝ) : ℂ) =
              (‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ : ℂ) *
                (radius (n + 1) : ℂ) ^ previousDegree (n + 1) *
                  (degree (n + 1) : ℂ) := by
          push_cast
          rfl
        exact congrArg
          (fun x : ℂ ↦ x *
            ((recurrentPhase (n + 1) : ℂ) *
              (rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ) ^
                previousDegree (n + 1))) hcoefcast.symm
      _ = (‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ : ℂ) *
            (radius (n + 1) : ℂ) ^ previousDegree (n + 1) *
              (degree (n + 1) : ℂ) *
          ((recurrentPhase (n + 1) : ℂ) *
            (rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ) ^
              previousDegree (n + 1)) := by
        push_cast
        rfl
  have hfactor : activeSlope q k * c - (activeMagnitude q : ℂ) * radialUnit q k =
      A * (R : ℂ) ^ S * c ^ S *
        (modelSlope q (innerIndex q k) * c - (m : ℂ)) := by
    rw [← hreference]
    simp only [activeSlope, idealSlope, q, c, A, R, S, m]
    ring
  have hslope := modelSlope_inner_close q k
  have hslopeMul :
      ‖modelSlope q (innerIndex q k) * c - (m : ℂ)‖ < (m : ℝ) / (n + 3) := by
    have heq : modelSlope q (innerIndex q k) * c - (m : ℂ) =
        (modelSlope q (innerIndex q k) - (m : ℂ) * c⁻¹) * c := by
      field_simp [hc0]
    rw [heq, norm_mul, hc, mul_one]
    dsimp only [q, m, c] at hslope ⊢
    norm_num only [Nat.cast_add, Nat.cast_one] at hslope ⊢
    convert hslope using 1 ; ring
  rw [hfactor, norm_mul, norm_mul, norm_mul]
  rw [norm_pow c S, hc, one_pow, mul_one]
  have hRnorm : ‖(R : ℂ)‖ = R := by
    dsimp only [R, q]
    calc
      ‖(radius (n + 1) : ℂ)‖ = |radius (n + 1)| := RCLike.norm_ofReal _
      _ = radius (n + 1) := abs_of_pos (radius_pos (n + 1))
  rw [norm_pow (R : ℂ) S, hRnorm]
  dsimp only [activeMagnitude, A, R, S, m, q]
  have hcoef : 0 < ‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ *
      radius (n + 1) ^ previousDegree (n + 1) := by
    positivity [leadingCoefficient_ne_zero_of_valid (constructionState (n + 1)).2,
      radius_pos (n + 1)]
  calc
    ‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ *
        radius (n + 1) ^ previousDegree (n + 1) *
          ‖modelSlope (n + 1) (innerIndex (n + 1) k) *
            modelRoot (n + 1) (innerIndex (n + 1) k) - (degree (n + 1) : ℂ)‖ <
      (‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ *
        radius (n + 1) ^ previousDegree (n + 1)) *
          ((degree (n + 1) : ℝ) / (n + 3)) :=
      mul_lt_mul_of_pos_left hslopeMul hcoef
    _ = ‖leadingCoefficient (constructionState (n + 1)) (n + 1)‖ *
        radius (n + 1) ^ previousDegree (n + 1) * degree (n + 1) / (n + 3) := by
      ring

private lemma activeSlope_radial_close_of_ne_zero (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) :
    ‖activeSlope n k * modelRoot n (innerIndex n k) -
        (activeMagnitude n : ℂ) * radialUnit n k‖ <
      activeMagnitude n / (n + 2) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h := activeSlope_radial_close q k
  convert h using 1
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private lemma norm_idealSlope_lt_two_mul_degree (n : ℕ) (k : Fin (t n)) :
    ‖idealSlope n k‖ < 2 * degree n := by
  have hclose := modelSlope_inner_close n k
  have href :
      ‖(degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹‖ = (degree n : ℝ) := by
    rw [norm_mul, norm_inv, norm_modelRoot_inner, inv_one, mul_one]
    simp
  have htri : ‖modelSlope n (innerIndex n k)‖ ≤
      ‖modelSlope n (innerIndex n k) -
        (degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹‖ +
        (degree n : ℝ) := by
    calc
      ‖modelSlope n (innerIndex n k)‖ =
          ‖(modelSlope n (innerIndex n k) -
              (degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹) +
            (degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹‖ := by ring_nf
      _ ≤ ‖modelSlope n (innerIndex n k) -
              (degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹‖ +
            ‖(degree n : ℂ) * (modelRoot n (innerIndex n k))⁻¹‖ := norm_add_le _ _
      _ = _ := by rw [href]
  have hfrac : (degree n : ℝ) / (n + 2) ≤ degree n := by
    have hdegree : 0 ≤ (degree n : ℝ) := by positivity
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).2 (by
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  have hideal : ‖idealSlope n k‖ = ‖modelSlope n (innerIndex n k)‖ := by
    rw [idealSlope, norm_mul, norm_pow, norm_modelRoot_inner, one_pow, one_mul]
  rw [hideal]
  nlinarith

private lemma affineRadius_lt_quarter (n : ℕ) : affineRadius n < 1 / 4 :=
  (affineRadius_lt_localRadius n).trans
    ((localRadius_lt_modelRadius n).trans (modelRadius_lt_quarter n))

private lemma activeMagnitude_large (n : ℕ) (hn : n ≠ 0) :
    16 * (n + 1 : ℝ) * (n + 2) < activeMagnitude n := by
  let X : ℝ := ‖leadingCoefficient (constructionState n) n‖ *
    radius n ^ previousDegree n
  have hcapacity := (radius_admissible n).2.2.2.2.2.1 hn
  have hmargin := derivativeMargin_lt n (⟨0, lt_of_lt_of_le (by omega) (four_le_t n)⟩)
  have hideal := norm_idealSlope_lt_two_mul_degree n
    (⟨0, lt_of_lt_of_le (by omega) (four_le_t n)⟩)
  have hX : 0 < X := by
    dsimp only [X]
    positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2, radius_pos n]
  have haff : 0 < affineRadius n := affineRadius_pos n
  have hbound :
      X * derivativeMargin n * affineRadius n <
        activeMagnitude n / (16 * (n + 2)) := by
    have h₁ : derivativeMargin n < (degree n : ℝ) / (4 * (n + 2)) := by
      calc
        derivativeMargin n <
            ‖idealSlope n ⟨0, lt_of_lt_of_le (by omega) (four_le_t n)⟩‖ /
              (8 * (n + 2)) := hmargin
        _ < (2 * degree n) / (8 * (n + 2)) := by
          gcongr
        _ = (degree n : ℝ) / (4 * (n + 2)) := by
          field_simp ; ring
    have h₂ : derivativeMargin n * affineRadius n <
        (degree n : ℝ) / (16 * (n + 2)) := by
      calc
        derivativeMargin n * affineRadius n <
            ((degree n : ℝ) / (4 * (n + 2))) * affineRadius n :=
          mul_lt_mul_of_pos_right h₁ haff
        _ < ((degree n : ℝ) / (4 * (n + 2))) * (1 / 4) := by
          exact mul_lt_mul_of_pos_left (affineRadius_lt_quarter n) (by
            positivity [degree_pos n])
        _ = (degree n : ℝ) / (16 * (n + 2)) := by
          field_simp ; ring
    calc
      X * derivativeMargin n * affineRadius n =
          X * (derivativeMargin n * affineRadius n) := by ring
      _ < X * ((degree n : ℝ) / (16 * (n + 2))) :=
        mul_lt_mul_of_pos_left h₂ hX
      _ = activeMagnitude n / (16 * (n + 2)) := by
        unfold activeMagnitude
        dsimp only [X]
        ring
  have hmain : (n + 1 : ℝ) < activeMagnitude n / (16 * (n + 2)) :=
    hcapacity.trans hbound
  have hden : 0 < (16 : ℝ) * (n + 2) := by positivity
  rw [lt_div_iff₀ hden] at hmain
  nlinarith

private lemma rootOfUnity_short_arc (n : ℕ) (k : Fin (t (n + 1))) :
    ‖(rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ) ^
          previousDegree (n + 1) - 1‖ <
      8 / (n + 2) := by
  let S := previousDegree (n + 1)
  let T := t (n + 1)
  let j : ℕ := k
  let θ : ℝ := (j * S : ℕ) * (2 * Real.pi / degree (n + 1))
  have hS : (n + 2) * S < T := by
    calc
      (n + 2) * S < (n + 2) * (S + 1) :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self S) (by omega)
      _ < T := by simpa only [S, T] using growth_bound n
  have hnat : (n + 2) * (j * S) < degree (n + 1) := by
    rw [degree, pow_two]
    have hmul : j * ((n + 2) * S) < T * T := by
      calc
        j * ((n + 2) * S) ≤ T * ((n + 2) * S) :=
          Nat.mul_le_mul_right ((n + 2) * S) k.isLt.le
        _ < T * T := Nat.mul_lt_mul_of_pos_left hS
          (lt_of_lt_of_le (by omega) (four_le_t (n + 1)))
    simpa only [j, T, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hdegree : (0 : ℝ) < degree (n + 1) := by exact_mod_cast degree_pos (n + 1)
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hratio : ((j * S : ℕ) : ℝ) / degree (n + 1) < 1 / (n + 2) := by
    apply (div_lt_iff₀ hdegree).2
    have hnatReal : ((n + 2 : ℕ) : ℝ) * ((j * S : ℕ) : ℝ) <
        degree (n + 1) := by exact_mod_cast hnat
    calc
      ((j * S : ℕ) : ℝ) =
          (1 / (n + 2 : ℝ)) * (((n + 2 : ℕ) : ℝ) * ((j * S : ℕ) : ℝ)) := by
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        field_simp
      _ < (1 / (n + 2 : ℝ)) * degree (n + 1) :=
        mul_lt_mul_of_pos_left hnatReal (by positivity)
      _ = 1 / (n + 2) * degree (n + 1) := by norm_num
  have hθnonneg : 0 ≤ θ := by
    dsimp only [θ]
    positivity [Real.pi_pos]
  have hθ : θ < 8 / (n + 2) := by
    have hpi : 2 * Real.pi < 8 := by linarith [Real.pi_lt_four]
    calc
      θ = (2 * Real.pi) * (((j * S : ℕ) : ℝ) / degree (n + 1)) := by
        dsimp only [θ]
        push_cast
        ring
      _ < (2 * Real.pi) * (1 / (n + 2)) :=
        mul_lt_mul_of_pos_left hratio (by positivity [Real.pi_pos])
      _ < 8 * (1 / (n + 2)) :=
        mul_lt_mul_of_pos_right hpi (by positivity)
      _ = 8 / (n + 2) := by ring
  have hpow :
      rootOfUnity (n + 1) (innerIndex (n + 1) k) ^ previousDegree (n + 1) =
        Circle.exp θ := by
    rw [rootOfUnity, ← pow_mul, primitiveDirection, ← Circle.exp_natCast_mul]
    congr 1
  have hpowC := congrArg (fun z : Circle ↦ (z : ℂ)) hpow
  simp only [Circle.coe_pow] at hpowC
  rw [hpowC, Circle.coe_exp]
  have hcomm : (θ : ℂ) * Complex.I = Complex.I * θ := by ring
  rw [hcomm]
  exact lt_of_le_of_lt Real.norm_exp_I_mul_ofReal_sub_one_le (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hθnonneg] using hθ)

private lemma radialUnit_close_recurrentPhase (n : ℕ) (k : Fin (t (n + 1))) :
    ‖radialUnit (n + 1) k - (recurrentPhase (n + 1) : ℂ)‖ <
      8 / (n + 2) := by
  unfold radialUnit
  have hfactor :
      (recurrentPhase (n + 1) : ℂ) *
            (rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ) ^
              previousDegree (n + 1) -
          (recurrentPhase (n + 1) : ℂ) =
        (recurrentPhase (n + 1) : ℂ) *
          ((rootOfUnity (n + 1) (innerIndex (n + 1) k) : ℂ) ^
              previousDegree (n + 1) - 1) := by ring
  rw [hfactor, norm_mul, Circle.norm_coe, one_mul]
  exact rootOfUnity_short_arc n k

private lemma half_activeMagnitude_lt_norm_activeSlope (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) :
    activeMagnitude n / 2 < ‖activeSlope n k‖ := by
  let D := activeMagnitude n
  let C := activeSlope n k
  let c := modelRoot n (innerIndex n k)
  let u := radialUnit n k
  have hclose := activeSlope_radial_close_of_ne_zero n hn k
  have hCc : ‖C * c‖ = ‖C‖ := by
    dsimp only [C, c]
    rw [norm_mul, norm_modelRoot_inner, mul_one]
  have hDu : ‖(D : ℂ) * u‖ = D := by
    dsimp only [D, u]
    rw [norm_mul, norm_radialUnit]
    norm_num [abs_of_pos (activeMagnitude_pos n)]
  have htri : D ≤ ‖C * c - (D : ℂ) * u‖ + ‖C * c‖ := by
    calc
      D = ‖(D : ℂ) * u‖ := hDu.symm
      _ = ‖(C * c - (D : ℂ) * u) - C * c‖ := by
        rw [show (C * c - (D : ℂ) * u) - C * c = -((D : ℂ) * u) by ring,
          norm_neg]
      _ ≤ ‖C * c - (D : ℂ) * u‖ + ‖C * c‖ := norm_sub_le _ _
  have hx : (3 : ℝ) ≤ n + 2 := by
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    exact_mod_cast (show 3 ≤ n + 2 by omega)
  have hD : 0 < D := activeMagnitude_pos n
  have hsmall : D / (n + 2) ≤ D / 3 := by
    exact div_le_div_of_nonneg_left hD.le (by norm_num) hx
  rw [hCc] at htri
  change ‖C * c - (D : ℂ) * u‖ < D / (n + 2) at hclose
  change D / 2 < ‖C‖
  nlinarith

private lemma localPoint_displacement_scaled_bound (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    activeMagnitude n *
        ‖localPoint n hn k a ha - modelRoot n (innerIndex n k)‖ ≤
      4 * ‖a‖ := by
  let D := activeMagnitude n
  let C := activeSlope n k
  let d := localPoint n hn k a ha - modelRoot n (innerIndex n k)
  let q : ℝ := localError n
  have hdisp := localPoint_displacement_bound n hn k a ha
  have hC : D / 2 < ‖C‖ := half_activeMagnitude_lt_norm_activeSlope n hn k
  have hD : 0 < D := activeMagnitude_pos n
  have hq : q ≤ 1 / 2 := by
    dsimp only [q]
    rw [localError_coe]
    have hx : (1 : ℝ) ≤ n + 2 := by
      exact_mod_cast (show 1 ≤ n + 2 by omega)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n + 2))).2
    nlinarith
  have hden : 1 / 2 ≤ 1 - q := by linarith
  have hnum : ‖a‖ / ‖C‖ ≤ ‖a‖ / (D / 2) := by
    exact div_le_div_of_nonneg_left (norm_nonneg a) (by positivity) hC.le
  have hbound : ‖d‖ ≤ 4 * ‖a‖ / D := by
    calc
      ‖d‖ ≤ (‖a‖ / ‖C‖) / (1 - q) := by
        dsimp only [d, C, q]
        simpa only [norm_div] using hdisp
      _ ≤ (‖a‖ / ‖C‖) / (1 / 2) := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ ≤ (‖a‖ / (D / 2)) / (1 / 2) := by
        gcongr
      _ = 4 * ‖a‖ / D := by field_simp ; ring
  have := mul_le_mul_of_nonneg_left hbound hD.le
  calc
    activeMagnitude n *
          ‖localPoint n hn k a ha - modelRoot n (innerIndex n k)‖ ≤
        D * (4 * ‖a‖ / D) := by simpa only [D, d] using this
    _ = 4 * ‖a‖ := by field_simp [hD.ne']

private lemma radial_inverse_close (n : ℕ) (hn : n ≠ 0) (k : Fin (t n)) :
    ‖modelRoot n (innerIndex n k) / radialUnit n k -
        (activeMagnitude n : ℂ) / activeSlope n k‖ ≤
      2 / (n + 2) := by
  let D := activeMagnitude n
  let C := activeSlope n k
  let c := modelRoot n (innerIndex n k)
  let u := radialUnit n k
  have hclose := activeSlope_radial_close_of_ne_zero n hn k
  have hC : D / 2 < ‖C‖ := half_activeMagnitude_lt_norm_activeSlope n hn k
  have hD : 0 < D := activeMagnitude_pos n
  have hu : ‖u‖ = 1 := norm_radialUnit n k
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hC0 : C ≠ 0 := activeSlope_ne_zero n k
  have hid : c / u - (D : ℂ) / C =
      (C * c - (D : ℂ) * u) / (u * C) := by
    field_simp [hu0, hC0]
  rw [hid, norm_div, norm_mul, hu, one_mul]
  have hCpos : 0 < ‖C‖ := (by positivity : 0 < D / 2).trans hC
  calc
    ‖C * c - (D : ℂ) * u‖ / ‖C‖ ≤ (D / (n + 2)) / ‖C‖ :=
      (div_le_div_iff_of_pos_right hCpos).2 hclose.le
    _ ≤ (D / (n + 2)) / (D / 2) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hC.le
    _ = 2 / (n + 2) := by field_simp

private lemma localPoint_scaled_displacement_error (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    ‖(activeMagnitude n : ℂ) *
          (localPoint n hn k a ha - modelRoot n (innerIndex n k)) +
        a * (modelRoot n (innerIndex n k) / radialUnit n k)‖ ≤
      4 * ‖a‖ / (n + 2) := by
  let D := activeMagnitude n
  let C := activeSlope n k
  let c := modelRoot n (innerIndex n k)
  let u := radialUnit n k
  let d := localPoint n hn k a ha - c
  let q : ℝ := localError n
  have hzero : ‖(0 : ℂ)‖ ≤ n + 1 := by
    simp only [norm_zero]
    positivity
  have hsec := localPoint_secant_error n hn k a 0 ha hzero
  rw [localPoint_zero n hn k hzero, sub_zero] at hsec
  have hdisp := localPoint_displacement_scaled_bound n hn k a ha
  have hinv := radial_inverse_close n hn k
  have hD : 0 < D := activeMagnitude_pos n
  have hid :
      (D : ℂ) * d + a * (c / u) =
        (D : ℂ) * (d + a / C) + a * (c / u - (D : ℂ) / C) := by
    field_simp [activeSlope_ne_zero n k]
    ring
  rw [hid]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have hfirst : ‖(D : ℂ)‖ * ‖d + a / C‖ ≤ 2 * ‖a‖ / (n + 2) := by
    have hDn : ‖(D : ℂ)‖ = D := by
      calc
        ‖(D : ℂ)‖ = |D| := RCLike.norm_ofReal _
        _ = D := abs_of_pos hD
    rw [hDn]
    have hqeq : q = 1 / (2 * (n + 2)) := by rfl
    have hs : ‖d + a / C‖ ≤ q * ‖d‖ := by
      dsimp only [d, C, c, q]
      simpa using hsec
    calc
      D * ‖d + a / C‖ ≤ D * (q * ‖d‖) := mul_le_mul_of_nonneg_left hs hD.le
      _ = q * (D * ‖d‖) := by ring
      _ ≤ q * (4 * ‖a‖) := mul_le_mul_of_nonneg_left
        (by simpa only [D, d] using hdisp) (by positivity)
      _ = 2 * ‖a‖ / (n + 2) := by
        rw [hqeq]
        field_simp ; ring
  have hsecond : ‖a‖ * ‖c / u - (D : ℂ) / C‖ ≤ 2 * ‖a‖ / (n + 2) := by
    calc
      ‖a‖ * ‖c / u - (D : ℂ) / C‖ ≤ ‖a‖ * (2 / (n + 2)) :=
        mul_le_mul_of_nonneg_left (by simpa only [D, C, c, u] using hinv) (norm_nonneg a)
      _ = 2 * ‖a‖ / (n + 2) := by ring
  calc
    ‖(D : ℂ)‖ * ‖d + a / C‖ + ‖a‖ * ‖c / u - (D : ℂ) / C‖ ≤
        2 * ‖a‖ / (n + 2) + 2 * ‖a‖ / (n + 2) := add_le_add hfirst hsecond
    _ = 4 * ‖a‖ / (n + 2) := by ring

private lemma radialUnit_close_recurrentPhase_of_ne_zero (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) :
    ‖radialUnit n k - (recurrentPhase n : ℂ)‖ < 8 / (n + 1) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h := radialUnit_close_recurrentPhase q k
  convert h using 1
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private noncomputable def differenceDirection (a b : ℂ) (hab : a ≠ b) : Circle := by
  refine ⟨(a - b) / ‖a - b‖, ?_⟩
  change (a - b) / (‖a - b‖ : ℂ) ∈ sphere (0 : ℂ) 1
  rw [mem_sphere_zero_iff_norm, norm_div]
  have hv : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv, div_self hv.ne']

private lemma coe_differenceDirection (a b : ℂ) (hab : a ≠ b) :
    (differenceDirection a b hab : ℂ) = (a - b) / ‖a - b‖ := rfl

private lemma localPoint_radial_order (n : ℕ) (hn : n ≠ 0) (k l : Fin (t n))
    (a b : ℂ) (hab : a ≠ b) (ha : ‖a‖ ≤ n + 1) (hb : ‖b‖ ≤ n + 1)
    (hphase : ‖radialUnit n k - (differenceDirection a b hab : ℂ)‖ < 1 / 8)
    (hcross : ‖b‖ * ‖radialUnit n k - radialUnit n l‖ < ‖a - b‖ / 2)
    (herror : 4 * (‖a‖ + ‖b‖) / (n + 2) ≤ ‖a - b‖ / 8)
    (hquadratic : 16 * (‖a‖ ^ 2 + ‖b‖ ^ 2) / activeMagnitude n < ‖a - b‖ / 2) :
    ‖localPoint n hn k a ha‖ < ‖localPoint n hn l b hb‖ := by
  let D := activeMagnitude n
  let ca := modelRoot n (innerIndex n k)
  let cb := modelRoot n (innerIndex n l)
  let ua := radialUnit n k
  let ub := radialUnit n l
  let wa := localPoint n hn k a ha
  let wb := localPoint n hn l b hb
  let da := wa - ca
  let db := wb - cb
  let ea := (D : ℂ) * da + a * (ca / ua)
  let eb := (D : ℂ) * db + b * (cb / ub)
  let v := a - b
  let L := ‖v‖
  have hD : 0 < D := activeMagnitude_pos n
  have hca : ‖ca‖ = 1 := norm_modelRoot_inner n k
  have hcb : ‖cb‖ = 1 := norm_modelRoot_inner n l
  have hua : ‖ua‖ = 1 := norm_radialUnit n k
  have hub : ‖ub‖ = 1 := norm_radialUnit n l
  have hca0 : ca ≠ 0 := norm_ne_zero_iff.mp (by rw [hca]; norm_num)
  have hcb0 : cb ≠ 0 := norm_ne_zero_iff.mp (by rw [hcb]; norm_num)
  have hua0 : ua ≠ 0 := norm_ne_zero_iff.mp (by rw [hua]; norm_num)
  have hub0 : ub ≠ 0 := norm_ne_zero_iff.mp (by rw [hub]; norm_num)
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hab
  have hL : 0 < L := norm_pos_iff.mpr hv0
  have hea : ‖ea‖ ≤ 4 * ‖a‖ / (n + 2) := by
    dsimp only [ea, da, wa, ca, ua, D]
    exact localPoint_scaled_displacement_error n hn k a ha
  have heb : ‖eb‖ ≤ 4 * ‖b‖ / (n + 2) := by
    dsimp only [eb, db, wb, cb, ub, D]
    exact localPoint_scaled_displacement_error n hn l b hb
  have he : ‖ea - eb‖ ≤ L / 8 := by
    calc
      ‖ea - eb‖ ≤ ‖ea‖ + ‖eb‖ := norm_sub_le _ _
      _ ≤ 4 * ‖a‖ / (n + 2) + 4 * ‖b‖ / (n + 2) := add_le_add hea heb
      _ = 4 * (‖a‖ + ‖b‖) / (n + 2) := by ring
      _ ≤ ‖a - b‖ / 8 := herror
      _ = L / 8 := rfl
  have hscaledA : (D : ℂ) * da = -(a * (ca / ua)) + ea := by
    dsimp only [ea]
    ring
  have hscaledB : (D : ℂ) * db = -(b * (cb / ub)) + eb := by
    dsimp only [eb]
    ring
  have htarget : conj v * ((differenceDirection a b hab : Circle) : ℂ) =
      (L : ℂ) := by
    rw [coe_differenceDirection]
    dsimp only [v, L]
    rw [div_eq_mul_inv, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    have hnorm : ‖a - b‖ ≠ 0 := (norm_pos_iff.mpr hv0).ne'
    push_cast
    field_simp [hnorm]
  have hphaseIdeal : ‖conj v * ua - (L : ℂ)‖ < L / 8 := by
    rw [← htarget, ← mul_sub]
    rw [norm_mul, RCLike.norm_conj]
    change L * ‖ua - (differenceDirection a b hab : ℂ)‖ < L / 8
    calc
      L * ‖ua - (differenceDirection a b hab : ℂ)‖ < L * (1 / 8) :=
        mul_lt_mul_of_pos_left (by simpa only [ua] using hphase) hL
      _ = L / 8 := by ring
  have hcaconj : ca * conj ca = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hca]
    norm_num
  have hcbconj : cb * conj cb = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcb]
    norm_num
  have huaconj : conj ua = ua⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hua]
    norm_num
  have hubconj : conj ub = ub⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hub]
    norm_num
  have hidealA : ca * conj (-(a * (ca / ua))) = -conj a * ua := by
    simp only [map_neg, map_mul, div_eq_mul_inv, map_inv₀]
    rw [huaconj, inv_inv]
    calc
      ca * -(conj a * (conj ca * ua)) = -(conj a) * ((ca * conj ca) * ua) := by ring
      _ = -conj a * ua := by rw [hcaconj, one_mul]
  have hidealB : cb * conj (-(b * (cb / ub))) = -conj b * ub := by
    simp only [map_neg, map_mul, div_eq_mul_inv, map_inv₀]
    rw [hubconj, inv_inv]
    calc
      cb * -(conj b * (conj cb * ub)) = -(conj b) * ((cb * conj cb) * ub) := by ring
      _ = -conj b * ub := by rw [hcbconj, one_mul]
  have hradialA : ca * conj ((D : ℂ) * da) = -conj a * ua + ca * conj ea := by
    rw [hscaledA, map_add, mul_add, hidealA]
  have hradialB : cb * conj ((D : ℂ) * db) = -conj b * ub + cb * conj eb := by
    rw [hscaledB, map_add, mul_add, hidealB]
  have hrePhase : (conj v * ua).re > L - L / 8 := by
    have hre := Complex.abs_re_le_norm (conj v * ua - (L : ℂ))
    have hreal : (conj v * ua - (L : ℂ)).re =
        (conj v * ua).re - L := by simp
    rw [hreal] at hre
    have habs : |(conj v * ua).re - L| < L / 8 := hre.trans_lt hphaseIdeal
    exact by nlinarith [(abs_lt.mp habs).1]
  have hcrossReal : |(conj b * (ua - ub)).re| < L / 2 := by
    calc
      |(conj b * (ua - ub)).re| ≤ ‖conj b * (ua - ub)‖ := Complex.abs_re_le_norm _
      _ = ‖b‖ * ‖ua - ub‖ := by rw [norm_mul, RCLike.norm_conj]
      _ < L / 2 := by simpa only [ua, ub, L] using hcross
  have hmain : (conj a * ua - conj b * ub).re > 3 * L / 8 := by
    have hid : conj a * ua - conj b * ub =
        conj v * ua + conj b * (ua - ub) := by
      dsimp only [v]
      simp only [map_sub]
      ring
    rw [hid, Complex.add_re]
    have hcrossLower : -(L / 2) < (conj b * (ua - ub)).re :=
      (abs_lt.mp hcrossReal).1
    nlinarith
  have hreError : (ca * conj ea - cb * conj eb).re ≤ L / 8 := by
    calc
      (ca * conj ea - cb * conj eb).re ≤
          |(ca * conj ea - cb * conj eb).re| := le_abs_self _
      _ ≤ ‖ca * conj ea - cb * conj eb‖ := Complex.abs_re_le_norm _
      _ ≤ ‖ca * conj ea‖ + ‖cb * conj eb‖ := norm_sub_le _ _
      _ = ‖ea‖ + ‖eb‖ := by rw [norm_mul, norm_mul, hca, hcb,
        RCLike.norm_conj, RCLike.norm_conj, one_mul, one_mul]
      _ ≤ L / 8 := by
        calc
          ‖ea‖ + ‖eb‖ ≤ 4 * ‖a‖ / (n + 2) + 4 * ‖b‖ / (n + 2) :=
            add_le_add hea heb
          _ = 4 * (‖a‖ + ‖b‖) / (n + 2) := by ring
          _ ≤ ‖a - b‖ / 8 := herror
          _ = L / 8 := rfl
  have hradialIdentity :
      ca * conj ((D : ℂ) * da) - cb * conj ((D : ℂ) * db) =
        -(conj a * ua - conj b * ub) + (ca * conj ea - cb * conj eb) := by
    rw [hradialA, hradialB]
    ring
  have hradial :
      (ca * conj ((D : ℂ) * da) - cb * conj ((D : ℂ) * db)).re < -(L / 4) := by
    rw [hradialIdentity, Complex.add_re, Complex.neg_re]
    simp only [Complex.sub_re]
    have hmain' : (conj a * ua).re - (conj b * ub).re > 3 * L / 8 := by
      simpa only [Complex.sub_re] using hmain
    have hreError' : (ca * conj ea).re - (cb * conj eb).re ≤ L / 8 := by
      simpa only [Complex.sub_re] using hreError
    nlinarith
  have hda := localPoint_displacement_scaled_bound n hn k a ha
  have hdb := localPoint_displacement_scaled_bound n hn l b hb
  have hdaSq : (D * ‖da‖) ^ 2 ≤ (4 * ‖a‖) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).2
    simpa only [D, da, wa, ca] using hda
  have hdbSq : (D * ‖db‖) ^ 2 ≤ (4 * ‖b‖) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).2
    simpa only [D, db, wb, cb] using hdb
  have hquad : D * (Complex.normSq da + Complex.normSq db) < L / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have haBound : D * ‖da‖ ^ 2 ≤ 16 * ‖a‖ ^ 2 / D := by
      apply (le_div_iff₀ hD).2
      nlinarith [hdaSq]
    have hbBound : D * ‖db‖ ^ 2 ≤ 16 * ‖b‖ ^ 2 / D := by
      apply (le_div_iff₀ hD).2
      nlinarith [hdbSq]
    calc
      D * (‖da‖ ^ 2 + ‖db‖ ^ 2) = D * ‖da‖ ^ 2 + D * ‖db‖ ^ 2 := by ring
      _ ≤ 16 * ‖a‖ ^ 2 / D + 16 * ‖b‖ ^ 2 / D := add_le_add haBound hbBound
      _ = 16 * (‖a‖ ^ 2 + ‖b‖ ^ 2) / D := by ring
      _ < ‖a - b‖ / 2 := hquadratic
      _ = L / 2 := rfl
  have hnormSqIdentity :
      D * (Complex.normSq wa - Complex.normSq wb) =
        2 * (ca * conj ((D : ℂ) * da) - cb * conj ((D : ℂ) * db)).re +
          D * (Complex.normSq da - Complex.normSq db) := by
    have hwa : wa = ca + da := by dsimp only [da]; ring
    have hwb : wb = cb + db := by dsimp only [db]; ring
    have hreScaleA :
        (ca * conj ((D : ℂ) * da)).re = D * (ca * conj da).re := by
      simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im]
      ring
    have hreScaleB :
        (cb * conj ((D : ℂ) * db)).re = D * (cb * conj db).re := by
      simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im]
      ring
    have hcaSq : Complex.normSq ca = 1 := by
      rw [Complex.normSq_eq_norm_sq, hca]
      norm_num
    have hcbSq : Complex.normSq cb = 1 := by
      rw [Complex.normSq_eq_norm_sq, hcb]
      norm_num
    rw [Complex.sub_re, hreScaleA, hreScaleB]
    rw [hwa, hwb, Complex.normSq_add, Complex.normSq_add, hcaSq, hcbSq]
    ring
  have hnormSq : Complex.normSq wa < Complex.normSq wb := by
    have hquad' : D * (Complex.normSq da - Complex.normSq db) < L / 2 := by
      have hnonneg := Complex.normSq_nonneg db
      calc
        D * (Complex.normSq da - Complex.normSq db) ≤
            D * (Complex.normSq da + Complex.normSq db) := by
          apply mul_le_mul_of_nonneg_left _ hD.le
          linarith
        _ < L / 2 := hquad
    have hneg : D * (Complex.normSq wa - Complex.normSq wb) < 0 := by
      rw [hnormSqIdentity]
      calc
        2 * (ca * conj ((D : ℂ) * da) - cb * conj ((D : ℂ) * db)).re +
              D * (Complex.normSq da - Complex.normSq db) <
            2 * (-(L / 4)) + L / 2 :=
          add_lt_add (mul_lt_mul_of_pos_left hradial (by norm_num)) hquad'
        _ = 0 := by ring
    have hdiff : Complex.normSq wa - Complex.normSq wb < 0 := by
      have hdiv : Complex.normSq wa - Complex.normSq wb < 0 / D :=
        (lt_div_iff₀ hD).2 (by simpa only [zero_mul, mul_comm] using hneg)
      simpa only [zero_div] using hdiv
    exact sub_neg.mp hdiff
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hnormSq
  exact (sq_lt_sq₀ (norm_nonneg wa) (norm_nonneg wb)).mp hnormSq

private lemma exists_radial_separating_stage (a b : ℂ) (hab : a ≠ b) (N : ℕ) :
    ∃ n : ℕ, ∃ hn : n ≠ 0, ∃ ha : ‖a‖ ≤ n + 1, ∃ hb : ‖b‖ ≤ n + 1,
      N < n ∧ ∀ k l : Fin (t n),
        ‖localPoint n hn k a ha‖ < ‖localPoint n hn l b hb‖ := by
  let L := ‖a - b‖
  let Q := ‖a‖ ^ 2 + ‖b‖ ^ 2
  let X : ℝ := (N : ℝ) + 129 + ‖a‖ + ‖b‖ +
    32 * (‖a‖ + ‖b‖) / L + 2 * Q / L
  have hL : 0 < L := by
    dsimp only [L]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hQ : 0 < Q := by
    dsimp only [Q]
    by_contra h
    have hzero : Q = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    have ha0 : ‖a‖ = 0 := by nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
    have hb0 : ‖b‖ = 0 := by nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
    exact hab (norm_eq_zero.mp ha0 ▸ norm_eq_zero.mp hb0 ▸ rfl)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt X
  obtain ⟨n, hnN₀, hrec⟩ :=
    recurrentPhase_recurrent (differenceDirection a b hab) (by norm_num : (0 : ℝ) < 1 / 16) N₀
  have hN₀n : (N₀ : ℝ) < n := by exact_mod_cast hnN₀
  have hXn : X < (n : ℝ) := hN₀.trans hN₀n
  have hNreal : (N : ℝ) < n := by
    dsimp only [X] at hXn
    have hnonneg : 0 ≤ 32 * (‖a‖ + ‖b‖) / L := by positivity
    have hnonnegQ : 0 ≤ 2 * Q / L := by positivity
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hN : N < n := by exact_mod_cast hNreal
  have hlarge : (128 : ℝ) < n := by
    dsimp only [X] at hXn
    have hnonneg : 0 ≤ 32 * (‖a‖ + ‖b‖) / L := by positivity
    have hnonnegQ : 0 ≤ 2 * Q / L := by positivity
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), norm_nonneg a, norm_nonneg b]
  have hn : n ≠ 0 := by
    have : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
    omega
  have hana : ‖a‖ < n := by
    dsimp only [X] at hXn
    have hnonneg : 0 ≤ 32 * (‖a‖ + ‖b‖) / L := by positivity
    have hnonnegQ : 0 ≤ 2 * Q / L := by positivity
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), norm_nonneg a, norm_nonneg b]
  have hbnb : ‖b‖ < n := by
    dsimp only [X] at hXn
    have hnonneg : 0 ≤ 32 * (‖a‖ + ‖b‖) / L := by positivity
    have hnonnegQ : 0 ≤ 2 * Q / L := by positivity
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), norm_nonneg a, norm_nonneg b]
  have ha : ‖a‖ ≤ n + 1 := by
    linarith
  have hb : ‖b‖ ≤ n + 1 := by
    linarith
  refine ⟨n, hn, ha, hb, hN, ?_⟩
  intro k l
  have hrecNorm :
      ‖(recurrentPhase n : ℂ) - (differenceDirection a b hab : ℂ)‖ < 1 / 16 := by
    change dist ((recurrentPhase n : Circle) : ℂ)
      ((differenceDirection a b hab : Circle) : ℂ) < 1 / 16 at hrec
    simpa only [dist_eq_norm] using hrec
  have harcRaw := radialUnit_close_recurrentPhase_of_ne_zero n hn k
  have harcRawOther := radialUnit_close_recurrentPhase_of_ne_zero n hn l
  have harcBound : 8 / (n + 1 : ℝ) < 1 / 16 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
    nlinarith
  have hphase :
      ‖radialUnit n k - (differenceDirection a b hab : ℂ)‖ < 1 / 8 := by
    calc
      ‖radialUnit n k - (differenceDirection a b hab : ℂ)‖ ≤
          ‖radialUnit n k - (recurrentPhase n : ℂ)‖ +
            ‖(recurrentPhase n : ℂ) - (differenceDirection a b hab : ℂ)‖ :=
        by
          rw [show radialUnit n k - (differenceDirection a b hab : ℂ) =
            (radialUnit n k - (recurrentPhase n : ℂ)) +
              ((recurrentPhase n : ℂ) - (differenceDirection a b hab : ℂ)) by ring]
          exact norm_add_le _ _
      _ < 1 / 16 + 1 / 16 := add_lt_add (harcRaw.trans harcBound) hrecNorm
      _ = 1 / 8 := by norm_num
  have herrThreshold : 32 * (‖a‖ + ‖b‖) / L < n := by
    dsimp only [X] at hXn
    have hqnonneg : 0 ≤ 2 * Q / L := by positivity
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), norm_nonneg a, norm_nonneg b]
  have herrMul : 32 * (‖a‖ + ‖b‖) < L * n := by
    have h := (div_lt_iff₀ hL).mp herrThreshold
    nlinarith
  have harcPair : ‖radialUnit n k - radialUnit n l‖ < 16 / (n + 1) := by
    calc
      ‖radialUnit n k - radialUnit n l‖ ≤
          ‖radialUnit n k - (recurrentPhase n : ℂ)‖ +
            ‖(recurrentPhase n : ℂ) - radialUnit n l‖ := by
        rw [show radialUnit n k - radialUnit n l =
          (radialUnit n k - (recurrentPhase n : ℂ)) +
            ((recurrentPhase n : ℂ) - radialUnit n l) by ring]
        exact norm_add_le _ _
      _ < 8 / (n + 1) + 8 / (n + 1) :=
        add_lt_add harcRaw (by rw [norm_sub_rev]; exact harcRawOther)
      _ = 16 / (n + 1) := by ring
  have hcross : ‖b‖ * ‖radialUnit n k - radialUnit n l‖ < L / 2 := by
    by_cases hbzero : ‖b‖ = 0
    · rw [hbzero, zero_mul]
      positivity
    · calc
        ‖b‖ * ‖radialUnit n k - radialUnit n l‖ < ‖b‖ * (16 / (n + 1)) :=
          mul_lt_mul_of_pos_left harcPair (lt_of_le_of_ne (norm_nonneg b) (Ne.symm hbzero))
        _ < L / 2 := by
          rw [show ‖b‖ * (16 / (n + 1 : ℝ)) = (‖b‖ * 16) / (n + 1) by ring]
          apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
          have hbn : 32 * ‖b‖ < L * n := by
            nlinarith [norm_nonneg a, norm_nonneg b]
          nlinarith
  have herror : 4 * (‖a‖ + ‖b‖) / (n + 2) ≤ ‖a - b‖ / 8 := by
    rw [show ‖a - b‖ = L from rfl]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).2
    nlinarith
  have hquadThreshold : 2 * Q / L < n := by
    dsimp only [X] at hXn
    have herrNonneg : 0 ≤ 32 * (‖a‖ + ‖b‖) / L := by positivity
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), norm_nonneg a, norm_nonneg b]
  have hquadMul : 2 * Q < L * n := by
    have h := (div_lt_iff₀ hL).mp hquadThreshold
    nlinarith
  have hDlarge := activeMagnitude_large n hn
  have hquadratic : 16 * (‖a‖ ^ 2 + ‖b‖ ^ 2) / activeMagnitude n < ‖a - b‖ / 2 := by
    rw [show ‖a‖ ^ 2 + ‖b‖ ^ 2 = Q from rfl, show ‖a - b‖ = L from rfl]
    apply (div_lt_iff₀ (activeMagnitude_pos n)).2
    have hn2 : (1 : ℝ) < n + 2 := by
      exact_mod_cast (show 1 < n + 2 by omega)
    nlinarith
  exact localPoint_radial_order n hn k l a b hab ha hb hphase hcross herror hquadratic

private lemma exists_between_finite_families {α β : Type*}
    [Finite α] [Nonempty α] [Finite β] [Nonempty β]
    (f : α → ℝ) (g : β → ℝ) (h : ∀ i j, f i < g j) :
    ∃ r : ℝ, (∀ i, f i < r) ∧ ∀ j, r < g j := by
  classical
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  let sf := (Finset.univ : Finset α).image f
  let sg := (Finset.univ : Finset β).image g
  have hsf : sf.Nonempty := Finset.univ_nonempty.image f
  have hsg : sg.Nonempty := Finset.univ_nonempty.image g
  let A := sf.max' hsf
  let B := sg.min' hsg
  have hAB : A < B := by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (sf.max'_mem hsf)
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (sg.min'_mem hsg)
    dsimp only [A, B]
    rw [← hi, ← hj]
    exact h i j
  refine ⟨(A + B) / 2, ?_, ?_⟩
  · intro i
    have hi : f i ≤ A := by
      exact sf.le_max' (f i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    linarith
  · intro j
    have hj : B ≤ g j := by
      exact sg.min'_le (g j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    linarith

/-! The smaller branches at all roots provide the global localization and
upper-count bound. -/

private noncomputable def generalActiveSlope (n : ℕ) (k : Fin (degree n)) : ℂ :=
  leadingCoefficient (constructionState n) n * (radius n : ℂ) ^ previousDegree n *
    generalIdealSlope n k

private lemma generalActiveSlope_ne_zero (n : ℕ) (k : Fin (degree n)) :
    generalActiveSlope n k ≠ 0 := by
  unfold generalActiveSlope
  exact mul_ne_zero
    (mul_ne_zero (leadingCoefficient_ne_zero_of_valid (constructionState n).2)
      (pow_ne_zero _ (by exact_mod_cast (radius_pos n).ne')))
    (generalIdealSlope_ne_zero n k)

private lemma norm_generalActiveSlope (n : ℕ) (k : Fin (degree n)) :
    ‖generalActiveSlope n k‖ =
      ‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n *
        ‖generalIdealSlope n k‖ := by
  have hR : ‖(radius n : ℂ)‖ = radius n := by
    calc
      ‖(radius n : ℂ)‖ = |radius n| := RCLike.norm_ofReal _
      _ = radius n := abs_of_pos (radius_pos n)
  simp only [generalActiveSlope, norm_mul, norm_pow, hR]

private lemma scaledFunction_zero_general (n : ℕ) (k : Fin (degree n)) :
    scaledFunction n (modelRoot n k) = 0 := by
  let w := modelRoot n k
  have hw : w ≠ 0 := modelRoot_ne_zero n k
  have hstage : stageFunction n ((radius n : ℂ) * w) = 0 := by
    rw [stageFunction_scaled n w hw]
    unfold normalizedValue
    rw [modelBlock_zero n k]
    ring
  change constructedFunction ((radius n : ℂ) * w) = 0
  calc
    constructedFunction ((radius n : ℂ) * w) =
        stageFunction n ((radius n : ℂ) * w) * futureProduct n ((radius n : ℂ) * w) :=
      (constructedFunction_factorization n _).symm
    _ = 0 := by rw [hstage, zero_mul]

private lemma fullNormalizedDerivative_close_general (n : ℕ) (k : Fin (degree n)) {w : ℂ}
    (hw : w ∈ closedBall (modelRoot n k) (globalRadius n)) :
    ‖fullNormalizedDerivative n w + generalIdealSlope n k‖ <
      ‖generalIdealSlope n k‖ / (2 * (n + 2)) := by
  have hwGlobal : w ∈ globalModelSet n := (mem_globalModelSet_iff n w).mpr ⟨k, hw⟩
  have hwExt := globalModelSet_subset_extended n hwGlobal
  have htail := fullNormalizedDerivative_tail_close n hwExt
  have hx : |1 / radius n| < uniformScaleBound (constructionState n) n := by
    rw [abs_of_pos (by positivity [radius_pos n] : 0 < 1 / radius n)]
    exact (radius_admissible n).2.1
  have hscale := normalizedDerivative_scale_close (constructionState n) n hx hwExt
  have hlimit := limitingDerivative_close_global n k hw
  have hmargin := derivativeMargin_lt_global n k
  have hrewrite : fullNormalizedDerivative n w + generalIdealSlope n k =
      (fullNormalizedDerivative n w -
          normalizedDerivative (constructionState n) n (1 / radius n) w) +
        (normalizedDerivative (constructionState n) n (1 / radius n) w -
          limitingDerivative n w) +
        (limitingDerivative n w + generalIdealSlope n k) := by ring
  rw [hrewrite]
  calc
    ‖(fullNormalizedDerivative n w -
          normalizedDerivative (constructionState n) n (1 / radius n) w) +
        (normalizedDerivative (constructionState n) n (1 / radius n) w -
          limitingDerivative n w) +
        (limitingDerivative n w + generalIdealSlope n k)‖ ≤
      ‖fullNormalizedDerivative n w -
          normalizedDerivative (constructionState n) n (1 / radius n) w‖ +
        ‖normalizedDerivative (constructionState n) n (1 / radius n) w -
          limitingDerivative n w‖ +
        ‖limitingDerivative n w + generalIdealSlope n k‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ < derivativeMargin n + derivativeMargin n +
        ‖generalIdealSlope n k‖ / (8 * (n + 2)) := by
      exact add_lt_add (add_lt_add htail hscale) hlimit
    _ < ‖generalIdealSlope n k‖ / (2 * (n + 2)) := by
      have hpiece : 0 < ‖generalIdealSlope n k‖ / (8 * (n + 2)) := by
        positivity [generalIdealSlope_ne_zero n k]
      have htarget : ‖generalIdealSlope n k‖ / (2 * (n + 2)) =
          4 * (‖generalIdealSlope n k‖ / (8 * (n + 2))) := by
        field_simp ; ring
      rw [htarget]
      linarith

private lemma scaledFunction_deriv_close_general (n : ℕ) (hn : n ≠ 0)
    (k : Fin (degree n)) {w : ℂ}
    (hw : w ∈ closedBall (modelRoot n k) (globalRadius n)) :
    ‖deriv (scaledFunction n) w + generalActiveSlope n k‖ <
      (localError n : ℝ) * ‖generalActiveSlope n k‖ := by
  let A : ℂ := leadingCoefficient (constructionState n) n *
    (radius n : ℂ) ^ previousDegree n
  have hwGlobal : w ∈ globalModelSet n := (mem_globalModelSet_iff n w).mpr ⟨k, hw⟩
  rw [deriv_scaledFunction n hn (globalModelSet_subset_extended n hwGlobal)]
  change ‖A * fullNormalizedDerivative n w + A * generalIdealSlope n k‖ <
    (localError n : ℝ) * ‖A * generalIdealSlope n k‖
  rw [← mul_add, localError_coe]
  rw [norm_mul A (fullNormalizedDerivative n w + generalIdealSlope n k),
    norm_mul A (generalIdealSlope n k)]
  have hA : 0 < ‖A‖ := norm_pos_iff.mpr (mul_ne_zero
    (leadingCoefficient_ne_zero_of_valid (constructionState n).2)
    (pow_ne_zero _ (by exact_mod_cast (radius_pos n).ne')))
  have hclose := fullNormalizedDerivative_close_general n k hw
  calc
    ‖A‖ * ‖fullNormalizedDerivative n w + generalIdealSlope n k‖ <
        ‖A‖ * (‖generalIdealSlope n k‖ / (2 * ((n : ℝ) + 2))) :=
      mul_lt_mul_of_pos_left hclose hA
    _ = 1 / (2 * ((n : ℝ) + 2)) * (‖A‖ * ‖generalIdealSlope n k‖) := by ring

private lemma global_target_admissible (n : ℕ) (hn : n ≠ 0) (k : Fin (degree n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    ‖a / generalActiveSlope n k‖ ≤
      (1 - (localError n : ℝ)) * globalRadius n := by
  let X : ℝ := ‖leadingCoefficient (constructionState n) n‖ *
    radius n ^ previousDegree n
  let I : ℝ := ‖generalIdealSlope n k‖
  let d : ℝ := globalRadius n
  let x : ℝ := (n : ℝ) + 2
  have hX : 0 < X := by
    dsimp only [X]
    positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2, radius_pos n]
  have hI : 0 < I := by
    dsimp only [I]
    positivity [generalIdealSlope_ne_zero n k]
  have hd : 0 < d := globalRadius_pos n
  have hx : 0 < x := by dsimp only [x]; positivity
  have hcapacity := (radius_admissible n).2.2.2.2.2.2.1 hn
  have hmargin := derivativeMargin_lt_global n k
  have hstrong : (n + 1 : ℝ) < X * (I / (8 * x)) * d := by
    apply hcapacity.trans
    dsimp only [X, I, d, x] at hmargin ⊢
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hmargin (by
      positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2,
        radius_pos n])) (globalRadius_pos n)
  have hratio : 1 / (8 * x) < 1 - 1 / (2 * x) := by
    rw [div_lt_iff₀ (by positivity : 0 < 8 * x)]
    field_simp
    nlinarith
  have hsmall : ‖a‖ < X * I * ((1 - 1 / (2 * x)) * d) := by
    calc
      ‖a‖ ≤ (n + 1 : ℝ) := ha
      _ < X * (I / (8 * x)) * d := hstrong
      _ = X * I * ((1 / (8 * x)) * d) := by ring
      _ < X * I * ((1 - 1 / (2 * x)) * d) := by gcongr
  rw [norm_div]
  have hC : 0 < ‖generalActiveSlope n k‖ :=
    norm_pos_iff.mpr (generalActiveSlope_ne_zero n k)
  apply (div_le_iff₀ hC).2
  rw [norm_generalActiveSlope]
  change ‖a‖ ≤ (1 - 1 / (2 * x)) * d * (X * I)
  nlinarith [hsmall]

private lemma existsUnique_globalPoint (n : ℕ) (hn : n ≠ 0) (k : Fin (degree n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    ∃! w : ℂ, w ∈ closedBall (modelRoot n k) (globalRadius n) ∧
      scaledFunction n w = a := by
  apply quantitative_local_inverse (scaledFunction n) (differentiable_scaledFunction n)
    (modelRoot n k) (generalActiveSlope n k) a (globalRadius n) (localError n)
  · exact globalRadius_pos n
  · exact localError_lt_one n
  · exact generalActiveSlope_ne_zero n k
  · exact scaledFunction_zero_general n k
  · exact fun w hw ↦ (scaledFunction_deriv_close_general n hn k hw).le
  · exact global_target_admissible n hn k a ha

private lemma localPoint_mem_global (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    localPoint n hn k a ha ∈
      closedBall (modelRoot n (innerIndex n k)) (globalRadius n) := by
  obtain ⟨w, hw, -⟩ := existsUnique_globalPoint n hn (innerIndex n k) a ha
  have hwAffine : w ∈ closedBall (modelRoot n (innerIndex n k)) (affineRadius n) := by
    apply mem_closedBall.mpr
    exact (mem_closedBall.mp hw.1).trans (globalRadius_lt_affineRadius n).le
  have heq : w = localPoint n hn k a ha := by
    apply (Classical.choose_spec (existsUnique_localPoint n hn k a ha)).2
    exact ⟨hwAffine, hw.2⟩
  simpa [← heq] using hw.1

private lemma scaledFunction_deriv_ne_zero_on_global (n : ℕ) (hn : n ≠ 0)
    (k : Fin (degree n)) {w : ℂ}
    (hw : w ∈ closedBall (modelRoot n k) (globalRadius n)) :
    deriv (scaledFunction n) w ≠ 0 := by
  intro hz
  have hclose := scaledFunction_deriv_close_general n hn k hw
  rw [hz, zero_add] at hclose
  have hq : (localError n : ℝ) < 1 := by exact_mod_cast localError_lt_one n
  have hC : 0 < ‖generalActiveSlope n k‖ :=
    norm_pos_iff.mpr (generalActiveSlope_ne_zero n k)
  nlinarith

private lemma global_solution_unique (n : ℕ) (hn : n ≠ 0) (k : Fin (degree n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) {w₁ w₂ : ℂ}
    (hw₁ : w₁ ∈ closedBall (modelRoot n k) (globalRadius n))
    (hw₂ : w₂ ∈ closedBall (modelRoot n k) (globalRadius n))
    (h₁ : scaledFunction n w₁ = a) (h₂ : scaledFunction n w₂ = a) : w₁ = w₂ := by
  exact (existsUnique_globalPoint n hn k a ha).unique ⟨hw₁, h₁⟩ ⟨hw₂, h₂⟩

/-! ## Escape estimates and global localization -/

private lemma futureProduct_norm_gt_half (n : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ actualTailControl n) : 1 / 2 < ‖futureProduct n z‖ := by
  have hclose := futureProduct_close_to_one n z hz
  have htri : (1 : ℝ) ≤ ‖futureProduct n z - 1‖ + ‖futureProduct n z‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖(1 - futureProduct n z) + futureProduct n z‖ := by ring_nf
      _ ≤ ‖1 - futureProduct n z‖ + ‖futureProduct n z‖ := norm_add_le _ _
      _ = ‖futureProduct n z - 1‖ + ‖futureProduct n z‖ := by rw [norm_sub_rev]
  linarith [tailTolerance_lt_half n]

private lemma normalizedValue_norm_ge_escape_half (n : ℕ) {w : ℂ}
    (hw : w ∈ escapeModelSet n) :
    escapeMinimum n / 2 <
      ‖normalizedValue (constructionState n) n (1 / radius n) w‖ := by
  have hx : |1 / radius n| < uniformScaleBound (constructionState n) n := by
    rw [abs_of_pos (by positivity [radius_pos n] : 0 < 1 / radius n)]
    exact (radius_admissible n).2.1
  have hclose := normalizedValue_shell_close (constructionState n) n hx hw.1
  have hlimit := escapeMinimum_le n hw
  have htri := norm_le_norm_add_norm_sub' (limitingValue n w)
    (normalizedValue (constructionState n) n (1 / radius n) w)
  rw [norm_sub_rev] at htri
  nlinarith

private lemma scaledFunction_norm_gt_on_escape (n : ℕ) (hn : n ≠ 0) {w : ℂ}
    (hw : w ∈ escapeModelSet n) :
    (n + 1 : ℝ) < ‖scaledFunction n w‖ := by
  let A := leadingCoefficient (constructionState n) n
  let R := radius n
  let NV := normalizedValue (constructionState n) n (1 / radius n) w
  let P := futureProduct n ((radius n : ℂ) * w)
  have hw0 : w ≠ 0 := modelAnnulus_nonzero hw.1
  have hfactor : scaledFunction n w = A * (R : ℂ) ^ previousDegree n * NV * P := by
    change constructedFunction ((radius n : ℂ) * w) = _
    rw [← constructedFunction_factorization n]
    change stageFunction n ((radius n : ℂ) * w) *
      futureProduct n ((radius n : ℂ) * w) = _
    rw [stageFunction_scaled n w hw0]
  have hwNorm : ‖w‖ ≤ 4 := by
    simpa [mem_closedBall, dist_zero_left] using hw.1.1
  have hRnorm : ‖(R : ℂ)‖ = R := by
    dsimp only [R]
    calc
      ‖(radius n : ℂ)‖ = |radius n| := RCLike.norm_ofReal _
      _ = radius n := abs_of_pos (radius_pos n)
  have hzTail : ‖(radius n : ℂ) * w‖ ≤ actualTailControl n := by
    rw [norm_mul, hRnorm]
    rw [actualTailControl]
    nlinarith [modelBound_pos n, radius_pos n]
  have hP : 1 / 2 < ‖P‖ := futureProduct_norm_gt_half n _ hzTail
  have hNV : escapeMinimum n / 2 < ‖NV‖ := normalizedValue_norm_ge_escape_half n hw
  have hcapacity := (radius_admissible n).2.2.2.2.2.2.2.1 hn
  rw [hfactor, norm_mul, norm_mul, norm_mul, norm_pow, hRnorm]
  dsimp only [A, R, NV, P] at hcapacity ⊢
  have hnonneg : 0 ≤ ‖leadingCoefficient (constructionState n) n‖ *
      radius n ^ previousDegree n :=
    mul_nonneg (norm_nonneg _) (pow_nonneg (radius_pos n).le _)
  have hQpos : 0 < ‖leadingCoefficient (constructionState n) n‖ *
      radius n ^ previousDegree n := by
    positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2, radius_pos n]
  have hNVpos : 0 < ‖normalizedValue (constructionState n) n (1 / radius n) w‖ :=
    (by positivity [escapeMinimum_pos n] : 0 < escapeMinimum n / 2).trans hNV
  have hprod : escapeMinimum n / 4 <
      ‖normalizedValue (constructionState n) n (1 / radius n) w‖ *
        ‖futureProduct n ((radius n : ℂ) * w)‖ := by
    calc
      escapeMinimum n / 4 = (escapeMinimum n / 2) * (1 / 2) := by ring
      _ < ‖normalizedValue (constructionState n) n (1 / radius n) w‖ * (1 / 2) :=
        mul_lt_mul_of_pos_right hNV (by norm_num)
      _ < ‖normalizedValue (constructionState n) n (1 / radius n) w‖ *
          ‖futureProduct n ((radius n : ℂ) * w)‖ :=
        mul_lt_mul_of_pos_left hP hNVpos
  have hscaled := mul_lt_mul_of_pos_left hprod hQpos
  have hbase : (n + 1 : ℝ) <
      (‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n) *
        (escapeMinimum n / 4) := by
    nlinarith
  calc
    (n + 1 : ℝ) <
        (‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n) *
          (escapeMinimum n / 4) := hbase
    _ < (‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n) *
          (‖normalizedValue (constructionState n) n (1 / radius n) w‖ *
            ‖futureProduct n ((radius n : ℂ) * w)‖) := hscaled
    _ = ‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n *
          ‖normalizedValue (constructionState n) n (1 / radius n) w‖ *
            ‖futureProduct n ((radius n : ℂ) * w)‖ := by ring

private lemma radius_le_of_le {i n : ℕ} (hin : i ≤ n) : radius i ≤ radius n := by
  rcases hin.eq_or_lt with rfl | hin
  · exact le_rfl
  · have hsep := (radius_admissible n).2.2.2.1 i hin
    rw [constructionState_radius_stable hin, abs_of_pos (radius_pos i)] at hsep
    linarith [radius_pos i]

private lemma radialScale_lt_two (n : ℕ) (k : Fin (degree n)) :
    radialScale n (delta n) k < 2 := by
  simp only [radialScale]
  split_ifs
  · norm_num
  · exact delta_lt_two n

private lemma norm_actualRoot_lt_two_mul_radius_of_le {i n : ℕ} (hin : i ≤ n)
    (k : Fin (degree i)) : ‖actualRoot i k‖ < 2 * radius n := by
  rw [norm_actualRoot]
  calc
    radius i * radialScale i (delta i) k < radius i * 2 :=
      mul_lt_mul_of_pos_left (radialScale_lt_two i k) (radius_pos i)
    _ ≤ radius n * 2 := by gcongr; exact radius_le_of_le hin
    _ = 2 * radius n := by ring

private lemma half_le_norm_one_sub_actual_div (n : ℕ) {z : ℂ}
    (hz : 4 * radius n ≤ ‖z‖) (i : PreviousIndex (n + 1)) :
    1 / 2 ≤ ‖1 - actualRoot i.1 i.2 / z‖ := by
  have hroot : ‖actualRoot i.1 i.2‖ < 2 * radius n :=
    norm_actualRoot_lt_two_mul_radius_of_le (Nat.le_of_lt_succ i.1.isLt) i.2
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity [radius_pos n]) hz
  have hquot : ‖actualRoot i.1 i.2 / z‖ < 1 / 2 := by
    rw [norm_div]
    apply (div_lt_iff₀ hzpos).2
    nlinarith [radius_pos n]
  have hrev := norm_sub_norm_le (1 : ℂ) (actualRoot i.1 i.2 / z)
  norm_num only [norm_one] at hrev
  linarith

private lemma norm_gap_correction_ge (n : ℕ) {z : ℂ}
    (hlow : 4 * radius n ≤ ‖z‖) :
    (1 / 2 : ℝ) ^ previousDegree (n + 1) ≤
      ‖correction (constructionState (n + 1)) (n + 1) (1 / radius (n + 1))
        (z / radius (n + 1))‖ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt
    (lt_of_lt_of_le (by positivity [radius_pos n]) hlow))
  have hR0 : (radius (n + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (radius_pos (n + 1)).ne'
  rw [correction_constructionState, norm_prod]
  have hfactor (i : PreviousIndex (n + 1)) :
      ((1 / radius (n + 1) : ℝ) : ℂ) * actualRoot i.1 i.2 /
          (z / radius (n + 1)) = actualRoot i.1 i.2 / z := by
    push_cast
    field_simp [hR0, hz0]
  simp_rw [hfactor]
  rw [show previousDegree (n + 1) = Fintype.card (PreviousIndex (n + 1)) by
    simpa using (card_previousIndex (n + 1)).symm]
  have hconst : (1 / 2 : ℝ) ^ Fintype.card (PreviousIndex (n + 1)) =
      ∏ _ : PreviousIndex (n + 1), (1 / 2 : ℝ) := by simp
  rw [hconst]
  exact Finset.prod_le_prod (fun _ _ ↦ by norm_num) (fun i _ ↦
    half_le_norm_one_sub_actual_div n hlow i)

private lemma gap_algebra (n : ℕ) :
    (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n *
          (4 * radius n) ^ previousDegree (n + 1) *
        (1 / 2 : ℝ) ^ previousDegree (n + 1) =
      radius n ^ previousDegree n * gapConstant n := by
  have hcombine : (4 * radius n) ^ previousDegree (n + 1) *
      (1 / 2 : ℝ) ^ previousDegree (n + 1) =
      (2 * radius n) ^ previousDegree (n + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n *
          (4 * radius n) ^ previousDegree (n + 1) *
        (1 / 2 : ℝ) ^ previousDegree (n + 1) =
      (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n *
        ((4 * radius n) ^ previousDegree (n + 1) *
          (1 / 2 : ℝ) ^ previousDegree (n + 1)) := by ring
    _ = (radius n ^ degree n)⁻¹ * modelLeadingMagnitude n *
        (2 * radius n) ^ previousDegree (n + 1) := by rw [hcombine]
    _ = radius n ^ previousDegree n * gapConstant n := by
      rw [previousDegree_succ, gapConstant, pow_add, mul_pow, mul_pow, pow_add]
      have hR : radius n ≠ 0 := (radius_pos n).ne'
      field_simp [hR]

private lemma scaledFunction_norm_gt_on_gap (n : ℕ) (hn : n ≠ 0) {z : ℂ}
    (hlow : 4 * radius n ≤ ‖z‖)
    (hupp : ‖z‖ ≤ radius (n + 1) / 2) :
    (n + 1 : ℝ) < ‖constructedFunction z‖ := by
  let N := previousDegree (n + 1)
  let R := radius (n + 1)
  let w : ℂ := z / R
  let A := leadingCoefficient (constructionState (n + 1)) (n + 1)
  let Corr := correction (constructionState (n + 1)) (n + 1) (1 / R) w
  let B := modelBlock (n + 1) w
  let P := futureProduct (n + 1) z
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt
    (lt_of_lt_of_le (by positivity [radius_pos n]) hlow))
  have hRpos : 0 < R := radius_pos (n + 1)
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hw0 : w ≠ 0 := div_ne_zero hz0 hR0
  have hRw : (R : ℂ) * w = z := by
    dsimp only [w]
    field_simp [hR0]
  have hfactor : constructedFunction z = A * (R : ℂ) ^ N * (w ^ N * Corr * B) * P := by
    rw [← hRw]
    rw [← constructedFunction_factorization (n + 1)]
    change stageFunction (n + 1) ((R : ℂ) * w) *
      futureProduct (n + 1) ((R : ℂ) * w) = _
    rw [stageFunction_scaled (n + 1) w hw0]
    simp only [normalizedValue]
    rw [hRw]
  have hwNorm : ‖w‖ ≤ 1 / 2 := by
    dsimp only [w, R]
    rw [norm_div]
    have hRnorm : ‖(radius (n + 1) : ℂ)‖ = radius (n + 1) := by
      calc
        ‖(radius (n + 1) : ℂ)‖ = |radius (n + 1)| := RCLike.norm_ofReal _
        _ = radius (n + 1) := abs_of_pos (radius_pos (n + 1))
    rw [hRnorm]
    exact (div_le_iff₀ (radius_pos (n + 1))).2 (by nlinarith)
  have hwBall : w ∈ closedBall (0 : ℂ) (1 / 2) := by
    simpa [mem_closedBall, dist_zero_left] using hwNorm
  have hB : insideMinimum (n + 1) ≤ ‖B‖ := insideMinimum_le (n + 1) hwBall
  have hCorr : (1 / 2 : ℝ) ^ N ≤ ‖Corr‖ := by
    dsimp only [N, Corr, R, w]
    exact norm_gap_correction_ge n hlow
  have hRnorm : ‖(R : ℂ)‖ = R := by
    dsimp only [R]
    calc
      ‖(radius (n + 1) : ℂ)‖ = |radius (n + 1)| := RCLike.norm_ofReal _
      _ = radius (n + 1) := abs_of_pos (radius_pos (n + 1))
  have hwNormEq : ‖w‖ = ‖z‖ / R := by
    dsimp only [w]
    rw [norm_div, hRnorm]
  have hzTail : ‖z‖ ≤ actualTailControl (n + 1) := by
    rw [actualTailControl]
    nlinarith [modelBound_pos (n + 1), radius_pos (n + 1)]
  have hP : 1 / 2 < ‖P‖ := futureProduct_norm_gt_half (n + 1) z hzTail
  have hAeq := norm_leadingCoefficient_succ n
  have hpow : (4 * radius n) ^ N ≤ ‖z‖ ^ N := by
    exact pow_le_pow_left₀ (by positivity [radius_pos n]) hlow N
  have hnormalized :
      (‖z‖ / R) ^ N * (1 / 2 : ℝ) ^ N * insideMinimum (n + 1) ≤
        ‖w ^ N * Corr * B‖ := by
    rw [norm_mul, norm_mul, norm_pow, hwNormEq]
    have hc : (‖z‖ / R) ^ N * (1 / 2 : ℝ) ^ N ≤
        (‖z‖ / R) ^ N * ‖Corr‖ :=
      mul_le_mul_of_nonneg_left hCorr (pow_nonneg (by positivity) _)
    exact mul_le_mul hc hB (insideMinimum_pos (n + 1)).le
      (mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg Corr))
  have hprefix :
      ‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n *
          gapConstant n * insideMinimum (n + 1) ≤
        ‖A‖ * R ^ N * ‖w ^ N * Corr * B‖ := by
    calc
      ‖leadingCoefficient (constructionState n) n‖ * radius n ^ previousDegree n *
          gapConstant n * insideMinimum (n + 1) =
        (‖leadingCoefficient (constructionState n) n‖ *
          ((radius n ^ degree n)⁻¹ * modelLeadingMagnitude n)) *
          (4 * radius n) ^ N * (1 / 2 : ℝ) ^ N * insideMinimum (n + 1) := by
            have hg := gap_algebra n
            dsimp only [N]
            calc
              ‖leadingCoefficient (constructionState n) n‖ *
                    radius n ^ previousDegree n * gapConstant n * insideMinimum (n + 1) =
                  ‖leadingCoefficient (constructionState n) n‖ *
                    (radius n ^ previousDegree n * gapConstant n) *
                      insideMinimum (n + 1) := by ring
              _ = ‖leadingCoefficient (constructionState n) n‖ *
                    ((radius n ^ degree n)⁻¹ * modelLeadingMagnitude n *
                      (4 * radius n) ^ previousDegree (n + 1) *
                      (1 / 2 : ℝ) ^ previousDegree (n + 1)) *
                      insideMinimum (n + 1) := by rw [hg]
              _ = _ := by ring
      _ = ‖A‖ * (4 * radius n) ^ N * (1 / 2 : ℝ) ^ N *
          insideMinimum (n + 1) := by rw [hAeq]; ring
      _ ≤ ‖A‖ * ‖z‖ ^ N * (1 / 2 : ℝ) ^ N * insideMinimum (n + 1) := by
        gcongr ; positivity [insideMinimum_pos (n + 1)]
      _ = ‖A‖ * R ^ N *
          ((‖z‖ / R) ^ N * (1 / 2 : ℝ) ^ N * insideMinimum (n + 1)) := by
        have hcancel : R ^ N * (‖z‖ / R) ^ N = ‖z‖ ^ N := by
          rw [← mul_pow]
          congr 1
          field_simp [hRpos.ne']
        rw [← hcancel]
        ring
      _ ≤ ‖A‖ * R ^ N * ‖w ^ N * Corr * B‖ := by gcongr
  have hcapacity := (radius_admissible n).2.2.2.2.2.2.2.2 hn
  rw [hfactor, norm_mul, norm_mul, norm_mul, norm_pow, hRnorm]
  have hprefixPos : 0 < ‖A‖ * R ^ N * ‖w ^ N * Corr * B‖ := by
    have hbasePos : 0 < ‖leadingCoefficient (constructionState n) n‖ *
        radius n ^ previousDegree n * gapConstant n * insideMinimum (n + 1) := by
      positivity [leadingCoefficient_ne_zero_of_valid (constructionState n).2,
        radius_pos n, gapConstant_pos n, insideMinimum_pos (n + 1)]
    exact hbasePos.trans_le hprefix
  have hfinal :
      ‖A‖ * R ^ N * ‖w ^ N * Corr * B‖ * (1 / 2) <
        ‖A‖ * R ^ N * ‖w ^ N * Corr * B‖ * ‖P‖ :=
    mul_lt_mul_of_pos_left hP hprefixPos
  dsimp only [A, R, N, P] at hprefix hcapacity hfinal ⊢
  nlinarith

private lemma solution_localizes_between (N n : ℕ) (hN0 : N ≠ 0) (hNn : N ≤ n)
    (a : ℂ) (ha : ‖a‖ ≤ N + 1) {z : ℂ}
    (hzValue : constructedFunction z = a)
    (hzLow : 4 * radius N ≤ ‖z‖) (hzHigh : ‖z‖ < 4 * radius n) :
    ∃ i : ℕ, N < i ∧ i ≤ n ∧ ∃ k : Fin (degree i),
      z / radius i ∈ ball (modelRoot i k) (globalRadius i) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hNlt : N < n + 1
      · have hNle : N ≤ n := by omega
        by_cases hzPrev : ‖z‖ < 4 * radius n
        · obtain ⟨i, hiN, hin, k, hk⟩ := ih hNle hzPrev
          exact ⟨i, hiN, hin.trans (Nat.le_succ n), k, hk⟩
        · have hzPrevLow : 4 * radius n ≤ ‖z‖ := le_of_not_gt hzPrev
          have hn0 : n ≠ 0 := by omega
          by_cases hzHalf : ‖z‖ ≤ radius (n + 1) / 2
          · have hgap := scaledFunction_norm_gt_on_gap n hn0 hzPrevLow hzHalf
            rw [hzValue] at hgap
            have ha' : ‖a‖ ≤ n + 1 := by
              calc
                ‖a‖ ≤ (N + 1 : ℝ) := ha
                _ ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hNle 1
            linarith
          · let R := radius (n + 1)
            let w : ℂ := z / R
            have hR : 0 < R := radius_pos (n + 1)
            have hRnorm : ‖(R : ℂ)‖ = R := by
              calc
                ‖(R : ℂ)‖ = |R| := RCLike.norm_ofReal _
                _ = R := abs_of_pos hR
            have hwNorm : ‖w‖ = ‖z‖ / R := by
              dsimp only [w]
              rw [norm_div, hRnorm]
            have hwUpper : ‖w‖ ≤ 4 := by
              rw [hwNorm]
              apply (div_le_iff₀ hR).2
              exact hzHigh.le
            have hwLower : 1 / 4 ≤ ‖w‖ := by
              rw [hwNorm]
              have hzHalf' : R / 2 < ‖z‖ := lt_of_not_ge hzHalf
              apply (le_div_iff₀ hR).2
              nlinarith
            have hwAnnulus : w ∈ modelAnnulus := by
              constructor
              · simpa [mem_closedBall, dist_zero_left] using hwUpper
              · intro hwBall
                have : ‖w‖ < 1 / 4 := by
                  simpa [mem_ball, dist_zero_right] using hwBall
                linarith
            have hRw : (R : ℂ) * w = z := by
              dsimp only [w]
              field_simp [show (R : ℂ) ≠ 0 by exact_mod_cast hR.ne']
            have hwValue : scaledFunction (n + 1) w = a := by
              change constructedFunction ((radius (n + 1) : ℂ) * w) = a
              simpa only [R] using hRw.symm ▸ hzValue
            have hwExceptional : w ∈ exceptionalModelSet (n + 1) := by
              by_contra hwNot
              have hescape := scaledFunction_norm_gt_on_escape (n + 1) (by omega)
                ⟨hwAnnulus, hwNot⟩
              rw [hwValue] at hescape
              norm_num only [Nat.cast_add, Nat.cast_one] at hescape
              have ha' : ‖a‖ ≤ n + 2 := by
                calc
                  ‖a‖ ≤ (N + 1 : ℝ) := ha
                  _ ≤ (n + 2 : ℝ) := by
                    exact_mod_cast Nat.add_le_add_right (show N ≤ n + 1 by omega) 1
              linarith
            obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hwExceptional
            exact ⟨n + 1, hNlt, le_rfl, k, hk⟩
      · have hNeq : N = n + 1 := by omega
        subst N
        linarith

/-- The multiplicity-weighted number of solutions of `f z = a` in the open
disc `‖z‖ < r`.  For an entire nonconstant function the divisor has finite
support, so this is the ordinary finite sum of analytic multiplicities. -/
noncomputable def aPointCount (f : ℂ → ℂ) (r : ℝ) (a : ℂ) : ℕ :=
  ∑ᶠ z : ℂ,
    Int.toNat (MeromorphicOn.divisor (fun w ↦ f w - a) (ball 0 r) z)

/-- Division-free form of `limsup (n(r,a)/n(r,b)) = ∞`. -/
def UnboundedCountRatio (f : ℂ → ℂ) (a b : ℂ) : Prop :=
  ∀ M : ℕ, ∀ R : ℝ, ∃ r : ℝ, R < r ∧
    0 < aPointCount f r b ∧
      M * aPointCount f r b < aPointCount f r a

private lemma analytic_sub_const {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    AnalyticOnNhd ℂ (fun z ↦ f z - a) univ := by
  exact Complex.analyticOnNhd_univ_iff_differentiable.2
    (hf.sub (differentiable_const (𝕜 := ℂ) (E := ℂ) a))

private lemma aPoint_divisor_support_finite {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (r : ℝ) (a : ℂ) :
    (MeromorphicOn.divisor (fun z ↦ f z - a) (ball 0 r)).support.Finite := by
  apply MeromorphicOn.divisor_ball_support_finite
  exact fun z _ ↦ (analytic_sub_const hf a).meromorphicOn z (mem_univ z)

private lemma aPoint_divisor_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (r : ℝ) (a : ℂ) :
    0 ≤ MeromorphicOn.divisor (fun z ↦ f z - a) (ball 0 r) := by
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    ((analytic_sub_const hf a).mono (Set.subset_univ (ball (0 : ℂ) r)))

private noncomputable def constructedSupport (r : ℝ) (a : ℂ) : Finset ℂ :=
  (aPoint_divisor_support_finite differentiable_constructedFunction r a).toFinset

private lemma mem_constructedSupport_iff (r : ℝ) (a z : ℂ) :
    z ∈ constructedSupport r a ↔
      MeromorphicOn.divisor (fun w ↦ constructedFunction w - a) (ball 0 r) z ≠ 0 := by
  simp [constructedSupport, Function.mem_support]

private lemma aPointCount_constructed_eq_sum (r : ℝ) (a : ℂ) :
    aPointCount constructedFunction r a =
      ∑ z ∈ constructedSupport r a,
        Int.toNat (MeromorphicOn.divisor
          (fun w ↦ constructedFunction w - a) (ball 0 r) z) := by
  unfold aPointCount
  apply finsum_eq_sum_of_support_subset
  intro z hz
  change z ∈ constructedSupport r a
  apply (mem_constructedSupport_iff r a z).mpr
  intro hzero
  simp [hzero] at hz

private lemma constructedSupport_mem_ball {r : ℝ} {a z : ℂ}
    (hz : z ∈ constructedSupport r a) : z ∈ ball 0 r := by
  have hsupport : z ∈ (MeromorphicOn.divisor
      (fun w ↦ constructedFunction w - a) (ball 0 r)).support := by
    simpa [Function.mem_support] using (mem_constructedSupport_iff r a z).mp hz
  exact (MeromorphicOn.divisor
    (fun w ↦ constructedFunction w - a) (ball 0 r)).supportWithinDomain hsupport

private lemma constructedSupport_value {r : ℝ} {a z : ℂ}
    (hz : z ∈ constructedSupport r a) : constructedFunction z = a := by
  have hzBall := constructedSupport_mem_ball hz
  have hne := (mem_constructedSupport_iff r a z).mp hz
  have han := analytic_sub_const differentiable_constructedFunction a
  have hanBall := han.mono (Set.subset_univ (ball (0 : ℂ) r))
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanBall hzBall] at hne
  by_contra hvalue
  have horder : analyticOrderAt (fun w ↦ constructedFunction w - a) z = 0 :=
    (han z (mem_univ z)).analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hvalue)
  rw [horder] at hne
  simp at hne

private lemma constructed_divisor_eq_one {r : ℝ} {a z : ℂ}
    (hzBall : z ∈ ball (0 : ℂ) r) (hzValue : constructedFunction z = a)
    (hzDeriv : deriv constructedFunction z ≠ 0) :
    MeromorphicOn.divisor (fun w ↦ constructedFunction w - a) (ball 0 r) z = 1 := by
  have han := analytic_sub_const differentiable_constructedFunction a
  have hAt := han z (mem_univ z)
  have hzero : (fun w ↦ constructedFunction w - a) z = 0 := by simp [hzValue]
  have hderiv : deriv (fun w ↦ constructedFunction w - a) z ≠ 0 := by
    simpa only [deriv_sub_const] using hzDeriv
  have horder := hAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
  have hanBall := han.mono (Set.subset_univ (ball (0 : ℂ) r))
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanBall hzBall, horder]
  rfl

private lemma deriv_scaledFunction_eq (n : ℕ) (w : ℂ) :
    deriv (scaledFunction n) w =
      (radius n : ℂ) * deriv constructedFunction ((radius n : ℂ) * w) := by
  change deriv (fun u ↦ constructedFunction ((radius n : ℂ) * u)) w = _
  rw [deriv_comp_mul_left]
  rfl

private lemma localPoint_actual_value (n : ℕ) (hn : n ≠ 0) (k : Fin (t n))
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    constructedFunction ((radius n : ℂ) * localPoint n hn k a ha) = a := by
  exact localPoint_value n hn k a ha

private lemma localPoint_actual_deriv_ne_zero (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    deriv constructedFunction ((radius n : ℂ) * localPoint n hn k a ha) ≠ 0 := by
  have hw := localPoint_mem_global n hn k a ha
  have hscaled := scaledFunction_deriv_ne_zero_on_global n hn (innerIndex n k) hw
  intro hzero
  apply hscaled
  rw [deriv_scaledFunction_eq, hzero, mul_zero]

private lemma localPoint_injective (n : ℕ) (hn : n ≠ 0) (a : ℂ)
    (ha : ‖a‖ ≤ n + 1) :
    Function.Injective (fun k : Fin (t n) ↦ localPoint n hn k a ha) := by
  intro k l hkl
  change localPoint n hn k a ha = localPoint n hn l a ha at hkl
  by_contra hne
  have hk := localPoint_mem n hn k a ha
  have hl := localPoint_mem n hn l a ha
  have hcenters :
      dist (modelRoot n (innerIndex n k)) (modelRoot n (innerIndex n l)) ≤
        2 * affineRadius n := by
    calc
      dist (modelRoot n (innerIndex n k)) (modelRoot n (innerIndex n l)) ≤
          dist (modelRoot n (innerIndex n k)) (localPoint n hn k a ha) +
            dist (localPoint n hn k a ha) (modelRoot n (innerIndex n l)) :=
        dist_triangle _ _ _
      _ ≤ affineRadius n + affineRadius n := by
        apply add_le_add
        · simpa only [dist_comm] using mem_closedBall.mp hk
        · calc
            dist (localPoint n hn k a ha) (modelRoot n (innerIndex n l)) =
                dist (localPoint n hn l a ha) (modelRoot n (innerIndex n l)) := by rw [hkl]
            _ ≤ affineRadius n := mem_closedBall.mp hl
      _ = 2 * affineRadius n := by ring
  have hindex : innerIndex n k ≠ innerIndex n l := by
    intro h
    apply hne
    apply Fin.ext
    simpa using congrArg Fin.val h
  have hsep := modelRoot_separated n (innerIndex n k) (innerIndex n l) hindex
  have haff := affineRadius_lt_quarter n
  have haffModel : affineRadius n < modelRadius n :=
    (affineRadius_lt_localRadius n).trans (localRadius_lt_modelRadius n)
  nlinarith [modelRadius_pos n]

private lemma actualLocalPoint_injective (n : ℕ) (hn : n ≠ 0) (a : ℂ)
    (ha : ‖a‖ ≤ n + 1) :
    Function.Injective
      (fun k : Fin (t n) ↦ (radius n : ℂ) * localPoint n hn k a ha) := by
  intro k l h
  apply localPoint_injective n hn a ha
  exact mul_left_cancel₀ (by exact_mod_cast (radius_pos n).ne') h

private lemma t_le_aPointCount_at_separating_radius (n : ℕ) (hn : n ≠ 0)
    (a : ℂ) (ha : ‖a‖ ≤ n + 1) (ρ : ℝ)
    (hρ : ∀ k : Fin (t n), ‖localPoint n hn k a ha‖ < ρ) :
    t n ≤ aPointCount constructedFunction (radius n * ρ) a := by
  classical
  let p : Fin (t n) → ℂ :=
    fun k ↦ (radius n : ℂ) * localPoint n hn k a ha
  have hpMem (k : Fin (t n)) : p k ∈ constructedSupport (radius n * ρ) a := by
    rw [mem_constructedSupport_iff]
    have hRnorm : ‖(radius n : ℂ)‖ = radius n := by
      calc
        ‖(radius n : ℂ)‖ = |radius n| := RCLike.norm_ofReal _
        _ = radius n := abs_of_pos (radius_pos n)
    have hpBall : p k ∈ ball (0 : ℂ) (radius n * ρ) := by
      rw [mem_ball, dist_zero_right]
      dsimp only [p]
      rw [norm_mul, hRnorm]
      exact mul_lt_mul_of_pos_left (hρ k) (radius_pos n)
    rw [constructed_divisor_eq_one hpBall
      (localPoint_actual_value n hn k a ha)
      (localPoint_actual_deriv_ne_zero n hn k a ha)]
    norm_num
  let imagePoints := (Finset.univ : Finset (Fin (t n))).image p
  have himageSubset : imagePoints ⊆ constructedSupport (radius n * ρ) a := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    exact hpMem k
  have hcardImage : imagePoints.card = t n := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact (actualLocalPoint_injective n hn a ha).injOn
  rw [aPointCount_constructed_eq_sum]
  calc
    t n = imagePoints.card := hcardImage.symm
    _ = ∑ z ∈ imagePoints, (1 : ℕ) := by simp
    _ = ∑ z ∈ imagePoints,
        Int.toNat (MeromorphicOn.divisor
          (fun w ↦ constructedFunction w - a) (ball 0 (radius n * ρ)) z) := by
      apply Finset.sum_congr rfl
      intro z hzImage
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hzImage
      have hzBall := constructedSupport_mem_ball (hpMem k)
      rw [constructed_divisor_eq_one hzBall
        (localPoint_actual_value n hn k a ha)
        (localPoint_actual_deriv_ne_zero n hn k a ha)]
      norm_num
    _ ≤ ∑ z ∈ constructedSupport (radius n * ρ) a,
        Int.toNat (MeromorphicOn.divisor
          (fun w ↦ constructedFunction w - a) (ball 0 (radius n * ρ)) z) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himageSubset
      intro i hi hi'
      omega

private lemma constructed_deriv_ne_zero_of_global_disk (n : ℕ) (hn : n ≠ 0)
    (k : Fin (degree n)) {z : ℂ}
    (hz : z / radius n ∈ ball (modelRoot n k) (globalRadius n)) :
    deriv constructedFunction z ≠ 0 := by
  let w : ℂ := z / radius n
  have hwClosed : w ∈ closedBall (modelRoot n k) (globalRadius n) :=
    mem_closedBall.mpr (mem_ball.mp hz).le
  have hscaled := scaledFunction_deriv_ne_zero_on_global n hn k hwClosed
  have hR0 : (radius n : ℂ) ≠ 0 := by exact_mod_cast (radius_pos n).ne'
  have hRw : (radius n : ℂ) * w = z := by
    dsimp only [w]
    field_simp [hR0]
  intro hzero
  apply hscaled
  rw [deriv_scaledFunction_eq, hRw, hzero, mul_zero]

private lemma localized_solutions_equal (n : ℕ) (hn : n ≠ 0)
    (k : Fin (degree n)) (a : ℂ) (ha : ‖a‖ ≤ n + 1) {z₁ z₂ : ℂ}
    (hz₁ : z₁ / radius n ∈ ball (modelRoot n k) (globalRadius n))
    (hz₂ : z₂ / radius n ∈ ball (modelRoot n k) (globalRadius n))
    (hv₁ : constructedFunction z₁ = a) (hv₂ : constructedFunction z₂ = a) : z₁ = z₂ := by
  let w₁ : ℂ := z₁ / radius n
  let w₂ : ℂ := z₂ / radius n
  have hw₁ : w₁ ∈ closedBall (modelRoot n k) (globalRadius n) :=
    mem_closedBall.mpr (mem_ball.mp hz₁).le
  have hw₂ : w₂ ∈ closedBall (modelRoot n k) (globalRadius n) :=
    mem_closedBall.mpr (mem_ball.mp hz₂).le
  have hR0 : (radius n : ℂ) ≠ 0 := by exact_mod_cast (radius_pos n).ne'
  have hRw₁ : (radius n : ℂ) * w₁ = z₁ := by
    dsimp only [w₁]
    field_simp [hR0]
  have hRw₂ : (radius n : ℂ) * w₂ = z₂ := by
    dsimp only [w₂]
    field_simp [hR0]
  have hsw₁ : scaledFunction n w₁ = a := by
    change constructedFunction ((radius n : ℂ) * w₁) = a
    rwa [hRw₁]
  have hsw₂ : scaledFunction n w₂ = a := by
    change constructedFunction ((radius n : ℂ) * w₂) = a
    rwa [hRw₂]
  have hwEq := global_solution_unique n hn k a ha hw₁ hw₂ hsw₁ hsw₂
  rw [← hRw₁, ← hRw₂, hwEq]

private lemma norm_localPoint_le_one_add_affine (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    ‖localPoint n hn k a ha‖ ≤ 1 + affineRadius n := by
  have hk := localPoint_mem n hn k a ha
  have htri := norm_le_norm_add_norm_sub'
    (localPoint n hn k a ha) (modelRoot n (innerIndex n k))
  rw [norm_modelRoot_inner] at htri
  have hdist :
      ‖localPoint n hn k a ha - modelRoot n (innerIndex n k)‖ ≤ affineRadius n := by
    simpa only [dist_eq_norm] using mem_closedBall.mp hk
  nlinarith

private lemma one_sub_affine_le_norm_localPoint (n : ℕ) (hn : n ≠ 0)
    (k : Fin (t n)) (a : ℂ) (ha : ‖a‖ ≤ n + 1) :
    1 - affineRadius n ≤ ‖localPoint n hn k a ha‖ := by
  have hk := localPoint_mem n hn k a ha
  have htri := norm_le_norm_add_norm_sub'
    (modelRoot n (innerIndex n k)) (localPoint n hn k a ha)
  rw [norm_modelRoot_inner] at htri
  have hdist :
      ‖modelRoot n (innerIndex n k) - localPoint n hn k a ha‖ ≤ affineRadius n := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using mem_closedBall.mp hk
  linarith

private lemma current_solution_outside_separator (n : ℕ) (hn : n ≠ 0)
    (b : ℂ) (hb : ‖b‖ ≤ n + 1) (ρ : ℝ)
    (hρb : ∀ l : Fin (t n), ρ < ‖localPoint n hn l b hb‖)
    (k : Fin (degree n)) {w : ℂ}
    (hw : w ∈ ball (modelRoot n k) (globalRadius n))
    (hwValue : scaledFunction n w = b) : ρ < ‖w‖ := by
  have hρAffine : ρ < 1 + affineRadius n := by
    let l₀ : Fin (t n) := ⟨0, lt_of_lt_of_le (by omega) (four_le_t n)⟩
    have hnorm := norm_localPoint_le_one_add_affine n hn l₀ b hb
    exact (hρb l₀).trans_le hnorm
  by_cases hkInner : (k : ℕ) < t n
  · let l : Fin (t n) := ⟨k, hkInner⟩
    have hidx : innerIndex n l = k := Fin.ext rfl
    have hwClosed : w ∈ closedBall (modelRoot n (innerIndex n l)) (globalRadius n) := by
      rw [hidx]
      exact mem_closedBall.mpr (mem_ball.mp hw).le
    have hlClosed := localPoint_mem_global n hn l b hb
    have heq := global_solution_unique n hn (innerIndex n l) b hb hwClosed hlClosed
      hwValue (localPoint_value n hn l b hb)
    rw [heq]
    exact hρb l
  · have hscale : radialScale n (delta n) k = delta n := by
      simp [radialScale, hkInner]
    have hcenter : ‖modelRoot n k‖ = delta n := by rw [norm_modelRoot, hscale]
    have hdist : dist w (modelRoot n k) < globalRadius n := mem_ball.mp hw
    have htri := norm_le_norm_add_norm_sub' (modelRoot n k) w
    rw [hcenter] at htri
    have hgap : affineRadius n < (delta n - 1) / 4 :=
      (affineRadius_lt_localRadius n).trans
        ((localRadius_lt_modelRadius n).trans (modelRadius_lt_gap n))
    have hgap4 : affineRadius n * 4 < delta n - 1 :=
      (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hgap
    have hglobal := globalRadius_lt_affineRadius n
    have haffPos := affineRadius_pos n
    have hdistNorm : ‖modelRoot n k - w‖ < globalRadius n := by
      simpa only [dist_eq_norm, norm_sub_rev] using hdist
    nlinarith

private lemma outer_support_localizes_previous (N n : ℕ) (hN0 : N ≠ 0) (hNn : N < n)
    (hn : n ≠ 0) (b : ℂ) (hbN : ‖b‖ ≤ N + 1) (hb : ‖b‖ ≤ n + 1) (ρ : ℝ)
    (hρb : ∀ l : Fin (t n), ρ < ‖localPoint n hn l b hb‖)
    {z : ℂ} (hzSupport : z ∈ constructedSupport (radius n * ρ) b)
    (hzOuter : 4 * radius N ≤ ‖z‖) :
    ∃ i : PreviousIndex n,
      N < (i.1 : ℕ) ∧
        z / radius i.1 ∈ ball (modelRoot i.1 i.2) (globalRadius i.1) := by
  have hρlt : ρ < 4 := by
    let l₀ : Fin (t n) := ⟨0, lt_of_lt_of_le (by omega) (four_le_t n)⟩
    have hnorm := norm_localPoint_le_one_add_affine n hn l₀ b hb
    have haff := affineRadius_lt_quarter n
    nlinarith [hρb l₀]
  have hzBall := constructedSupport_mem_ball hzSupport
  have hzNorm : ‖z‖ < radius n * ρ := by
    simpa [mem_ball, dist_zero_right] using hzBall
  have hzHigh : ‖z‖ < 4 * radius n := by
    exact hzNorm.trans (by
      simpa [mul_comm] using mul_lt_mul_of_pos_left hρlt (radius_pos n))
  have hzValue := constructedSupport_value hzSupport
  obtain ⟨i, hiN, hin, k, hk⟩ := solution_localizes_between N n hN0 hNn.le b hbN
    hzValue hzOuter hzHigh
  have hi : i < n := by
    apply lt_of_le_of_ne hin
    intro hieq
    have hieq' : i = n := hieq
    subst i
    let w : ℂ := z / radius n
    have hwValue : scaledFunction n w = b := by
      have hR0 : (radius n : ℂ) ≠ 0 := by exact_mod_cast (radius_pos n).ne'
      have hRw : (radius n : ℂ) * w = z := by
        dsimp only [w]
        field_simp [hR0]
      change constructedFunction ((radius n : ℂ) * w) = b
      rwa [hRw]
    have hout := current_solution_outside_separator n hn b hb ρ hρb k hk hwValue
    have hwNorm : ‖w‖ = ‖z‖ / radius n := by
      dsimp only [w]
      have hRnorm : ‖(radius n : ℂ)‖ = radius n := by
        rw [Complex.norm_real, Real.norm_of_nonneg (radius_pos n).le]
      rw [norm_div, hRnorm]
    have hwInside : ‖w‖ < ρ := by
      rw [hwNorm]
      exact (div_lt_iff₀ (radius_pos n)).2 (by simpa [mul_comm] using hzNorm)
    linarith
  exact ⟨⟨⟨i, hi⟩, k⟩, hiN, hk⟩

private lemma outer_support_card_le_previousDegree (N n : ℕ) (hN0 : N ≠ 0)
    (hNn : N < n) (hn : n ≠ 0) (b : ℂ) (hbN : ‖b‖ ≤ N + 1)
    (hb : ‖b‖ ≤ n + 1) (ρ : ℝ)
    (hρb : ∀ l : Fin (t n), ρ < ‖localPoint n hn l b hb‖) :
    ((constructedSupport (radius n * ρ) b).filter
      (fun z ↦ 4 * radius N ≤ ‖z‖)).card ≤ previousDegree n := by
  classical
  let outer := (constructedSupport (radius n * ρ) b).filter
    (fun z ↦ 4 * radius N ≤ ‖z‖)
  have hloc (z : ↥outer) : ∃ i : PreviousIndex n,
      N < (i.1 : ℕ) ∧
        z.1 / radius i.1 ∈ ball (modelRoot i.1 i.2) (globalRadius i.1) := by
    have hz := Finset.mem_filter.mp z.2
    exact outer_support_localizes_previous N n hN0 hNn hn b hbN hb ρ hρb hz.1 hz.2
  let block : ↥outer → PreviousIndex n := fun z ↦ Classical.choose (hloc z)
  have hblock (z : ↥outer) :
      z.1 / radius (block z).1 ∈
        ball (modelRoot (block z).1 (block z).2) (globalRadius (block z).1) :=
    (Classical.choose_spec (hloc z)).2
  have hblockInjective : Function.Injective block := by
    intro z₁ z₂ hEq
    have hz₁Support := (Finset.mem_filter.mp z₁.2).1
    have hz₂Support := (Finset.mem_filter.mp z₂.2).1
    have hiN : N < ((block z₁).1 : ℕ) := by
      exact (Classical.choose_spec (hloc z₁)).1
    have hi0 : ((block z₁).1 : ℕ) ≠ 0 := by omega
    have hbi : ‖b‖ ≤ ((block z₁).1 : ℕ) + 1 := by
      calc
        ‖b‖ ≤ (N + 1 : ℝ) := hbN
        _ ≤ (((block z₁).1 : ℕ) + 1 : ℝ) := by
          exact_mod_cast Nat.add_le_add_right hiN.le 1
    apply Subtype.ext
    apply localized_solutions_equal ((block z₁).1 : ℕ) hi0 (block z₁).2 b hbi
    · exact hblock z₁
    · have hblock₂ := hblock z₂
      rw [← hEq] at hblock₂
      exact hblock₂
    · exact constructedSupport_value hz₁Support
    · exact constructedSupport_value hz₂Support
  calc
    ((constructedSupport (radius n * ρ) b).filter
        (fun z ↦ 4 * radius N ≤ ‖z‖)).card = Fintype.card ↥outer := by
      simp [outer]
    _ ≤ Fintype.card (PreviousIndex n) :=
      Fintype.card_le_of_injective block hblockInjective
    _ = previousDegree n := card_previousIndex n

private lemma constructed_divisor_eq_of_mem_balls {r s : ℝ} {a z : ℂ}
    (hzr : z ∈ ball (0 : ℂ) r) (hzs : z ∈ ball (0 : ℂ) s) :
    MeromorphicOn.divisor (fun w ↦ constructedFunction w - a) (ball 0 r) z =
      MeromorphicOn.divisor (fun w ↦ constructedFunction w - a) (ball 0 s) z := by
  have han := analytic_sub_const differentiable_constructedFunction a
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
        (han.mono (Set.subset_univ (ball (0 : ℂ) r))) hzr,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
        (han.mono (Set.subset_univ (ball (0 : ℂ) s))) hzs]

private lemma aPointCount_at_separating_radius_le (N n : ℕ) (hN0 : N ≠ 0)
    (hNn : N < n) (hn : n ≠ 0) (b : ℂ) (hbN : ‖b‖ ≤ N + 1)
    (hb : ‖b‖ ≤ n + 1) (ρ : ℝ)
    (hρb : ∀ l : Fin (t n), ρ < ‖localPoint n hn l b hb‖) :
    aPointCount constructedFunction (radius n * ρ) b ≤
      aPointCount constructedFunction (4 * radius N) b + previousDegree n := by
  classical
  let largeSupport := constructedSupport (radius n * ρ) b
  let inner := largeSupport.filter (fun z ↦ ‖z‖ < 4 * radius N)
  let outer := largeSupport.filter (fun z ↦ 4 * radius N ≤ ‖z‖)
  let bigDivisor (z : ℂ) := Int.toNat (MeromorphicOn.divisor
    (fun w ↦ constructedFunction w - b) (ball 0 (radius n * ρ)) z)
  let smallDivisor (z : ℂ) := Int.toNat (MeromorphicOn.divisor
    (fun w ↦ constructedFunction w - b) (ball 0 (4 * radius N)) z)
  have hpartition : (∑ z ∈ largeSupport, bigDivisor z) =
      (∑ z ∈ inner, bigDivisor z) + ∑ z ∈ outer, bigDivisor z := by
    have hsplit := Finset.sum_filter_add_sum_filter_not largeSupport
      (fun z ↦ ‖z‖ < 4 * radius N) bigDivisor
    simpa only [inner, outer, not_lt] using hsplit.symm
  have hinnerSubset : inner ⊆ constructedSupport (4 * radius N) b := by
    intro z hz
    have hzParts := Finset.mem_filter.mp hz
    have hzLargeBall := constructedSupport_mem_ball hzParts.1
    have hzSmallBall : z ∈ ball (0 : ℂ) (4 * radius N) := by
      simpa [mem_ball, dist_zero_right] using hzParts.2
    apply (mem_constructedSupport_iff (4 * radius N) b z).mpr
    have hzNonzero := (mem_constructedSupport_iff (radius n * ρ) b z).mp hzParts.1
    rw [← constructed_divisor_eq_of_mem_balls hzLargeBall hzSmallBall]
    exact hzNonzero
  have hinner : (∑ z ∈ inner, bigDivisor z) ≤
      aPointCount constructedFunction (4 * radius N) b := by
    rw [aPointCount_constructed_eq_sum]
    calc
      (∑ z ∈ inner, bigDivisor z) = ∑ z ∈ inner, smallDivisor z := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzParts := Finset.mem_filter.mp hz
        have hzLargeBall := constructedSupport_mem_ball hzParts.1
        have hzSmallBall : z ∈ ball (0 : ℂ) (4 * radius N) := by
          simpa [mem_ball, dist_zero_right] using hzParts.2
        simp only [bigDivisor, smallDivisor]
        rw [constructed_divisor_eq_of_mem_balls hzLargeBall hzSmallBall]
      _ ≤ ∑ z ∈ constructedSupport (4 * radius N) b, smallDivisor z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hinnerSubset
        intro z hz hzNot
        omega
      _ = ∑ z ∈ constructedSupport (4 * radius N) b,
          Int.toNat (MeromorphicOn.divisor
            (fun w ↦ constructedFunction w - b) (ball 0 (4 * radius N)) z) := by
        rfl
  have houterOne (z : ℂ) (hz : z ∈ outer) : bigDivisor z = 1 := by
    have hzParts := Finset.mem_filter.mp hz
    obtain ⟨i, hiN, hi⟩ := outer_support_localizes_previous N n hN0 hNn hn b hbN hb ρ
      hρb hzParts.1 hzParts.2
    have hi0 : ((i.1 : Fin n) : ℕ) ≠ 0 := by omega
    have hzBall := constructedSupport_mem_ball hzParts.1
    simp only [bigDivisor]
    rw [constructed_divisor_eq_one hzBall (constructedSupport_value hzParts.1)
      (constructed_deriv_ne_zero_of_global_disk (i.1 : ℕ) hi0 i.2 hi)]
    norm_num
  have houter : (∑ z ∈ outer, bigDivisor z) ≤ previousDegree n := by
    calc
      (∑ z ∈ outer, bigDivisor z) = outer.card := by
        calc
          (∑ z ∈ outer, bigDivisor z) = ∑ _z ∈ outer, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro z hz
            exact houterOne z hz
          _ = outer.card := by simp
      _ ≤ previousDegree n := by
        simpa only [outer, largeSupport] using
          outer_support_card_le_previousDegree N n hN0 hNn hn b hbN hb ρ hρb
  rw [aPointCount_constructed_eq_sum]
  change (∑ z ∈ largeSupport, bigDivisor z) ≤ _
  rw [hpartition]
  exact Nat.add_le_add hinner houter

/-- Erdős Problem 1116 has a positive answer, already in the class of entire
functions.  `UnboundedCountRatio` is the division-free formulation of the
assertion that the upper limit of `n(r,a) / n(r,b)` is infinite. -/
theorem erdos_1116 :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ a b : ℂ, a ≠ b → UnboundedCountRatio f a b := by
  refine ⟨constructedFunction, differentiable_constructedFunction, ?_⟩
  intro a b hab M R
  let X : ℝ := 2 + ‖a‖ + ‖b‖
  obtain ⟨N, hNX⟩ := exists_nat_gt X
  have hN0 : N ≠ 0 := by
    have hNreal : (1 : ℝ) < N := by
      dsimp only [X] at hNX
      nlinarith [norm_nonneg a, norm_nonneg b]
    have hNone : 1 < N := by exact_mod_cast hNreal
    omega
  have haN : ‖a‖ ≤ N + 1 := by
    dsimp only [X] at hNX
    nlinarith [norm_nonneg b]
  have hbN : ‖b‖ ≤ N + 1 := by
    dsimp only [X] at hNX
    nlinarith [norm_nonneg a]
  let C := aPointCount constructedFunction (4 * radius N) b
  obtain ⟨K, hKR⟩ := exists_nat_gt (4 * R)
  let threshold := max N (max K (M * (C + 1) + 1))
  obtain ⟨n, hn, ha, hb, hthreshold, horder⟩ :=
    exists_radial_separating_stage a b hab threshold
  have hNn : N < n := by
    exact (le_max_left N (max K (M * (C + 1) + 1))).trans_lt hthreshold
  have hKn : K < n := by
    exact (le_trans (le_max_left K (M * (C + 1) + 1))
      (le_max_right N (max K (M * (C + 1) + 1)))).trans_lt hthreshold
  have hgrowthThreshold : M * (C + 1) + 1 < n := by
    exact (le_trans (le_max_right K (M * (C + 1) + 1))
      (le_max_right N (max K (M * (C + 1) + 1)))).trans_lt hthreshold
  let k₀ : Fin (t n) := ⟨0, lt_of_lt_of_le (by omega) (four_le_t n)⟩
  let _ : Nonempty (Fin (t n)) := ⟨k₀⟩
  obtain ⟨ρ, hρa, hρb⟩ := exists_between_finite_families
    (fun k : Fin (t n) ↦ ‖localPoint n hn k a ha‖)
    (fun l : Fin (t n) ↦ ‖localPoint n hn l b hb‖) horder
  have hρthree : (3 / 4 : ℝ) < ρ := by
    have hlower := one_sub_affine_le_norm_localPoint n hn k₀ a ha
    have haff := affineRadius_lt_quarter n
    nlinarith [hρa k₀]
  have hrLarge : R < radius n * ρ := by
    have hKRreal : 4 * R < (K : ℝ) := hKR
    have hKnreal : (K : ℝ) < n := by exact_mod_cast hKn
    have hnPos : (0 : ℝ) < n := by
      exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hRquarter : R < (n : ℝ) * (3 / 4) := by
      nlinarith
    calc
      R < (n : ℝ) * (3 / 4) := hRquarter
      _ < radius n * (3 / 4) :=
        mul_lt_mul_of_pos_right (radius_tends n) (by norm_num)
      _ < radius n * ρ := mul_lt_mul_of_pos_left hρthree (radius_pos n)
  have hlowerCount := t_le_aPointCount_at_separating_radius n hn a ha ρ hρa
  have hupperCount := aPointCount_at_separating_radius_le N n hN0 hNn hn b hbN hb ρ hρb
  have hgrowth : M * (C + previousDegree n) < t n :=
    large_growth_of_stage M C n hgrowthThreshold
  have hrBase : 4 * radius N < radius n * ρ := by
    have hsep := (radius_admissible n).2.2.2.1 N hNn
    rw [constructionState_radius_stable hNn, abs_of_pos (radius_pos N)] at hsep
    calc
      4 * radius N < radius n * (3 / 4) := by
        nlinarith [radius_pos N]
      _ < radius n * ρ := mul_lt_mul_of_pos_left hρthree (radius_pos n)
  have hbaseRho : ∀ k : Fin (t N),
      ‖localPoint N hN0 k b hbN‖ < (radius n * ρ) / radius N := by
    intro k
    have hnorm := norm_localPoint_le_one_add_affine N hN0 k b hbN
    have haff := affineRadius_lt_quarter N
    have hfour : 4 < (radius n * ρ) / radius N := by
      exact (lt_div_iff₀ (radius_pos N)).2 (by simpa [mul_comm] using hrBase)
    linarith
  have hbaseCount := t_le_aPointCount_at_separating_radius N hN0 b hbN
    ((radius n * ρ) / radius N) hbaseRho
  have hbaseRadius : radius N * ((radius n * ρ) / radius N) = radius n * ρ := by
    field_simp [(radius_pos N).ne']
  rw [hbaseRadius] at hbaseCount
  have hcountBPos : 0 < aPointCount constructedFunction (radius n * ρ) b := by
    have htN : 0 < t N := lt_of_lt_of_le (by omega) (four_le_t N)
    exact lt_of_lt_of_le htN hbaseCount
  refine ⟨radius n * ρ, hrLarge, hcountBPos, ?_⟩
  calc
    M * aPointCount constructedFunction (radius n * ρ) b ≤
        M * (C + previousDegree n) := Nat.mul_le_mul_left M hupperCount
    _ < t n := hgrowth
    _ ≤ aPointCount constructedFunction (radius n * ρ) a := hlowerCount

#print axioms erdos_1116

end Erdos1116
