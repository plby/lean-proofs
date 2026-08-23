/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeCompletionSharp
import ErdosProblems.Erdos240.BakerSourceCoprimeBoundaryHermiteBudget
import ErdosProblems.Erdos240.BakerSourceAlgebraicStaticFactors
import ErdosProblems.Erdos240.BakerSourceAlgebraicUniformBounds

/-!
# Source-faithful growth on the p. 52 coprime grid

At the successor state the p. 52 nodes and contour have radius proportional
to `q^(J+1)`.  The exact `q^(-(J+1))` factors in both the algebraic rate and
the perturbation amplification cancel this radius.  This file packages the
resulting fixed-height bounds.  In particular, no coefficient-dominance
hypothesis is used.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceCoprimeGridGrowth

open Complex Finset Metric Polynomial
open BakerCoprimeCompletionSharp
open BakerCoprimeHermiteTarget
open BakerCoprimeInterpolation
open BakerCoprimeMomentBounds
open BakerInduction
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerLemma4Concrete
open BakerSourceAlgebraicLevelMajorant
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceAlgebraicStaticFactors
open BakerSourceAlgebraicUniformBounds
open BakerSourceLogFormNormalization
open BakerSourceMajorantClosedForm
open BakerSourceOversizedConstantNumerics
open BakerSourceState
open HermiteInterpolation
open CoprimeHermiteBasis
open InterpolationProducts

/-- The fixed source-height unit used in the p. 52 estimates. -/
private def H {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) : ℝ :=
  (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld

private theorem H_pos {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) : 0 < H P := by
  unfold H
  exact mul_pos
    (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
    P.log_OmegaOld_pos

private theorem log_two_mul_Bsrc_le_two_h {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    Real.log (2 * (P.Bsrc : ℝ)) ≤ 2 * P.h := by
  have hBpos : (0 : ℝ) < P.Bsrc :=
    (Real.exp_pos 2).trans_le P.Bsrc_lower
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hBpos.ne']
  have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
  nlinarith [P.log_Bsrc_lt_h_add_one]

private theorem norm_oldLog_le_log_oldHeight {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (r : Fin oldRank) :
    ‖oldLog P r‖ ≤ Real.log (P.oldHeight r) := by
  unfold oldLog
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  · exact Real.log_le_log (by exact_mod_cast P.old_prime r |>.pos)
      (P.old_cast_lt_oldHeight r).le
  · exact Real.log_pos (by exact_mod_cast (P.old_prime r).one_lt)

private theorem norm_lastLog_le_log_newHeight {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    ‖lastLog P‖ ≤ Real.log P.newHeight := by
  unfold lastLog
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  · apply Real.log_le_log (by exact_mod_cast P.newPrime_pos)
    exact P.newPrime_cast_lt_varyingHeight.le.trans
      P.varyingHeight_le_newHeight
  · exact Real.log_pos (by exact_mod_cast P.new_prime.one_lt)

private theorem sourceAlgebraicRateBound_le_eighth {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    sourceAlgebraicRateBound P ≤
      (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
  let U : ℝ := (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
    P.Omega * Real.log P.OmegaOld
  have hterm (r : Fin oldRank) :
      (P.LiZero r : ℝ) * ‖oldLog P r‖ ≤ U := by
    calc
      (P.LiZero r : ℝ) * ‖oldLog P r‖ ≤
          P.LiZeroScale r * Real.log (P.oldHeight r) :=
        mul_le_mul (P.LiZero_cast_le r)
          (norm_oldLog_le_log_oldHeight P r) (norm_nonneg _)
          (P.LiZeroScale_pos r).le
      _ = U := by
        dsimp only [U]
        unfold VDPLParameters.LiZeroScale
        field_simp [P.log_oldHeight_pos r |>.ne']
  have hlast :
      (P.LlastZero : ℝ) * ‖lastLog P‖ ≤ U := by
    calc
      (P.LlastZero : ℝ) * ‖lastLog P‖ ≤
          P.LlastZeroScale * Real.log P.newHeight :=
        mul_le_mul P.LlastZero_cast_le
          (norm_lastLog_le_log_newHeight P) (norm_nonneg _)
          P.LlastZeroScale_pos.le
      _ = U := by
        dsimp only [U]
        unfold VDPLParameters.LlastZeroScale
        field_simp [P.log_newHeight_pos.ne']
  unfold sourceAlgebraicRateBound
  calc
    (∑ r : Fin oldRank, (P.LiZero r : ℝ) * ‖oldLog P r‖) +
        (P.LlastZero : ℝ) * ‖lastLog P‖ ≤
      (∑ _r : Fin oldRank, U) + U :=
        add_le_add (Finset.sum_le_sum fun r _hr ↦ hterm r) hlast
    _ = (P.rank : ℝ) * U := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [Fintype.card_fin, VDPLParameters.rank]
      push_cast
      ring
    _ = (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
      dsimp only [U]
      have hrankPos : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
      have hrank : (P.rank : ℝ) ≠ 0 := ne_of_gt hrankPos
      field_simp

private theorem fullBoundaryProduct_le (R : ℕ) (w : ℂ)
    (hz : ‖w‖ = 4 * (R : ℝ)) :
    (∏ i ∈ range R, ‖w - (((i + 1 : ℕ) : ℂ))‖) ≤
      (2 : ℝ) ^ (5 * R) * R.factorial := by
  have hterm (i : ℕ) (hi : i ∈ range R) :
      ‖w - (((i + 1 : ℕ) : ℂ))‖ ≤ 5 * (R : ℝ) := by
    have hiR : i + 1 ≤ R := Nat.succ_le_iff.mpr (mem_range.mp hi)
    calc
      ‖w - (((i + 1 : ℕ) : ℂ))‖ ≤ ‖w‖ + ‖(((i + 1 : ℕ) : ℂ))‖ :=
        norm_sub_le _ _
      _ = 4 * (R : ℝ) + (i + 1 : ℕ) := by
        rw [hz, Complex.norm_natCast]
      _ ≤ 5 * (R : ℝ) := by
        norm_cast
        omega
  have hprod :
      (∏ i ∈ range R, ‖w - (((i + 1 : ℕ) : ℂ))‖) ≤
        (5 * (R : ℝ)) ^ R := by
    calc
      (∏ i ∈ range R, ‖w - (((i + 1 : ℕ) : ℂ))‖) ≤
          ∏ _i ∈ range R, (5 * (R : ℝ)) := by
        exact prod_le_prod (fun _ _ ↦ norm_nonneg _) hterm
      _ = (5 * (R : ℝ)) ^ R := by simp
  have hpowfac : ((R : ℝ) ^ R) ≤ Real.exp R * R.factorial := by
    have hfac : (0 : ℝ) < R.factorial := by positivity
    exact (div_le_iff₀ hfac).mp
      (Real.pow_div_factorial_le_exp (x := (R : ℝ)) (by positivity) R)
  have hexp : Real.exp (R : ℝ) ≤ (2 : ℝ) ^ (2 * R) := by
    rw [show (R : ℝ) = (R : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
    calc
      Real.exp 1 ^ R ≤ (4 : ℝ) ^ R :=
        pow_le_pow_left₀ (Real.exp_pos 1).le
          (Real.exp_one_lt_three.le.trans (by norm_num)) R
      _ = (2 : ℝ) ^ (2 * R) := by rw [pow_mul]; norm_num
  calc
    (∏ i ∈ range R, ‖w - (((i + 1 : ℕ) : ℂ))‖) ≤
        (5 * (R : ℝ)) ^ R := hprod
    _ = (5 : ℝ) ^ R * (R : ℝ) ^ R := by rw [mul_pow]
    _ ≤ (8 : ℝ) ^ R * (Real.exp R * R.factorial) := by
      exact mul_le_mul
        (pow_le_pow_left₀ (by norm_num) (by norm_num) R) hpowfac
        (by positivity) (by positivity)
    _ ≤ (8 : ℝ) ^ R * ((2 : ℝ) ^ (2 * R) * R.factorial) := by
      gcongr
    _ = (2 : ℝ) ^ (5 * R) * R.factorial := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      calc
        (2 : ℝ) ^ (3 * R) * ((2 : ℝ) ^ (2 * R) * R.factorial) =
            ((2 : ℝ) ^ (3 * R) * (2 : ℝ) ^ (2 * R)) * R.factorial := by
          ring
        _ = (2 : ℝ) ^ (5 * R) * R.factorial := by
          rw [← pow_add]
          congr 2
          omega

private theorem fullSpacingProduct_eq_factorial_pair
    {R x : ℕ} (hx : 1 ≤ x) (hxR : x ≤ R) :
    ∏ i ∈ (range R).erase (x - 1),
        ‖((x : ℕ) : ℂ) - (((i + 1 : ℕ) : ℂ))‖ =
      (x - 1).factorial * (R - x).factorial := by
  have hsets : (range R).erase (x - 1) =
      range (x - 1) ∪ Ico x R := by
    ext i
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range (x - 1)) (Ico x R) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [mem_range] at hi
    simp only [mem_Ico] at hj
    omega
  rw [hsets, prod_union hdisj]
  have hleft :
      ∏ i ∈ range (x - 1),
          ‖((x : ℕ) : ℂ) - (((i + 1 : ℕ) : ℂ))‖ =
        ((x - 1).factorial : ℝ) := by
    rw [← prod_range_cast_sub_eq_factorial (x - 1)]
    apply prod_congr rfl
    intro i hi
    have hix : i + 1 ≤ x := by
      have hi' := mem_range.mp hi
      omega
    rw [← Nat.cast_sub hix, Complex.norm_natCast]
    norm_cast
    omega
  have hright :
      ∏ i ∈ Ico x R,
          ‖((x : ℕ) : ℂ) - (((i + 1 : ℕ) : ℂ))‖ =
        ((R - x).factorial : ℝ) := by
    rw [prod_Ico_eq_prod_range]
    rw [← prod_range_cast_add_one_eq_factorial (R - x)]
    apply prod_congr rfl
    intro i hi
    have hxi : x ≤ x + i + 1 := by omega
    rw [norm_sub_rev, ← Nat.cast_sub hxi, Complex.norm_natCast]
    congr 1
    omega
  rw [hleft, hright]

private theorem fullBoundaryProduct_le_spacing (R r : ℕ) (w : ℂ)
    (hr : r < R) (hz : ‖w‖ = 4 * (R : ℝ)) :
    (∏ i ∈ range R, ‖w - (((i + 1 : ℕ) : ℂ))‖) ≤
      (2 : ℝ) ^ (7 * R) *
        (∏ i ∈ (range R).erase r,
          ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖) := by
  have hfac := BakerLemma4Concrete.factorial_le_localCircle_factor_times_pow
    (R := R) (r := r + 1) (Nat.succ_pos r) (by omega : r + 1 ≤ R)
  have hspacing :
      ((r.factorial : ℝ) * (R - (r + 1)).factorial) =
        ∏ i ∈ (range R).erase r,
          ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖ := by
    symm
    simpa only [Nat.add_sub_cancel] using
      (fullSpacingProduct_eq_factorial_pair
        (x := r + 1) (R := R) (Nat.succ_pos r)
          (by omega : r + 1 ≤ R))
  norm_num only [Nat.add_sub_cancel] at hfac
  rw [show (2 : ℝ) ^ (2 * R) * (r.factorial : ℝ) *
      ((R - (r + 1)).factorial : ℝ) =
      (2 : ℝ) ^ (2 * R) *
        ((r.factorial : ℝ) * (R - (r + 1)).factorial) by ring] at hfac
  rw [hspacing] at hfac
  calc
    (∏ i ∈ range R, ‖w - (((i + 1 : ℕ) : ℂ))‖) ≤
        (2 : ℝ) ^ (5 * R) * R.factorial := fullBoundaryProduct_le R w hz
    _ ≤ (2 : ℝ) ^ (5 * R) *
        ((2 : ℝ) ^ (2 * R) *
          (∏ i ∈ (range R).erase r,
            ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖)) := by
      exact mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (2 : ℝ) ^ (7 * R) *
        (∏ i ∈ (range R).erase r,
          ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

/-- On `|w| = 4R`, the coprime-grid nodal product divided by any retained
spacing product is at most `2^(10R)`. -/
theorem norm_finiteNodePolynomial_boundary_le
    {q R r : ℕ} {w : ℂ} (hR : 0 < R)
    (hr : r ∈ coprimeNodeIndices q R)
    (hw : ‖w‖ = 4 * (R : ℝ)) :
    ‖(finiteNodePolynomial (coprimeNodeIndices q R)).eval w‖ ≤
      (2 : ℝ) ^ (10 * R) *
        finiteSpacingProduct (coprimeNodeIndices q R) r := by
  let p : ℕ → Prop := fun i ↦ (i + 1).Coprime q
  let fnum : ℕ → ℝ := fun i ↦ ‖w - (((i + 1 : ℕ) : ℂ))‖
  let fden : ℕ → ℝ := fun i ↦
    ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖
  let deleted : Finset ℕ := (range R).filter fun i ↦ ¬p i
  have hrR : r < R := (mem_coprimeNodeIndices.mp hr).1
  have hrp : p r := (mem_coprimeNodeIndices.mp hr).2
  have hdeleted (i : ℕ) (hi : i ∈ deleted) : fden i ≤ fnum i := by
    have hiR : i + 1 ≤ R := by
      dsimp only [deleted] at hi
      rw [mem_filter] at hi
      exact Nat.succ_le_iff.mpr (mem_range.mp hi.1)
    have hden : fden i ≤ 2 * (R : ℝ) := by
      dsimp only [fden]
      calc
        ‖(((r + 1 : ℕ) : ℂ)) - (((i + 1 : ℕ) : ℂ))‖ ≤
            ‖(((r + 1 : ℕ) : ℂ))‖ + ‖(((i + 1 : ℕ) : ℂ))‖ :=
          norm_sub_le _ _
        _ = ((r + 1 : ℕ) : ℝ) + (i + 1 : ℕ) := by
          rw [Complex.norm_natCast, Complex.norm_natCast]
        _ ≤ 2 * (R : ℝ) := by
          norm_cast
          omega
    have hnum : 3 * (R : ℝ) ≤ fnum i := by
      dsimp only [fnum]
      calc
        3 * (R : ℝ) = ‖w‖ - (R : ℝ) := by rw [hw]; ring
        _ ≤ ‖w‖ - ‖(((i + 1 : ℕ) : ℂ))‖ := by
          rw [Complex.norm_natCast]
          exact sub_le_sub_left (by exact_mod_cast hiR) _
        _ ≤ ‖w - (((i + 1 : ℕ) : ℂ))‖ := norm_sub_norm_le _ _
    have htwo_three : 2 * (R : ℝ) ≤ 3 * (R : ℝ) := by
      have hRn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
      nlinarith
    exact hden.trans (htwo_three.trans hnum)
  have hdeletedProd :
      (∏ i ∈ deleted, fden i) ≤ ∏ i ∈ deleted, fnum i := by
    exact prod_le_prod (fun _ _ ↦ norm_nonneg _) hdeleted
  have hdeletedPos : 0 < ∏ i ∈ deleted, fnum i := by
    apply Finset.prod_pos
    intro i hi
    have hiR : i + 1 ≤ R := by
      dsimp only [deleted] at hi
      rw [mem_filter] at hi
      exact Nat.succ_le_iff.mpr (mem_range.mp hi.1)
    have hlow : 3 * (R : ℝ) ≤ fnum i := by
      dsimp only [fnum]
      calc
        3 * (R : ℝ) = ‖w‖ - (R : ℝ) := by rw [hw]; ring
        _ ≤ ‖w‖ - ‖(((i + 1 : ℕ) : ℂ))‖ := by
          rw [Complex.norm_natCast]
          exact sub_le_sub_left (by exact_mod_cast hiR) _
        _ ≤ ‖w - (((i + 1 : ℕ) : ℂ))‖ := norm_sub_norm_le _ _
    exact (by positivity : 0 < 3 * (R : ℝ)).trans_le hlow
  have hnumSplit :
      (∏ i ∈ coprimeNodeIndices q R, fnum i) *
          (∏ i ∈ deleted, fnum i) = ∏ i ∈ range R, fnum i := by
    simpa only [coprimeNodeIndices, p, deleted] using
      (prod_filter_mul_prod_filter_not (range R) p fnum)
  have hdenSplit :
      (∏ i ∈ (coprimeNodeIndices q R).erase r, fden i) *
          (∏ i ∈ deleted, fden i) =
        ∏ i ∈ (range R).erase r, fden i := by
    have hs := prod_filter_mul_prod_filter_not ((range R).erase r) p fden
    rw [filter_erase] at hs
    have hfilter : ((range R).erase r).filter (fun i ↦ ¬p i) = deleted := by
      ext i
      dsimp only [deleted]
      simp only [mem_filter, mem_erase, mem_range]
      constructor
      · intro hi
        exact ⟨hi.1.2, hi.2⟩
      · intro hi
        refine ⟨⟨?_, hi.1⟩, hi.2⟩
        intro hir
        subst i
        exact hi.2 hrp
    rw [hfilter] at hs
    simpa only [coprimeNodeIndices, p, deleted] using hs
  have hfull :
      (∏ i ∈ range R, fnum i) ≤ (2 : ℝ) ^ (7 * R) *
        (∏ i ∈ (range R).erase r, fden i) := by
    simpa only [fnum, fden] using fullBoundaryProduct_le_spacing R r w hrR hw
  have hpow : (2 : ℝ) ^ (7 * R) ≤ (2 : ℝ) ^ (10 * R) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hmul :
      (∏ i ∈ coprimeNodeIndices q R, fnum i) *
          (∏ i ∈ deleted, fnum i) ≤
        ((2 : ℝ) ^ (10 * R) *
          (∏ i ∈ (coprimeNodeIndices q R).erase r, fden i)) *
            (∏ i ∈ deleted, fnum i) := by
    calc
      (∏ i ∈ coprimeNodeIndices q R, fnum i) *
          (∏ i ∈ deleted, fnum i) = ∏ i ∈ range R, fnum i := hnumSplit
      _ ≤ (2 : ℝ) ^ (7 * R) *
          (∏ i ∈ (range R).erase r, fden i) := hfull
      _ = (2 : ℝ) ^ (7 * R) *
          ((∏ i ∈ (coprimeNodeIndices q R).erase r, fden i) *
            (∏ i ∈ deleted, fden i)) := by rw [hdenSplit]
      _ ≤ (2 : ℝ) ^ (7 * R) *
          ((∏ i ∈ (coprimeNodeIndices q R).erase r, fden i) *
            (∏ i ∈ deleted, fnum i)) := by
        gcongr
      _ ≤ (2 : ℝ) ^ (10 * R) *
          ((∏ i ∈ (coprimeNodeIndices q R).erase r, fden i) *
            (∏ i ∈ deleted, fnum i)) := by
        gcongr
      _ = ((2 : ℝ) ^ (10 * R) *
          (∏ i ∈ (coprimeNodeIndices q R).erase r, fden i)) *
            (∏ i ∈ deleted, fnum i) := by ring
  have hcancel := le_of_mul_le_mul_right hmul hdeletedPos
  simpa only [eval_finiteNodePolynomial, norm_prod, finiteSpacingProduct,
    fnum, fden] using hcancel

/-- The factorial-cancelled basis-term estimate at an arbitrary complex
target.  The only replacement for integrality is the explicit unit-distance
hypothesis from every interpolation node. -/
theorem norm_finiteBasisTerm_eval_le_complex
    {s : Finset ℕ} {T r m j : ℕ} {w : ℂ} (hr : r ∈ s)
    (hdist : 1 ≤ ‖w - (((r + 1 : ℕ) : ℂ))‖)
    (hmj : m + j ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hratio : ‖(finiteNodePolynomial s).eval w‖ ≤
      K * finiteSpacingProduct s r) :
    ‖(finiteBasisTerm s T r m j).eval w‖ ≤
      K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) := by
  let D : ℝ := finiteSpacingProduct s r
  let d : ℝ := ‖w - (((r + 1 : ℕ) : ℂ))‖
  let A : ℝ := ‖(finiteCofactorPolynomial s r).eval w‖
  have hD : 0 < D := finiteSpacingProduct_pos
  have hd : 1 ≤ d := by simpa only [d] using hdist
  have hfull : ‖(finiteNodePolynomial s).eval w‖ = d * A := by
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

theorem norm_finiteBasisPolynomial_eval_le_sum_complex
    {s : Finset ℕ} {T r m : ℕ} {w : ℂ} (hr : r ∈ s)
    (hdist : 1 ≤ ‖w - (((r + 1 : ℕ) : ℂ))‖)
    (hm : m ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hratio : ‖(finiteNodePolynomial s).eval w‖ ≤
      K * finiteSpacingProduct s r) :
    ‖(finiteBasisPolynomial s T r m).eval w‖ ≤
      ∑ j ∈ range (T - m),
        K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) := by
  rw [finiteBasisPolynomial]
  simp_rw [Polynomial.eval_finsetSum]
  calc
    ‖∑ j ∈ range (T - m), (finiteBasisTerm s T r m j).eval w‖ ≤
        ∑ j ∈ range (T - m),
          ‖(finiteBasisTerm s T r m j).eval w‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range (T - m),
        K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      exact norm_finiteBasisTerm_eval_le_complex hr hdist (by omega) hK hratio

theorem norm_finiteHermitePolynomial_eval_le_sum_complex
    {s : Finset ℕ} {T : ℕ} {w : ℂ} (c : ℕ → ℕ → ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hdist : ∀ r ∈ s, 1 ≤ ‖w - (((r + 1 : ℕ) : ℂ))‖)
    (hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval w‖ ≤
        K * finiteSpacingProduct s r) :
    ‖(finiteHermitePolynomial s T c).eval w‖ ≤
      ∑ r ∈ s, ∑ m ∈ range T,
        ‖c r m‖ *
          (∑ j ∈ range (T - m),
            K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
  rw [finiteHermitePolynomial, Polynomial.eval_finsetSum]
  calc
    ‖∑ r ∈ s,
        (∑ m ∈ range T, c r m • finiteBasisPolynomial s T r m).eval w‖ ≤
      ∑ r ∈ s,
        ‖(∑ m ∈ range T, c r m • finiteBasisPolynomial s T r m).eval w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ s, ∑ m ∈ range T,
        ‖c r m‖ *
          (∑ j ∈ range (T - m),
            K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [Polynomial.eval_finsetSum]
      calc
        ‖∑ m ∈ range T,
            (c r m • finiteBasisPolynomial s T r m).eval w‖ ≤
          ∑ m ∈ range T,
            ‖(c r m • finiteBasisPolynomial s T r m).eval w‖ :=
          norm_sum_le _ _
        _ ≤ ∑ m ∈ range T,
            ‖c r m‖ *
              (∑ j ∈ range (T - m),
                K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [eval_smul, norm_smul]
          exact mul_le_mul_of_nonneg_left
            (norm_finiteBasisPolynomial_eval_le_sum_complex hr (hdist r hr)
              (Nat.le_of_lt (Finset.mem_range.mp hm)) hK (hratio r hr))
            (norm_nonneg _)

theorem norm_polynomial_finiteRepeatedNodes_eval_le_sum_complex
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Finset ℕ} {T : ℕ} {w : ℂ} (hs : s.Nonempty) (hT : 0 < T)
    {K : ℝ} (hK : 0 ≤ K)
    (hdist : ∀ r ∈ s, 1 ≤ ‖w - (((r + 1 : ℕ) : ℂ))‖)
    (hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval w‖ ≤
        K * finiteSpacingProduct s r) :
    ‖(polynomial f (finiteRepeatedNodes s T)).eval w‖ ≤
      ∑ r ∈ s, ∑ m ∈ range T,
        ‖iteratedDeriv m f (((r + 1 : ℕ) : ℂ)) / (m.factorial : ℂ)‖ *
          (∑ j ∈ range (T - m),
            K ^ T * (2 : ℝ) ^ ((s.erase r).card * T + j)) := by
  rw [polynomial_finiteRepeatedNodes_eq_finiteHermite hf hs hT]
  exact norm_finiteHermitePolynomial_eval_le_sum_complex _ hK hdist hratio

/-- Uniform normalized-jet estimate for the actual Newton--Hermite
polynomial at an arbitrary complex target. -/
theorem norm_polynomial_finiteRepeatedNodes_eval_le_uniform_complex
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Finset ℕ} {T : ℕ} {w : ℂ} (hs : s.Nonempty) (hT : 0 < T)
    {K delta : ℝ} (hK : 0 ≤ K) (hdelta : 0 ≤ delta)
    (hdist : ∀ r ∈ s, 1 ≤ ‖w - (((r + 1 : ℕ) : ℂ))‖)
    (hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval w‖ ≤
        K * finiteSpacingProduct s r)
    (hjet : ∀ r ∈ s, ∀ m < T,
      ‖iteratedDeriv m f (((r + 1 : ℕ) : ℂ)) / (m.factorial : ℂ)‖ ≤
        delta) :
    ‖(polynomial f (finiteRepeatedNodes s T)).eval w‖ ≤
      delta * ((s.card : ℝ) * T * T *
        (K ^ T * (2 : ℝ) ^ (s.card * T + T))) := by
  have hbase0 : 0 ≤ K ^ T * (2 : ℝ) ^ (s.card * T + T) := by
    positivity
  have hsum := norm_polynomial_finiteRepeatedNodes_eval_le_sum_complex
    hf hs hT hK hdist hratio
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

/-- On the successor p. 52 circle the scaled head argument is at most `64h`. -/
theorem norm_scaledArgument_le_coprimeCircle {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ 4 * (P.R (J + 1) : ℝ)) :
    ‖scaledArgument P.q (J + 1) z‖ ≤ 64 * P.h := by
  unfold scaledArgument
  unfold VDPLParameters.R at hz
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have hqpow : (0 : ℝ) < (P.q : ℝ) ^ (J + 1) := by
    norm_num [VDPLParameters.q]
  rw [div_le_iff₀ hqpow]
  push_cast at hz ⊢
  calc
    ‖z‖ ≤ 4 * (16 * (P.q : ℝ) ^ (J + 1) * P.h) := by
      simpa [Nat.cast_pow] using hz
    _ = (64 * P.h) * (P.q : ℝ) ^ (J + 1) := by ring

/-- A predecessor `/9` derivative budget contributes at most `H/4`. -/
theorem coprime_oldDeltaPower_le_exp_quarter {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J) ≤ Real.exp (H P / 4) := by
  have hBpos : 0 < P.Bsrc := by
    have : (0 : ℝ) < P.Bsrc :=
      (Real.exp_pos 2).trans_le P.Bsrc_lower
    exact_mod_cast this
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by
    exact_mod_cast Nat.mul_pos (by norm_num) hBpos)
  have hS := P.Sstep_cast_le J
  have hlog := log_two_mul_Bsrc_le_two_h P
  have hlog0 : 0 ≤ Real.log (((2 * P.Bsrc : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hB : 1 ≤ P.Bsrc := by
      have hBreal : (1 : ℝ) ≤ P.Bsrc :=
        (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
      exact_mod_cast hBreal
    exact_mod_cast (show 1 ≤ 2 * P.Bsrc by omega)
  have hlog' : Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤ 2 * P.h := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
  have hq : P.qInvPow J ≤ 1 := by
    have h := P.qInvPow_antitone (Nat.zero_le J)
    simpa [VDPLParameters.qInvPow] using h
  have hcore : 0 ≤ P.k * P.Omega * Real.log P.OmegaOld :=
    mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hscale : P.levelScale J ≤
      P.k * P.Omega * Real.log P.OmegaOld := by
    unfold VDPLParameters.levelScale
    calc
      P.qInvPow J * P.k * P.Omega * Real.log P.OmegaOld =
          P.qInvPow J * (P.k * P.Omega * Real.log P.OmegaOld) := by ring
      _ ≤ 1 * (P.k * P.Omega * Real.log P.OmegaOld) :=
        mul_le_mul_of_nonneg_right hq hcore
      _ = P.k * P.Omega * Real.log P.OmegaOld := one_mul _
  calc
    (P.Sstep J : ℝ) * Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤
        (P.levelScale J / 9) * (2 * P.h) :=
      mul_le_mul hS hlog' hlog0
        (div_nonneg (P.levelScale_pos J).le (by norm_num))
    _ ≤ (P.k * P.Omega * Real.log P.OmegaOld / 9) *
        (2 * P.h) := by gcongr
    _ ≤ H P / 4 := by
      unfold H
      nlinarith [mul_nonneg hcore (show (0 : ℝ) ≤ P.h by positivity)]

/-- The binary remnants of all ordinary old-coordinate Delta factors cost
at most `H/32` at every level. -/
theorem oldDeltaSidePower_le_exp_H_div_thirtyTwo {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    (2 : ℝ) ^ levelOldDeltaSideSum P N ≤ Real.exp (H P / 32) := by
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by norm_num)
  have hside := levelOldDeltaSideSum_cast_le P N
  have hq : P.qInvPow N ≤ 1 := by
    have h := P.qInvPow_antitone (Nat.zero_le N)
    simpa [VDPLParameters.qInvPow] using h
  have hbase : 0 ≤ (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
      Real.log P.OmegaOld :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.rpow_nonneg P.k_pos.le _))
        P.Omega_pos.le) P.log_OmegaOld_pos.le
  have hside' : (levelOldDeltaSideSum P N : ℝ) ≤
      (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld :=
    hside.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hq hbase)
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hreserve : (8 : ℝ) ≤ (P.h : ℝ) * P.k ^ P.sigma := by
    have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
    have hk := twoHundredFiftySix_le_k_rpow_sigma P
    nlinarith [mul_le_mul hh hk (by norm_num : (0 : ℝ) ≤ 256)
      (by positivity : (0 : ℝ) ≤ (P.h : ℝ))]
  calc
    (levelOldDeltaSideSum P N : ℝ) * Real.log 2 ≤
        (levelOldDeltaSideSum P N : ℝ) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := hside'
    _ = (1 / 32 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld * 8 := by ring
    _ ≤ (1 / 32 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld * ((P.h : ℝ) * P.k ^ P.sigma) := by
      exact mul_le_mul_of_nonneg_left hreserve (by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (Real.rpow_nonneg P.k_pos.le _))
            P.Omega_pos.le) P.log_OmegaOld_pos.le)
    _ = H P / 32 := by
      unfold H
      calc
        (1 / 32 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
            Real.log P.OmegaOld * ((P.h : ℝ) * P.k ^ P.sigma) =
          (1 / 32 : ℝ) * (P.h : ℝ) *
            (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) * P.Omega *
              Real.log P.OmegaOld := by ring
        _ = (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld / 32 := by
          rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
          ring

/-- The powered head Delta costs at most `H/16` on the radius-`4R` circle. -/
theorem sourceHeadDeltaMajorant_le_exp_H_div_sixteen {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (J : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 4 * (P.R (J + 1) : ℝ)) :
    sourceHeadDeltaMajorant P (J + 1) z ≤ Real.exp (H P / 16) := by
  refine (sourceHeadDeltaMajorant_le_of_scaledNorm_le P (J + 1) z
    (norm_scaledArgument_le_coprimeCircle P J z hz)).trans ?_
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by norm_num)
  have hceil : Nat.ceil ((64 : ℝ) * P.h + P.h) = 65 * P.h := by
    norm_num only
    rw [show (64 : ℝ) * P.h + P.h = (65 * P.h : ℕ) by
      push_cast; ring, Nat.ceil_natCast]
  have hcount :
      (((Nat.ceil ((64 : ℝ) * P.h + P.h) + 1 + P.h) *
          P.LzeroPlusOne : ℕ) : ℝ) ≤
        (67 * (P.h : ℝ)) * P.LzeroScale := by
    rw [hceil]
    push_cast
    have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.one_le_h
    have hL := P.LzeroPlusOne_cast_le
    exact mul_le_mul (by nlinarith) hL (Nat.cast_nonneg _) (by positivity)
  have hlog : Real.log (2 : ℝ) ≤ Real.log P.OmegaOld :=
    P.log_two_le_log_OmegaOld
  have hks : (134 : ℝ) ≤ P.k ^ P.sigma :=
    (by norm_num : (134 : ℝ) ≤ 256).trans
      (twoHundredFiftySix_le_k_rpow_sigma P)
  calc
    (((Nat.ceil ((64 : ℝ) * P.h + P.h) + 1 + P.h) *
        P.LzeroPlusOne : ℕ) : ℝ) * Real.log 2 ≤
      ((67 * (P.h : ℝ)) * P.LzeroScale) *
        Real.log P.OmegaOld :=
      mul_le_mul hcount hlog (Real.log_nonneg (by norm_num))
        (mul_nonneg (by positivity) (by
          unfold VDPLParameters.LzeroScale
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (Real.rpow_nonneg P.k_pos.le _)) P.Omega_pos.le))
    _ = (1 / 16 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld * 134 := by
      unfold VDPLParameters.LzeroScale
      ring
    _ ≤ (1 / 16 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld * P.k ^ P.sigma := by
      exact mul_le_mul_of_nonneg_left hks (by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (by positivity))
              (Real.rpow_nonneg P.k_pos.le _)) P.Omega_pos.le)
          P.log_OmegaOld_pos.le)
    _ = H P / 16 := by
      unfold H
      calc
        (1 / 16 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
            P.Omega * Real.log P.OmegaOld * P.k ^ P.sigma =
          (1 / 16 : ℝ) * (P.h : ℝ) *
            (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) * P.Omega *
              Real.log P.OmegaOld := by ring
        _ = (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld / 16 := by
          rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
          ring

/-- The level-scaled algebraic exponential costs at most `H/32` on the
radius-`4R` circle. -/
theorem algebraicRateExponent_le_H_div_thirtyTwo {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (J : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 4 * (P.R (J + 1) : ℝ)) :
    P.qInvPow (J + 1) * sourceAlgebraicRateBound P * ‖z‖ ≤ H P / 32 := by
  have hrate := sourceAlgebraicRateBound_le_eighth P
  have hz' := norm_scaledArgument_le_coprimeCircle P J z hz
  have hscaled : P.qInvPow (J + 1) * ‖z‖ =
      ‖scaledArgument P.q (J + 1) z‖ := by
    unfold scaledArgument VDPLParameters.qInvPow
    rw [norm_div, norm_pow, Complex.norm_natCast, Nat.cast_pow]
    field_simp
  have hks := twoHundredFiftySix_le_k_rpow_sigma P
  calc
    P.qInvPow (J + 1) * sourceAlgebraicRateBound P * ‖z‖ =
        sourceAlgebraicRateBound P *
          ‖scaledArgument P.q (J + 1) z‖ := by rw [← hscaled]; ring
    _ ≤ ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld) * (64 * P.h) :=
      mul_le_mul hrate hz' (norm_nonneg _)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (Real.rpow_nonneg P.k_pos.le _))
            P.Omega_pos.le) P.log_OmegaOld_pos.le)
    _ = (1 / 32 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld * 256 := by ring
    _ ≤ (1 / 32 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld * P.k ^ P.sigma := by
      exact mul_le_mul_of_nonneg_left hks (by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (by positivity))
              (Real.rpow_nonneg P.k_pos.le _)) P.Omega_pos.le)
          P.log_OmegaOld_pos.le)
    _ = H P / 32 := by
      unfold H
      calc
        (1 / 32 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
            P.Omega * Real.log P.OmegaOld * P.k ^ P.sigma =
          (1 / 32 : ℝ) * (P.h : ℝ) *
            (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) * P.Omega *
              Real.log P.OmegaOld := by ring
        _ = (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld / 32 := by
          rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
          ring

/-- The complete algebraic closed form on the p. 52 circle costs at most
`4H/3`.  The same estimate applies to every smaller grid point. -/
theorem sourceSharpAlgebraicGrowthMajorant_le_coprimeCircle
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (J : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 4 * (P.R (J + 1) : ℝ)) :
    sourceSharpAlgebraicGrowthMajorant P (J + 1) z (P.Sstep J) ≤
      Real.exp ((4 / 3 : ℝ) * H P) := by
  have hstatic := support_sq_mul_coeffHeight_le_exp_two_thirds P hreq
  have hold := coprime_oldDeltaPower_le_exp_quarter P J
  have hside := oldDeltaSidePower_le_exp_H_div_thirtyTwo P (J + 1)
  have hhead := sourceHeadDeltaMajorant_le_exp_H_div_sixteen P J z hz
  have hrate :
      Real.exp (P.qInvPow (J + 1) * sourceAlgebraicRateBound P * ‖z‖) ≤
        Real.exp (H P / 32) :=
    Real.exp_le_exp.mpr (algebraicRateExponent_le_H_div_thirtyTwo P J z hz)
  unfold sourceSharpAlgebraicGrowthMajorant sourceSharpDeltaFactorMajorant
  calc
    (initialSupportBound P : ℝ) *
          (P.coeffHeight * ((initialSupportBound P : ℝ) *
            (sourceHeadDeltaMajorant P (J + 1) z *
              (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J *
                (2 : ℝ) ^ levelOldDeltaSideSum P (J + 1))))) *
        Real.exp (P.qInvPow (J + 1) * sourceAlgebraicRateBound P * ‖z‖) =
      ((initialSupportBound P : ℝ) *
        (P.coeffHeight * (initialSupportBound P : ℝ))) *
        (((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J) *
          sourceHeadDeltaMajorant P (J + 1) z) *
          (2 : ℝ) ^ levelOldDeltaSideSum P (J + 1)) *
        Real.exp (P.qInvPow (J + 1) * sourceAlgebraicRateBound P * ‖z‖) := by
          ring
    _ ≤ Real.exp ((2 / 3 : ℝ) * H P) *
        ((Real.exp (H P / 4) * Real.exp (H P / 16)) *
          Real.exp (H P / 32)) * Real.exp (H P / 32) := by
      have hstatic' :
          (initialSupportBound P : ℝ) *
              (P.coeffHeight * (initialSupportBound P : ℝ)) ≤
            Real.exp ((2 / 3 : ℝ) * H P) := by
        simpa only [H] using hstatic
      have hdelta :
          ((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J) *
              sourceHeadDeltaMajorant P (J + 1) z) *
              (2 : ℝ) ^ levelOldDeltaSideSum P (J + 1) ≤
            (Real.exp (H P / 4) * Real.exp (H P / 16)) *
              Real.exp (H P / 32) := by
        exact mul_le_mul
          (mul_le_mul hold hhead
            (by unfold sourceHeadDeltaMajorant; positivity)
            (Real.exp_pos _).le)
          hside (pow_nonneg (by norm_num) _) (by positivity)
      exact mul_le_mul
        (mul_le_mul hstatic' hdelta
          (by
            exact mul_nonneg
              (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
                (by unfold sourceHeadDeltaMajorant; positivity))
              (pow_nonneg (by norm_num) _))
          (by positivity))
        hrate (by positivity) (by positivity)
    _ = Real.exp ((25 / 24 : ℝ) * H P) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((4 / 3 : ℝ) * H P) := by
      apply Real.exp_le_exp.mpr
      nlinarith [H_pos P]

/-- The structural source exponent is much larger than the fixed-height
circle budget. -/
theorem four_thirds_H_le_structural_quarter {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    (4 / 3 : ℝ) * H P ≤
      sourceExponent P (P.C * Real.log P.OmegaOld) / 4 := by
  have heps : P.epsilon ≤ 1 := by
    rw [P.epsilon_eq]
    have hrank : (1 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    apply (div_le_one (by positivity : (0 : ℝ) < 6 * (P.rank + 1))).2
    nlinarith
  have hk : (13 : ℝ) ≤ P.k := by
    calc
      (13 : ℝ) = P.q := by norm_num [VDPLParameters.q]
      _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
      _ ≤ P.k := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le P.one_le_k heps
  have hC : P.C = P.k ^ 2 := by
    unfold VDPLParameters.C
    rw [P.mu_eq]
    norm_num [Real.rpow_two]
  have hlog : (P.h : ℝ) ≤ Real.log P.Bsrc := P.h_cast_le_log_Bsrc
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact mul_nonneg P.Omega_pos.le P.log_OmegaOld_pos.le
  have hcoeff : (4 / 3 : ℝ) * (P.h : ℝ) * P.k ≤
      P.k ^ 2 * Real.log P.Bsrc / 4 := by
    have h1 : (4 / 3 : ℝ) * (P.h : ℝ) * P.k ≤
        (4 / 3 : ℝ) * Real.log P.Bsrc * P.k := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (by norm_num)) P.k_pos.le
    have h2 : (4 / 3 : ℝ) * Real.log P.Bsrc * P.k ≤
        P.k ^ 2 * Real.log P.Bsrc / 4 := by
      have hlog0 : 0 ≤ Real.log P.Bsrc :=
        (by norm_num : (0 : ℝ) ≤ 2).trans P.two_le_log_Bsrc
      nlinarith [mul_nonneg hlog0 P.k_pos.le]
    exact h1.trans h2
  have hmul := mul_le_mul_of_nonneg_right hcoeff hW
  unfold H sourceExponent
  rw [hC]
  dsimp only [W] at hmul
  unfold VDPLParameters.Omega at hmul ⊢
  nlinarith

/-- The closed perturbation amplification on the p. 52 circle is bounded
at the structural quarter scale. -/
theorem scaledAmplificationClosedForm_le_structural_quarter
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (J : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 4 * (P.R (J + 1) : ℝ)) :
    (initialSupportBound P : ℝ) *
        (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ ≤
      Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
  have hscaled := norm_scaledArgument_le_coprimeCircle P J z hz
  have hqz : P.qInvPow (J + 1) * ‖z‖ ≤ 64 * P.h := by
    have heq : P.qInvPow (J + 1) * ‖z‖ =
        ‖scaledArgument P.q (J + 1) z‖ := by
      unfold scaledArgument VDPLParameters.qInvPow
      rw [norm_div, norm_pow, Complex.norm_natCast, Nat.cast_pow]
      field_simp
    simpa only [heq] using hscaled
  have hL := P.LlastZero_cast_le
  have hrank : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
  have hlognew : (1 : ℝ) ≤ Real.log P.newHeight := P.one_le_log_newHeight
  have hks := twoHundredFiftySix_le_k_rpow_sigma P
  have hmiddle :
      (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ ≤ H P := by
    have hfirst :
        (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ ≤
          (64 * P.h) * P.LlastZeroScale := by
      calc
        (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ =
            (P.qInvPow (J + 1) * ‖z‖) * P.LlastZero := by ring
        _ ≤ (64 * P.h) * P.LlastZeroScale :=
          mul_le_mul hqz hL (Nat.cast_nonneg _) (by positivity)
    refine hfirst.trans ?_
    have hLscale : P.LlastZeroScale =
        (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) * P.OmegaOld *
          Real.log P.OmegaOld := by
      unfold VDPLParameters.LlastZeroScale VDPLParameters.Omega
      field_simp [P.log_newHeight_pos.ne']
    rw [hLscale]
    unfold H VDPLParameters.Omega
    have hden : 0 < (8 * P.rank : ℝ) := by positivity
    have hrankne : (P.rank : ℝ) ≠ 0 := by positivity
    have hreserve : (8 : ℝ) ≤
        P.rank * P.k ^ P.sigma * Real.log P.newHeight := by
      calc
        (8 : ℝ) ≤ 1 * 256 * 1 := by norm_num
        _ ≤ P.rank * P.k ^ P.sigma * Real.log P.newHeight :=
          mul_le_mul (mul_le_mul hrank hks (by norm_num) (by positivity))
            hlognew (by norm_num) (by positivity)
    have hnonneg : 0 ≤ (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.OmegaOld * Real.log P.OmegaOld := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (Real.rpow_nonneg P.k_pos.le _))
          P.OmegaOld_pos.le) P.log_OmegaOld_pos.le
    have hmul := mul_le_mul_of_nonneg_left hreserve hnonneg
    have heq :
        (64 * (P.h : ℝ)) *
            ((8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) * P.OmegaOld *
              Real.log P.OmegaOld) =
          (8 * ((P.h : ℝ) * P.k ^ (1 - P.sigma) * P.OmegaOld *
            Real.log P.OmegaOld)) / P.rank := by
      field_simp [hrankne]
      ring
    rw [heq]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < P.rank)]
    calc
      8 * ((P.h : ℝ) * P.k ^ (1 - P.sigma) * P.OmegaOld *
          Real.log P.OmegaOld) ≤
        (P.rank * P.k ^ P.sigma * Real.log P.newHeight) *
          ((P.h : ℝ) * P.k ^ (1 - P.sigma) * P.OmegaOld *
            Real.log P.OmegaOld) := by
          simpa only [mul_comm, mul_left_comm, mul_assoc] using hmul
      _ = ((P.h : ℝ) * P.k * (P.OmegaOld * Real.log P.newHeight) *
          Real.log P.OmegaOld) * P.rank := by
        calc
          (P.rank * P.k ^ P.sigma * Real.log P.newHeight) *
              ((P.h : ℝ) * P.k ^ (1 - P.sigma) * P.OmegaOld *
                Real.log P.OmegaOld) =
            ((P.h : ℝ) *
              (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) *
              (P.OmegaOld * Real.log P.newHeight) *
              Real.log P.OmegaOld) * P.rank := by ring
          _ = ((P.h : ℝ) * P.k *
              (P.OmegaOld * Real.log P.newHeight) *
              Real.log P.OmegaOld) * P.rank := by
            rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
  have hs : (initialSupportBound P : ℝ) ≤ Real.exp (H P / 6) := by
    convert initialSupportBound_le_exp_sixth P hreq using 1 <;>
      unfold H <;> ring
  have hHexp : H P ≤ Real.exp (H P) := by
    have h := Real.add_one_le_exp (H P)
    nlinarith [H_pos P]
  calc
    (initialSupportBound P : ℝ) *
        (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ =
      (initialSupportBound P : ℝ) *
        ((P.qInvPow (J + 1) * P.LlastZero) * ‖z‖) := by ring
    _ ≤ Real.exp (H P / 6) * Real.exp (H P) :=
      mul_le_mul hs (hmiddle.trans hHexp)
        (mul_nonneg
          (mul_nonneg (P.qInvPow_pos _).le (Nat.cast_nonneg _))
          (norm_nonneg _))
        (Real.exp_pos _).le
    _ = Real.exp ((7 / 6 : ℝ) * H P) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) :=
      Real.exp_le_exp.mpr (by
        have h := four_thirds_H_le_structural_quarter P
        nlinarith [H_pos P])

/-- Premise-free algebraic growth on all p. 52 coprime nodes. -/
theorem coprimeNode_algebraicGrowth_le_structural_quarter
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc)
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (r : ℕ) (hr : r ∈ coprimeNodeIndices P.q (P.R (J + 1)))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J) :
    (scaledStateAlgebraicExponentialMajorant P state b bLast
        (((r + 1 : ℕ) : ℂ)) m).growth ≤
      Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
  have hrR : r + 1 ≤ P.R (J + 1) := by
    rw [mem_coprimeNodeIndices] at hr
    omega
  have hz : ‖(((r + 1 : ℕ) : ℂ))‖ ≤ 4 * (P.R (J + 1) : ℝ) := by
    rw [Complex.norm_natCast]
    exact_mod_cast (hrR.trans (Nat.le_mul_of_pos_left _ (by norm_num)))
  calc
    (scaledStateAlgebraicExponentialMajorant P state b bLast
        (((r + 1 : ℕ) : ℂ)) m).growth ≤
      sourceSharpAlgebraicGrowthMajorant P (J + 1)
        (((r + 1 : ℕ) : ℂ)) (P.Sstep J) :=
      levelAlgebraicGrowth_le_sharpClosedForm P state b bLast hb hbLastBound _ _
        hm
    _ ≤ Real.exp ((4 / 3 : ℝ) * H P) :=
      sourceSharpAlgebraicGrowthMajorant_le_coprimeCircle P hreq J _ hz
    _ ≤ Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
      apply Real.exp_le_exp.mpr
      exact (by
        exact four_thirds_H_le_structural_quarter P)

/-- Premise-free perturbation amplification on all p. 52 coprime nodes. -/
theorem coprimeNode_amplification_le_structural_quarter
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (r : ℕ) (hr : r ∈ coprimeNodeIndices P.q (P.R (J + 1)))
    (m : VDPLMultiIndex (oldRank + 1)) :
    (stateSourceMajorants P state b bLast
        (((r + 1 : ℕ) : ℂ)) m).amplificationMajorant ≤
      Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
  have hrR : r + 1 ≤ P.R (J + 1) := by
    rw [mem_coprimeNodeIndices] at hr
    omega
  have hz : ‖(((r + 1 : ℕ) : ℂ))‖ ≤ 4 * (P.R (J + 1) : ℝ) := by
    rw [Complex.norm_natCast]
    exact_mod_cast (hrR.trans (Nat.le_mul_of_pos_left _ (by norm_num)))
  exact (amplificationMajorant_le_scaledClosedForm
    P state b hbLast _ m).trans
      (scaledAmplificationClosedForm_le_structural_quarter P hreq J _ hz)

/-- The literal algebraic comparison row on every successor integer target. -/
theorem integralTarget_rowError_le_exp_neg_three_quarters
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (l : ℕ) (hlR : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel (J + 1)) :
    levelAlgebraicSourceRowError P state b bLast (l : ℂ)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld))
        (toSourceMultiIndex P m) ≤
      Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  have hz : ‖(l : ℂ)‖ ≤ 4 * (P.R (J + 1) : ℝ) := by
    rw [Complex.norm_natCast]
    exact_mod_cast hlR.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  apply levelAlgebraicSourceRowError_le_exp_neg_three_quarters_of_closedForm
    P state b hb hbLastBound hbLast (l : ℂ) (toSourceMultiIndex P m)
      (S := P.Sstep J)
      (by
        simpa only [weight_toSourceMultiIndex] using
          hm.trans (P.Slevel_succ_le_Sstep J)) hstruct hE
  · exact (sourceSharpAlgebraicGrowthMajorant_le_coprimeCircle
      P hreq J _ hz).trans
      (Real.exp_le_exp.mpr (four_thirds_H_le_structural_quarter P))
  · exact scaledAmplificationClosedForm_le_structural_quarter
      P hreq J _ hz

/-- On the successor boundary circle, the actual coprime Newton--Hermite
polynomial is exponentially small. -/
theorem norm_coprimeHermitePolynomial_boundary_le_exp_neg_half
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (hJ : P.LevelOK J)
    (hseed : CoprimeDescentAtLevel P (g state b bLast) J)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel (J + 1))
    (w : ℂ) (hw : ‖w‖ = 4 * (P.R (J + 1) : ℝ)) :
    ‖(polynomial (fun z ↦ f state b bLast z m)
        (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval w‖ ≤
      Real.exp (-sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 2) := by
  let s := coprimeNodeIndices P.q (P.R (J + 1))
  let T := P.Sstep J / 4
  let K : ℝ := (2 : ℝ) ^ (10 * P.R (J + 1))
  let E : ℝ := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let delta : ℝ := Real.exp (-2 * E / 3)
  have hs : s.Nonempty := coprimeNodeIndices_nonempty (P.R_pos (J + 1))
  have hT : 0 < T := P.Sstep_div_four_pos_of_LevelOK hJ
  have hK : 0 ≤ K := by positivity
  have hdelta : 0 ≤ delta := (Real.exp_pos _).le
  have hdiff : Differentiable ℂ (fun z ↦ f state b bLast z m) :=
    differentiable_sourceState_f state b bLast m
  have hdist : ∀ r ∈ s, 1 ≤ ‖w - (((r + 1 : ℕ) : ℂ))‖ := by
    intro r hr
    have hrR : r + 1 ≤ P.R (J + 1) := by
      dsimp only [s] at hr
      rw [mem_coprimeNodeIndices] at hr
      omega
    calc
      (1 : ℝ) ≤ 3 * (P.R (J + 1) : ℝ) := by
        exact_mod_cast (by
          have hR := P.R_pos (J + 1)
          omega : 1 ≤ 3 * P.R (J + 1))
      _ = ‖w‖ - (P.R (J + 1) : ℝ) := by rw [hw]; ring
      _ ≤ ‖w‖ - ‖(((r + 1 : ℕ) : ℂ))‖ := by
        rw [Complex.norm_natCast]
        exact sub_le_sub_left (by exact_mod_cast hrR) _
      _ ≤ ‖w - (((r + 1 : ℕ) : ℂ))‖ := norm_sub_norm_le _ _
  have hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval w‖ ≤
        K * finiteSpacingProduct s r := by
    intro r hr
    simpa only [s, K] using norm_finiteNodePolynomial_boundary_le
      (P.R_pos (J + 1)) hr hw
  have hsmallJets : ∀ r ∈ s, ∀ j < T,
      ‖iteratedDeriv j (fun z ↦ f state b bLast z m)
          (((r + 1 : ℕ) : ℂ)) / (j.factorial : ℂ)‖ ≤ delta := by
    intro r hr j hj
    have hrmem := mem_coprimeNodeIndices.mp (by simpa only [s] using hr)
    apply norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_coprimeDescent
      state b hbLast hseed hstruct hjet hE hsmall (r + 1) j
      (by omega) (by omega) hrmem.2
      (fun m' hm' ↦ coprimeNode_algebraicGrowth_le_structural_quarter
        state b bLast hb hbLastBound hreq r (by simpa only [s] using hr) m' hm')
      (fun m' _hm' ↦ coprimeNode_amplification_le_structural_quarter
        state b hbLast hreq r (by simpa only [s] using hr) m') m
    have hbudget := P.Slevel_succ_add_Sstep_div_four_le_of_LevelOK hJ
    exact (Nat.add_le_add_left (Nat.le_of_lt hj) _).trans
      ((Nat.add_le_add_right hm T).trans hbudget)
  have hpoly := norm_polynomial_finiteRepeatedNodes_eval_le_uniform_complex
    hdiff hs hT hK hdelta hdist hratio hsmallJets
  rw [finiteRepeatedNodes_coprimeNodeIndices] at hpoly
  have hloss :
      (s.card : ℝ) * T * T *
          (K ^ T * (2 : ℝ) ^ (s.card * T + T)) ≤ Real.exp (E / 6) := by
    simpa only [s, T, K, E] using
      P.coprime_boundary_fullHermiteFactor_le_exp_sixth hJ hstruct
  calc
    ‖(polynomial (fun z ↦ f state b bLast z m)
        (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval w‖ ≤
      delta * ((s.card : ℝ) * T * T *
        (K ^ T * (2 : ℝ) ^ (s.card * T + T))) := by
          simpa only [s, T, K] using hpoly
    _ ≤ Real.exp (-2 * E / 3) * Real.exp (E / 6) := by
      exact mul_le_mul_of_nonneg_left hloss hdelta
    _ = Real.exp (-E / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Erdos240.BakerSourceCoprimeGridGrowth

#print axioms
  Erdos240.BakerSourceCoprimeGridGrowth.norm_finiteNodePolynomial_boundary_le
#print axioms
  Erdos240.BakerSourceCoprimeGridGrowth.norm_polynomial_finiteRepeatedNodes_eval_le_uniform_complex
#print axioms
  Erdos240.BakerSourceCoprimeGridGrowth.coprimeNode_algebraicGrowth_le_structural_quarter
#print axioms
  Erdos240.BakerSourceCoprimeGridGrowth.coprimeNode_amplification_le_structural_quarter
#print axioms
  Erdos240.BakerSourceCoprimeGridGrowth.integralTarget_rowError_le_exp_neg_three_quarters
#print axioms
  Erdos240.BakerSourceCoprimeGridGrowth.norm_coprimeHermitePolynomial_boundary_le_exp_neg_half
