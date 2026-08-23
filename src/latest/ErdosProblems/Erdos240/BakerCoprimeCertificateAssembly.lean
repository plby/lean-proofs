/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeHermiteTarget
import ErdosProblems.Erdos240.BakerCoprimeOuterEstimate

/-!
# Assembly of the p. 52 coprime interpolation certificate

The contour is the circle `|z| = 4R`.  This module turns the exact nodal
quotient `3^(-#nodes*T)`, a boundary numerator estimate, and a Hermite
polynomial estimate into the certificate consumed by the Liouville
alternative.  In particular the Cauchy radius/gap cost is proved to be at
most `4/3`.
-/

noncomputable section

namespace Erdos240.BakerCoprimeCertificateAssembly

open Complex Metric
open BakerCoprimeInterpolation BakerCoprimeOuterEstimate
open BakerRationalExtrapolation HermiteInterpolation

theorem four_mul_radius_div_gap_le_four_thirds
    {R l : ℕ} (hR : 0 < R) (hl : l ≤ R) :
    (4 * (R : ℝ)) / (4 * (R : ℝ) - dist (l : ℂ) 0) ≤ 4 / 3 := by
  have hdist : dist (l : ℂ) 0 = (l : ℝ) := by
    rw [dist_zero_right, Complex.norm_natCast]
  rw [hdist]
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hlreal : (l : ℝ) ≤ R := by exact_mod_cast hl
  have hden : 0 < 4 * (R : ℝ) - l := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- The source-shaped certificate constructor.  Its strict numerical input
is exactly `polynomial + (4/3) * outer * nodalDecay < lower`.
-/
def coprimeInterpolationCertificateOfBounds
    {q R T l : ℕ} (hR : 0 < R) (hT : 0 < T)
    (hl : 1 ≤ l) (hlR : l ≤ R) (hlq : ¬l.Coprime q)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {lower polynomialBound outer decay : ℝ}
    (hpoly0 : 0 ≤ polynomialBound) (houter0 : 0 ≤ outer)
    (hdecay0 : 0 ≤ decay)
    (hboundary : ∀ w, ‖w‖ = 4 * (R : ℝ) →
      ‖f w - (polynomial f (coprimeNodes q R T)).eval w‖ ≤ outer)
    (hpoly : ‖(polynomial f (coprimeNodes q R T)).eval (l : ℂ)‖ ≤
      polynomialBound)
    (hratio : ∀ w, ‖w‖ = 4 * (R : ℝ) →
      ‖coprimeNodalProduct q R T (l : ℂ)‖ /
          ‖coprimeNodalProduct q R T w‖ ≤ decay)
    (hstrict : polynomialBound + (4 / 3 : ℝ) * outer * decay < lower) :
    CoprimeInterpolationCertificate q R T f (l : ℂ) lower := by
  let nodes := coprimeNodes q R T
  let targetNorm := nodeProductNorm nodes (l : ℂ)
  let boundaryBound := outer * decay / targetNorm
  have htarget_ne : nodeProduct nodes (l : ℂ) ≠ 0 := by
    apply nodeProduct_ne_zero_of_forall_ne
    intro a ha hla
    rw [mem_coprimeNodes_iff] at ha
    obtain ⟨r, _hr1, _hrR, hrcop, _hT, rfl⟩ := ha
    apply hlq
    have hcast : l = r := by exact_mod_cast hla
    simpa only [hcast] using hrcop
  have htargetPos : 0 < targetNorm := by
    dsimp only [targetNorm]
    rw [← norm_nodeProduct]
    exact norm_pos_iff.mpr htarget_ne
  refine ⟨{
    nodes := nodes
    center := 0
    radius := 4 * (R : ℝ)
    boundaryBound := boundaryBound
    polynomialBound := polynomialBound
    differentiable := hf
    radius_pos := by positivity
    target_mem := ?_
    boundaryBound_nonneg := by
      exact div_nonneg (mul_nonneg houter0 hdecay0) htargetPos.le
    nodes_mem := ?_
    boundary := ?_
    polynomial_target := hpoly
    strict_budget := ?_
  }, rfl⟩
  · rw [mem_ball, dist_zero_right, Complex.norm_natCast]
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hlreal : (l : ℝ) ≤ R := by exact_mod_cast hlR
    linarith
  · intro a ha
    rw [mem_coprimeNodes_iff] at ha
    obtain ⟨r, _hr1, hrR, _hrcop, _hT, rfl⟩ := ha
    rw [mem_ball, dist_zero_right, Complex.norm_natCast]
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hrreal : (r : ℝ) ≤ R := by exact_mod_cast hrR
    linarith
  · intro w hw
    rw [mem_sphere, dist_zero_right] at hw
    have hwnode : nodeProduct nodes w ≠ 0 := by
      apply nodeProduct_ne_zero_of_forall_ne
      intro a ha hwa
      rw [mem_coprimeNodes_iff] at ha
      obtain ⟨r, _hr1, hrR, _hrcop, _hT, rfl⟩ := ha
      have hn := congrArg norm hwa
      rw [hw, Complex.norm_natCast] at hn
      have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
      have hrreal : (r : ℝ) ≤ R := by exact_mod_cast hrR
      linarith
    have hwNorm : 0 < nodeProductNorm nodes w := by
      rw [← norm_nodeProduct]
      exact norm_pos_iff.mpr hwnode
    have houterDiv :
        ‖f w - (polynomial f nodes).eval w‖ / nodeProductNorm nodes w ≤
          outer / nodeProductNorm nodes w :=
      div_le_div_of_nonneg_right (hboundary w hw) hwNorm.le
    have hratio' : targetNorm / nodeProductNorm nodes w ≤ decay := by
      dsimp only [targetNorm, nodes]
      rw [← norm_nodeProduct, nodeProduct_coprimeNodes,
        ← norm_nodeProduct, nodeProduct_coprimeNodes]
      exact hratio w hw
    calc
      ‖f w - (polynomial f nodes).eval w‖ / nodeProductNorm nodes w ≤
          outer / nodeProductNorm nodes w := houterDiv
      _ = outer * (targetNorm / nodeProductNorm nodes w) / targetNorm := by
        field_simp [htargetPos.ne', hwNorm.ne']
      _ ≤ outer * decay / targetNorm := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio' houter0) htargetPos.le
  · have hgapPos :
        0 < 4 * (R : ℝ) - dist (l : ℂ) 0 := by
      rw [dist_zero_right, Complex.norm_natCast]
      have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
      have hlreal : (l : ℝ) ≤ R := by exact_mod_cast hlR
      linarith
    have hradial := four_mul_radius_div_gap_le_four_thirds hR hlR
    have hrewrite :
        targetNorm *
            ((4 * (R : ℝ)) *
              (boundaryBound /
                (4 * (R : ℝ) - dist (l : ℂ) 0))) =
          ((4 * (R : ℝ)) /
              (4 * (R : ℝ) - dist (l : ℂ) 0)) * outer * decay := by
      dsimp only [boundaryBound]
      field_simp [htargetPos.ne', hgapPos.ne']
    rw [hrewrite]
    apply lt_of_le_of_lt _ hstrict
    gcongr

#print axioms coprimeInterpolationCertificateOfBounds

end Erdos240.BakerCoprimeCertificateAssembly
