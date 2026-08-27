/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiMomentWeights
import ErdosProblems.Erdos207.SourceQuasiJointInclusion
import ErdosProblems.Erdos207.AdditiveConfigurationMoment

/-! # The proper quasi-moment under the corrected residual master law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.sourceQuasi_canonical_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j hmax s : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k i : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    (hnonempty : ∀ a, (W.U a).Nonempty) (hki : k ≤ i)
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix i) j F y z)
    (e : Sym2 V) (S B : Finset V) (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (hB : B.card ≤ hmax) (hp : p ≤ 1) (hC : 1 ≤ C)
    (hscale : z ≤ y * p ^ (hmax + 1) * S.card) :
    let d := j - 3 + B.card
    let κ : ℝ≥0 := (2 : ℝ≥0) ^ (j - 2) * (i.val + 3 : ℕ) * (j ^ i.val : ℕ) *
      y * p ^ (B.card + 1) * S.card
    L.expectation (fun ω ↦ selectedCount
      (fun x : sourceQuasiMarkings (W.prefix i) F e S B ↦ x.1.coordinates B)
      (sourceQuasiRealizedCoordinates G (initial ω) (later ω)) ^ s) ≤
      C ^ (s * d) * (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ s +
        b * ((2 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) ^ s) := by
  dsimp only
  let d := j - 3 + B.card
  let κ : ℝ≥0 := (2 : ℝ≥0) ^ (j - 2) * (i.val + 3 : ℕ) * (j ^ i.val : ℕ) *
    y * p ^ (B.card + 1) * S.card
  let π := sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹) (vortexTripleWeight (W.prefix i) p) p
  let R := fun ω ↦ sourceQuasiRealizedCoordinates G (initial ω) (later ω)
  have hsize : ∀ x : sourceQuasiMarkings (W.prefix i) F e S B, (x.1.coordinates B).card ≤ d := by
    intro x
    have hd := mem_sourceQuasiMarkings_iff.mp x.2
    rw [SourceQuasiMarking.coordinates_card hd, (hsource.uniform x.1.system hd.mem_family).1]
    dsimp only [d]
    omega
  have hjoint : ∀ H : Finset (SourceQuasiCoordinate V), H.card ≤ s * d →
      L.probability (fun ω ↦ H ⊆ R ω) ≤ C ^ (s * d) * setWeight π H + C ^ (s * d) * b := by
    intro H hH
    have hb := (hstrong.future_stage hnonempty hki).sourceQuasi_joint_inclusion hdis H
    apply hb.trans
    calc
      _ ≤ C ^ (s * d) * (setWeight π H + b) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hH) zero_le
      _ = _ := by ring
  have hκ := hsource.sourceQuasi_canonical_hasExtensionBound hoff heB hB p hp hscale
  have hb := configurationMomentBound_additive L
    (fun x : sourceQuasiMarkings (W.prefix i) F e S B ↦ x.1.coordinates B) R π
    (C ^ (s * d)) (C ^ (s * d) * b) κ hsize hκ hjoint
  have hcount : (Fintype.card (sourceQuasiMarkings (W.prefix i) F e S B) : ℝ≥0) ≤
      (2 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j) := by
    rw [Fintype.card_coe]
    exact_mod_cast card_sourceQuasiMarkings_le_polynomial (W := W.prefix i) (S := S)
      (fun E hE ↦ (hsource.uniform E hE).2) (fun E hE ↦ (hsource.uniform E hE).1) heB
  apply hb.trans
  calc
    _ ≤ C ^ (s * d) * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ s +
        (C ^ (s * d) * b) * ((2 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) ^ s := by gcongr
    _ = _ := by ring

end

end Erdos207
