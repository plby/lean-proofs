/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTwoDensityQuasiWeights
import ErdosProblems.Erdos207.SourceLeftJointInclusion
import ErdosProblems.Erdos207.AdditiveConfigurationMoment

/-! # The source left moment with its two residual reserve spokes -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.sourceLeft_canonical_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j s : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix k) j F y z)
    (e : Sym2 V) (S : Finset V) (hoff : ¬ e.IsDiag) (hp : p ≤ 1) (hr : r ≤ 1) (hC : 1 ≤ C)
    (hscale : z ≤ y*r^2*p^3*S.card) :
    let d := j-1
    let κ : ℝ≥0 := (2 : ℝ≥0)^(j-2)*(k.val+3 : ℕ)*(j^k.val : ℕ)*y*r^2*p^3*S.card
    L.expectation (fun ω ↦ selectedCount
      (fun x : sourceQuasiMarkings (W.prefix k) F e S e.toFinset ↦ x.1.coordinates e.toFinset)
      (sourceLeftRealizedCoordinates G (initial ω) (later ω) (reserve ω)) ^ s) ≤
      (C^2)^(s*d) * (((boundedIntersectionMomentCoefficient d s : ℝ≥0)*κ)^s +
        b*((2 : ℝ≥0)^(j-2)*(Fintype.card V+1 : ℝ≥0)^(3*j))^s) := by
  dsimp only
  let d := j-1
  let κ : ℝ≥0 := (2 : ℝ≥0)^(j-2)*(k.val+3 : ℕ)*(j^k.val : ℕ)*y*r^2*p^3*S.card
  let π := sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹) (vortexTripleWeight (W.prefix k) p) (p*r)
  let R := fun ω ↦ sourceLeftRealizedCoordinates G (initial ω) (later ω) (reserve ω)
  have hsize : ∀ x : sourceQuasiMarkings (W.prefix k) F e S e.toFinset,
      (x.1.coordinates e.toFinset).card ≤ d := by
    intro x
    have hd := mem_sourceQuasiMarkings_iff.mp x.2
    rw [SourceQuasiMarking.coordinates_card hd, (hsource.uniform x.1.system hd.mem_family).1,
      Sym2.card_toFinset_of_not_isDiag e hoff]
    have hj := hsource.order
    dsimp only [d]
    omega
  have hjoint : ∀ H : Finset (SourceQuasiCoordinate V), H.card ≤ s*d →
      L.probability (fun ω ↦ H ⊆ R ω) ≤ (C^2)^(s*d)*setWeight π H + (C^2)^(s*d)*b := by
    intro H hH
    apply (hstrong.sourceLeft_joint_inclusion hdis hC H).trans
    calc
      _ ≤ (C^2)^(s*d)*(setWeight π H+b) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_pow₀ hC) hH) zero_le
      _ = _ := by ring
  have hκ := hsource.sourceLeft_canonical_hasExtensionBound e S hoff p r hp hr hscale
  have hb := configurationMomentBound_additive L
    (fun x : sourceQuasiMarkings (W.prefix k) F e S e.toFinset ↦ x.1.coordinates e.toFinset)
    R π ((C^2)^(s*d)) ((C^2)^(s*d)*b) κ hsize hκ hjoint
  have hcount : (Fintype.card (sourceQuasiMarkings (W.prefix k) F e S e.toFinset) : ℝ≥0) ≤
      (2 : ℝ≥0)^(j-2)*(Fintype.card V+1 : ℝ≥0)^(3*j) := by
    rw [Fintype.card_coe]
    exact_mod_cast card_sourceQuasiMarkings_le_polynomial (W := W.prefix k) (S := S)
      (fun E hE ↦ (hsource.uniform E hE).2) (fun E hE ↦ (hsource.uniform E hE).1) (Subset.refl e.toFinset)
  apply hb.trans
  calc
    _ ≤ (C^2)^(s*d)*((boundedIntersectionMomentCoefficient d s : ℝ≥0)*κ)^s +
        ((C^2)^(s*d)*b)*((2 : ℝ≥0)^(j-2)*(Fintype.card V+1 : ℝ≥0)^(3*j))^s := by gcongr
    _ = _ := by ring

end

end Erdos207
