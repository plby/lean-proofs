/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiTail
import ErdosProblems.Erdos207.QuasiMomentNormalization

/-! # The actual quasi-obstruction tail at the expected extension scale -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.sourceQuasi_normalized_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j hmax s q : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k i : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    (hnonempty : ∀ a, (W.U a).Nonempty) (hki : k ≤ i)
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix i) j F y z)
    (e : Sym2 V) (S B : Finset V) (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (hB : B.card ≤ hmax) (hp : 0 < p) (hp1 : p ≤ 1) (hC : 1 ≤ C)
    (hscale : z ≤ y * p ^ (hmax + 1) * S.card)
    (epsilon eta : ℝ≥0) (hepsilon : 0 < epsilon) (heta : 0 < eta) (hS : S.Nonempty) :
    let d := j - 3 + B.card
    let K : ℝ≥0 := (boundedIntersectionMomentCoefficient d s : ℝ≥0) *
      (2 : ℝ≥0) ^ (j - 2) * (i.val + 3 : ℕ) * (j ^ i.val : ℕ) * y
    L.probability (fun ω ↦ epsilon * p ^ B.card * eta ^ q * S.card ≤
      (sourceQuasiObstructedVertices (W.prefix i) F e S B G (initial ω) (later ω)).card) ≤
      (C ^ d * K * p / (epsilon * eta ^ q)) ^ s +
        b * (C ^ d * ((2 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3*j)) /
          (epsilon * p ^ B.card * eta ^ q * S.card)) ^ s := by
  dsimp only
  have hS' : (0 : ℝ≥0) < S.card := by exact_mod_cast card_pos.mpr hS
  have hR : 0 < epsilon * p ^ B.card * eta ^ q * S.card := by positivity
  have hb := hstrong.sourceQuasi_canonical_tail (s := s) hdis hnonempty hki hsource
    e S B hoff heB hB hp1 hC hscale (epsilon * p ^ B.card * eta ^ q * S.card) hR
  dsimp only at hb
  apply hb.trans_eq
  simpa only [mul_assoc] using quasi_moment_normalized_bound C
    ((boundedIntersectionMomentCoefficient (j-3+B.card) s : ℝ≥0) *
      (2 : ℝ≥0) ^ (j-2) * (i.val+3 : ℕ) * (j ^ i.val : ℕ) * y)
    p S.card epsilon eta b ((2 : ℝ≥0) ^ (j-2) * (Fintype.card V+1 : ℝ≥0) ^ (3*j))
    B.card q (j-3+B.card) s hp hS' hepsilon heta

end

end Erdos207
