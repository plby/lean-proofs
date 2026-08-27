/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiMoment
import ErdosProblems.Erdos207.SourceQuasiObstructionCount

/-! # Canonical quasi-moment tails for actual forbidden extension vertices -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.sourceQuasi_canonical_tail
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
    (hscale : z ≤ y * p ^ (hmax + 1) * S.card) (R : ℝ≥0) (hR : 0 < R) :
    let d := j - 3 + B.card
    let κ : ℝ≥0 := (2 : ℝ≥0) ^ (j - 2) * (i.val + 3 : ℕ) * (j ^ i.val : ℕ) *
      y * p ^ (B.card + 1) * S.card
    L.probability (fun ω ↦ R ≤
      (sourceQuasiObstructedVertices (W.prefix i) F e S B G (initial ω) (later ω)).card) ≤
      (C ^ (s * d) * (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ s +
        b * ((2 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) ^ s)) / R ^ s := by
  dsimp only
  apply L.sourceQuasiObstructedVertices_tail (W.prefix i) F e S B G initial later s R _ hR
  exact hstrong.sourceQuasi_canonical_moment_le hdis hnonempty hki hsource e S B hoff heB hB hp hC hscale

end

end Erdos207
