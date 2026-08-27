/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLeftObstructionCount
import ErdosProblems.Erdos207.QuasiMomentNormalization

/-! # Left-moment loss at the actual reserve-candidate scale -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.sourceLeft_normalized_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j s : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix k) j F y z)
    (e : Sym2 V) (S : Finset V) (hoff : ¬ e.IsDiag) (hp : 0 < p) (hp1 : p ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C) (hscale : z ≤ y*r^2*p^3*S.card)
    (epsilon : ℝ≥0) (hepsilon : 0 < epsilon) (hS : S.Nonempty) :
    let d := j-1
    let K : ℝ≥0 := (boundedIntersectionMomentCoefficient d s : ℝ≥0) *
      (2 : ℝ≥0)^(j-2)*(k.val+3 : ℕ)*(j^k.val : ℕ)*y
    L.probability (fun ω ↦ epsilon*p^2*r^2*S.card ≤
      (sourceLeftObstructedVertices (W.prefix k) F e S G (initial ω) (later ω) (reserve ω)).card) ≤
      ((C^2)^d*K*p/epsilon)^s +
        b*((C^2)^d*((2 : ℝ≥0)^(j-2)*(Fintype.card V+1 : ℝ≥0)^(3*j))/(epsilon*p^2*r^2*S.card))^s := by
  dsimp only
  let K : ℝ≥0 := (boundedIntersectionMomentCoefficient (j-1) s : ℝ≥0) *
    (2 : ℝ≥0)^(j-2)*(k.val+3 : ℕ)*(j^k.val : ℕ)*y
  have hn : (0 : ℝ≥0) < S.card := by exact_mod_cast card_pos.mpr hS
  have hR : 0 < epsilon*p^2*r^2*S.card := by positivity
  have hb := hstrong.sourceLeft_canonical_tail (s := s) hdis hsource e S hoff hp1 hr1 hC hscale
    (epsilon*p^2*r^2*S.card) hR
  dsimp only at hb
  apply hb.trans_eq
  have hnorm := quasi_moment_normalized_bound (C^2) (K*r^2) p S.card epsilon r b
    ((2 : ℝ≥0)^(j-2)*(Fintype.card V+1 : ℝ≥0)^(3*j)) 2 2 (j-1) s hp hn hepsilon hr
  have hmain : (C^2)^(j-1)*(K*r^2)*p/(epsilon*r^2) = (C^2)^(j-1)*K*p/epsilon := by field_simp
  rw [hmain] at hnorm
  simpa only [K, mul_assoc] using hnorm

end

end Erdos207
