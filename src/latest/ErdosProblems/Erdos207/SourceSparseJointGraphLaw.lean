/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceSparseProcessCrude
import ErdosProblems.Erdos207.SparseJointGraphLaw

/-! # Conditional sparse mixed laws from actual fixed-source moments -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.source_sparse_joint_graph_law_failure_le
    {D V I : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype I]
    {ell : ℕ} {P : FiniteLaw D} {W : Vortex V ell} {current : Fin (ell + 1)}
    {baseGraph : SimpleGraph V} {initial later : D → TripleSystemOn V} {p C beta : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed P W current baseGraph initial later p C beta)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (q b B k t Rmin c s R decay errorExponent zExponent : ℕ)
    (horizon : D → ℕ) (J : D → ForbiddenFamilyOn (W.U current))
    (G : D → SimpleGraph (W.U current)) (a coeff : D → ℕ → ℝ) (E A eta : D → ℝ)
    (S₀ : D → GreedyStateOn (W.U current)) (Good : D → Prop)
    (hparams : ∀ d, Good d → KSSSPowerParameters (J d) q (horizon d) b B k t Rmin
      (a d) (coeff d) (E d) (A d))
    (ht : 32 ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ (W.U current).card)
    (htime : ∀ d, horizon d ≤ (W.U current).card ^ 2)
    (hInv : ∀ d, GreedyInvariant (J d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (F : I → ForbiddenFamilyOn V) (order : I → ℕ) (y z : I → ℝ≥0)
    (hF : ∀ i, SourceVortexWellSpread (W.prefix current) (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (hprior : P.SupportedOn (fun d ↦
      Disjoint (mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (S₀ d).available)
        (initial d ∪ later d) ∧
      ∀ D ∈ mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (J d),
        D ⊆ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (S₀ d).available ∧
        ∃ i H, H ∈ F i ∧ D ⊆ H ∧ H \ D ⊆ initial d ∪ later d))
    (Z priorCoefficient : ℝ≥0) (hZ : 1 ≤ Z) (hz : ∀ i, z i ≤ Z)
    (hZpower : Z ≤ (t : ℝ≥0) ^ zExponent)
    (hconstant : sourceCrudeUniformCoefficient current.val q (Fintype.card I) 1 1 ≤ t)
    (hk : 2 * zExponent + 2 * q * (5 * b + 3) + 2 ≤ k)
    (hambient : Fintype.card V ≤ t ^ R) (hs : 6 * R + decay ≤ s)
    (herrorExponent : 6 * R + (6 * q * R) * s + decay ≤ errorExponent)
    (hbeta : beta ≤ priorCoefficient / (t : ℝ≥0) ^ errorExponent)
    (hEcard : ∀ d, Good d → ((graphEdges (G d)).card : ℝ) = E d)
    (htri : ∀ d, Good d → ∀ T ∈ (S₀ d).available, tripleEdgeFinset T ⊆ graphEdges (G d))
    (hregular : ∀ d, Good d → KSSSInitialRegularity (J d) (S₀ d) q (graphPairFamily (G d))
      (a d) (E d) (A d) (eta d))
    (hfamily : ∀ d, Good d → ∀ H ∈ J d, H ⊆ (S₀ d).available)
    (heta : ∀ d, Good d → 0 ≤ eta d)
    (hetaSmall : ∀ d, Good d → eta d ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B))
    (hcb : 2 * c ≤ b)
    (hfloor : ∀ d, Good d → ∀ i : ℕ, i ≤ horizon d → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity (E d) i)
    (badInput bandError delta : ℝ≥0) (hdelta : 0 < delta) (hsmall : delta < 1)
    (herror : (1 / 2 : ℝ≥0) ^ t ≤ delta)
    (hinput : P.probability (fun d ↦ ¬ Good d) ≤ badInput)
    (hbandError : 2 * (((W.U current).card : ℝ) ^ 2 +
      (q + 1 : ℝ) ^ 2 * ((W.U current).card : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t ≤ bandError) :
    P.probability (fun d ↦ ¬ (Good d ∧ IsGraphMixedProductBound
      (stoppedGreedyStateLaw (horizon d) (J d)
        (fun i S ↦ Good d ∧ KSSSPowerActive (J d) (graphPairFamily (G d)) q b B k t
          (a d) (E d) (A d) i S) (S₀ d))
      (fun S ↦ S.chosen) (G d) (Real.toNNReal (ksssEdgeDensity (E d) (horizon d)))
      (Real.toNNReal (E d) / Real.toNNReal (A d)) (ksssSparseGraphProductConstant q (coeff d)) delta)) ≤
      (badInput + bandError + sourceSparseCrudeFailure q s (Fintype.card I) t decay C priorCoefficient) /
        delta := by
  have hcrude := hstrong.source_sparse_crude_failure_le hp hC hnonempty q b B k t Rmin s R decay
    errorExponent zExponent horizon J G a coeff E A S₀ Good hparams ht hscale htime hInv hchosen
    F order y z hF horder hidentical hprior Z priorCoefficient hZ hz hZpower hconstant hk
    hambient hs herrorExponent hbeta
  exact sparse_joint_graph_law_failure_le P horizon J G q b B k t Rmin c a coeff E A eta S₀ Good
    hparams hInv hchosen hEcard htri hregular hfamily heta hetaSmall hcb hfloor
    badInput bandError (sourceSparseCrudeFailure q s (Fintype.card I) t decay C priorCoefficient)
    delta hdelta hsmall herror hinput (by simpa only [Fintype.card_coe] using hbandError) hcrude

end

end Erdos207
