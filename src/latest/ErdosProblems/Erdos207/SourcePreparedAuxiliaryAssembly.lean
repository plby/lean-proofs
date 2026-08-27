/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePreparedReserveData
import ErdosProblems.Erdos207.PreparedAuxiliaryRegularization

/-! # Condition the actual auxiliary degrees and construct their fixed envelopes -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem eventually_regularize_source_prepared_law
    (q b Bexp k Rmin R gapDecay : ℕ) (eta0 : ℝ≥0) (heta0 : 0 < eta0) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V] {ell : ℕ},
      ∀ (P : FiniteLaw Omega) (W : Vortex V ell) (i : Fin ell) (full : ForbiddenFamilyOn V)
        (Gamma : SimpleGraph V) (ambient : TripleSystemOn V)
        (G : Omega → SimpleGraph V) (A I D B : Omega → TripleSystemOn V)
        (bits : Omega → Sym2 V → Bool) (p eta xi r C beta : ℝ≥0)
        (epsilon theta : ℝ) (supply h : ℕ),
      SourcePreparedReserveData P W i full Gamma ambient G A I D B bits
        p eta xi r C beta eta0 epsilon theta supply h →
      ∀ (F : ℕ → ForbiddenFamilyOn V) (y z : ℕ → ℝ≥0) (s decay errorExponent : ℕ)
        (priorCoefficient error : ℝ≥0),
      Fintype.card V ≤ t ^ R → 3*R+decay ≤ s → 3*R+R*(3*q)*s+decay ≤ errorExponent →
      p ≤ 1 → 1 ≤ C → (∀ j ∈ Icc 4 q, 1 ≤ y j) →
      1 ≤ p ^ 3 * (W.prefix i.castSucc).terminalSize →
      beta ≤ priorCoefficient / (t : ℝ≥0) ^ errorExponent →
      (∀ a, (W.U a).Nonempty) →
      (∀ j ∈ Icc 4 q, SourceVortexWellSpread (W.prefix i.castSucc) j (F j) (y j) (z j)) →
      (∀ j ∈ Icc 4 q, ∀ j' ∈ Icc j q,
        z j' ≤ y j' * p ^ (3*(j-3)) * (W.prefix i.castSucc).terminalSize) →
      sourceAllAuxiliaryDegreeFailure q s t decay C priorCoefficient ≤ error → error < 1 →
      t ^ ksssPowerDenominatorExponent q b Bexp k Rmin ≤ (W.U i.castSucc).card →
      1 / (t : ℝ≥0) ^ b ≤ p → p ≤ 1 / t → (∀ j ∈ Icc 4 q, y j ≤ t) →
      (∀ j ∈ Icc 4 q, (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient i.val j' 2 * y j') ≤ t) →
      let Good := sourceAuxiliaryDegreeGood W i.castSucc q t F B (fun omega ↦ I omega ∪ D omega) p y
      ∃ hpos : 0 < P.probability Good, 1-error ≤ P.probability Good ∧
        SourcePreparedReserveData (P.conditionSubtype Good hpos) W i full Gamma ambient
          (G ∘ Subtype.val) (A ∘ Subtype.val) (I ∘ Subtype.val) (D ∘ Subtype.val)
          (B ∘ Subtype.val) (bits ∘ Subtype.val) p eta xi r (C/(1-error)) beta eta0
          epsilon theta supply h ∧
        (∀ x : {omega // Good omega}, sourceAuxiliaryDegreeGood W i.castSucc q t F
          (B ∘ Subtype.val) (fun x ↦ I x.val ∪ D x.val) p y x) ∧
        ∃ inst : ∀ x : {omega // Good omega}, Nonempty {T // T ∈ B x.val},
        letI := inst
        ∃ Lstar : ℕ → (x : {omega // Good omega}) → Finset (Finset {T // T ∈ B x.val}),
        ∃ envelope : ℕ → ForbiddenFamilyOn V,
          (∀ j ∈ Icc 4 q,
            FixedRandomOrderResult (P.conditionSubtype Good hpos) (W.prefix i.castSucc)
              (fun x ↦ Function.Embedding.subtype (fun T ↦ T ∈ B x.val)) j (8192*t)
              (fun x ↦ finiteHypergraphOnSubset (B x.val)
                (localForbiddenConfigurations ((Icc 4 q).biUnion F) (B x.val) (I x.val ∪ D x.val) j))
              (fun x ↦ (Ico 4 j).biUnion (fun a ↦ Lstar a x)) (F j)
              (terminalRandomConfigurations (W.prefix i.castSucc) j)
              (y j) (z j) ((t : ℝ≥0)^4) (1/(t : ℝ≥0)^gapDecay) (Lstar j) (envelope j)) ∧
          (P.conditionSubtype Good hpos).probability (fun x ↦
            ∃ j ∈ Icc 4 q, 8192*t < finiteHypergraphDegreeGap (Lstar j x)) ≤
            ((Icc 4 q).card : ℝ≥0)/(t : ℝ≥0)^gapDecay := by
  obtain ⟨T, hT1, hT⟩ := eventually_regularize_prepared_auxiliary_inputs q b Bexp k Rmin R gapDecay
    (192/eta0) (by positivity)
  refine ⟨T, hT1, ?_⟩
  intro t ht Omega V _ _ _ _ ell P W i full Gamma ambient G A I D B bits p eta xi r C beta
    epsilon theta supply h data F y z s decay errorExponent priorCoefficient error hN hs hL hp hC hy
    hdensity hbeta hnonempty hF hz hfailure herror hscale hpLo hpHi hyHi hcoeff
  dsimp only
  let Good := sourceAuxiliaryDegreeGood W i.castSucc q t F B (fun omega ↦ I omega ∪ D omega) p y
  have hgeometry : P.SupportedOn (fun omega ↦
      (∀ U ∈ B omega, (W.prefix i.castSucc).level U = Fin.last i.val) ∧
      ∀ U ∈ B omega, ∀ e ∈ tripleEdgeFinset U,
        e ∈ graphEdges Gamma ∧ e ∉ (coveredGraph (I omega ∪ D omega)).edgeSet) :=
    fun omega _ ↦ ⟨(data.available_geometry omega).1, (data.available_geometry omega).2.1⟩
  have hbad : P.probability (fun omega ↦ ¬ Good omega) ≤ error :=
    (data.distribution.toResidual.all_auxiliary_degree_failure_le q R s decay errorExponent t
      priorCoefficient B F y z (hT1.trans ht) hN hs hL hp hC hy hdensity hbeta hnonempty hF hz
      hgeometry).trans hfailure
  have hlower : 1-error ≤ P.probability Good := by
    rw [P.probability_not Good] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  have hpos : 0 < P.probability Good := (tsub_pos_iff_lt.mpr herror).trans_le hlower
  let Pc := P.conditionSubtype Good hpos
  have hdata := data.conditionSubtype Good hpos error herror hlower
  have hdegree : ∀ x : {omega // Good omega}, sourceAuxiliaryDegreeGood W i.castSucc q t F
      (B ∘ Subtype.val) (fun x ↦ I x.val ∪ D x.val) p y x := fun x ↦ x.property
  let inst : ∀ x : {omega // Good omega}, Nonempty {T // T ∈ B x.val} := fun x ↦ by
    obtain ⟨T, hT⟩ := data.nonempty x.val
    exact ⟨⟨T, hT⟩⟩
  refine ⟨hpos, hlower, hdata, hdegree, inst, ?_⟩
  exact hT t ht Pc W i.castSucc (fun x ↦ B x.val) (fun x ↦ I x.val ∪ D x.val) F p y z
    (fun x ↦ (data.protected_geometry x.val).2.1) hF hscale hN hpLo hpHi hyHi hcoeff
    (fun x ↦ data.mass x.val) hdegree

end

end Erdos207
