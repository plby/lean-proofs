/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayExactFrontierClause

/-!
# Exact-frontier simultaneous cardinal induction

This is the source-faithful refinement of `CardinalInductionAt`.  It keeps
the exact terminal frontier supplied by the half-way construction, while
providing a projection to the existing induction interface for all regular
and auxiliary-web consumers.
-/

noncomputable section

open Cardinal

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- The simultaneous induction assertion with the exact-frontier half-way
clause retained. -/
def ExactFrontierCardinalInductionAt (Gamma : DWeb V)
    (kappa : Cardinal.{u}) : Prop :=
  CardinalInductionAt Gamma kappa ∧
    (aleph0 ≤ kappa → ExactFrontierHalfwayClauseAt Gamma kappa)

/-- Uniform exact-frontier induction at one cardinal. -/
def UniversalExactFrontierCardinalInductionAt (V : Type u)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ Gamma : DWeb V, Gamma.IsUnhindered →
    ExactFrontierCardinalInductionAt Gamma kappa

/-- All exact-frontier induction hypotheses strictly below `kappa`. -/
def UniversalExactFrontierCardinalInductionBelow (V : Type u)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ mu, mu < kappa → UniversalExactFrontierCardinalInductionAt V mu

namespace ExactFrontierCardinalInductionAt

theorem extension {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (h : ExactFrontierCardinalInductionAt Gamma kappa) :
    ExtensionClauseAt Gamma kappa :=
  h.1.extension

theorem exactHalfway {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (h : ExactFrontierCardinalInductionAt Gamma kappa)
    (hkappa : aleph0 ≤ kappa) :
    ExactFrontierHalfwayClauseAt Gamma kappa :=
  h.2 hkappa

/-- Existing consumers can forget exactness without changing their proofs. -/
theorem toCardinalInductionAt {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (h : ExactFrontierCardinalInductionAt Gamma kappa) :
    CardinalInductionAt Gamma kappa :=
  h.1

theorem halfway {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (h : ExactFrontierCardinalInductionAt Gamma kappa)
    (hkappa : aleph0 ≤ kappa) :
    HalfwayClauseAt Gamma kappa :=
  (h.exactHalfway hkappa).toHalfwayClauseAt

end ExactFrontierCardinalInductionAt

namespace UniversalExactFrontierCardinalInductionBelow

/-- Forget exact frontiers in every lower-cardinal hypothesis. -/
theorem toUniversalCardinalInductionBelow
    {kappa : Cardinal.{u}}
    (h : UniversalExactFrontierCardinalInductionBelow V kappa) :
    UniversalCardinalInductionBelow V kappa := by
  intro mu hmu Gamma hGamma
  exact (h mu hmu Gamma hGamma).toCardinalInductionAt

/-- Direct exact half-way accessor at a lower cardinal. -/
theorem exactHalfway
    {kappa mu : Cardinal.{u}}
    (h : UniversalExactFrontierCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hmuInfinite : aleph0 ≤ mu) :
    ExactFrontierHalfwayClauseAt Gamma mu :=
  (h mu hmu Gamma hGamma).exactHalfway hmuInfinite

end UniversalExactFrontierCardinalInductionBelow

/-- Well-founded assembly retaining the exact frontier at every infinite
cardinal. -/
theorem universalExactFrontierCardinalInduction_of_steps
    (extensionStep : ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V kappa →
        UniversalExtensionClauseAt V kappa)
    (halfwayStep : ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      aleph0 ≤ kappa →
        ∀ Gamma : DWeb V, Gamma.IsUnhindered →
          ExactFrontierHalfwayClauseAt Gamma kappa)
    (separatingHalfwayStep : ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      aleph0 ≤ kappa →
        ∀ Gamma : DWeb V, Gamma.IsUnhindered →
          SeparatingHalfwayClauseAt Gamma kappa) :
    ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionAt V kappa := by
  intro kappa
  induction kappa using Cardinal.lt_wf.induction with
  | h kappa ih =>
      have hlower :
          UniversalExactFrontierCardinalInductionBelow V kappa :=
        fun mu hmu ↦ ih mu hmu
      have hext : UniversalExtensionClauseAt V kappa :=
        extensionStep kappa hlower
      intro Gamma hGamma
      exact ⟨⟨hext Gamma hGamma,
          fun hkappa ↦
            separatingHalfwayStep kappa hlower hext hkappa Gamma hGamma⟩,
        fun hkappa ↦ halfwayStep kappa hlower hext hkappa Gamma hGamma⟩

/-- The exact-frontier universal result projects pointwise to the existing
public simultaneous induction result. -/
theorem universalCardinalInduction_of_exactFrontier
    (h : ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionAt V kappa) :
    ∀ kappa : Cardinal.{u}, UniversalCardinalInductionAt V kappa := by
  intro kappa Gamma hGamma
  exact (h kappa Gamma hGamma).toCardinalInductionAt

#print axioms
  UniversalExactFrontierCardinalInductionBelow.toUniversalCardinalInductionBelow
#print axioms universalExactFrontierCardinalInduction_of_steps
#print axioms universalCardinalInduction_of_exactFrontier

end CardinalInduction
end Erdos599
