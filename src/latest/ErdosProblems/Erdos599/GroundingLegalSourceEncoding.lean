/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInitialBlueprint
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# Legal-ladder source coverage and auxiliary source encodings

The final warp of a legal ladder covers every original source vertex by the
initial vertex of a grounded parent.  This fact is distinct from the source
encoding used by the Section 8 auxiliary web: finite recorded parents are
encoded by their terminal, while grounded recorded rays are encoded by a
fresh proxy.  The latter conclusion is proved here for chosen grounded
records.  The stronger assertion that every grounded limiting parent has
such an encoding is exposed as a proposition, but is not assumed.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingLegalSourceEncoding

open DirectedPath

universe u v

variable {V : Type u} {J : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (J : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma J

abbrev LV (_I : Input Gamma J) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V J

/-- A particular auxiliary vertex encodes a ladder parent: an old vertex
encodes the terminal of a finite recorded parent, while a proxy encodes its
represented infinite parent. -/
def EncodedAt (I : Input Gamma J) (parent : Gamma.DPath) (z : LV I) : Prop :=
  (∃ p : FinitePath Gamma.graph,
      parent = .inl p ∧ p.finish ∈ I.finiteSource ∧
        z = .old p.finish) ∨
    ∃ i : J, parent = I.proxyPath i ∧ z = .proxy i

/-- A ladder parent has a source encoding when one of its finite-terminal or
proxy encodings is an actual source vertex of the auxiliary web. -/
def IsSourceEncoded (I : Input Gamma J) (parent : Gamma.DPath) : Prop :=
  ∃ z : I.lambda.source, EncodedAt I parent z.1

/-- The source-subtype packaging in `IsSourceEncoded` is equivalent to the
literal finite-terminal/proxy alternative. -/
theorem isSourceEncoded_iff (I : Input Gamma J) (parent : Gamma.DPath) :
    IsSourceEncoded I parent ↔
      (∃ p : FinitePath Gamma.graph,
          parent = .inl p ∧ p.finish ∈ I.finiteSource) ∨
        ∃ i : J, parent = I.proxyPath i := by
  constructor
  · rintro ⟨z, hz | hz⟩
    · obtain ⟨p, hp, hfinish, _⟩ := hz
      exact Or.inl ⟨p, hp, hfinish⟩
    · obtain ⟨i, hp, _⟩ := hz
      exact Or.inr ⟨i, hp⟩
  · rintro (hfinite | hproxy)
    · obtain ⟨p, hp, hfinish⟩ := hfinite
      let z : I.lambda.source :=
        ⟨.old p.finish, (I.mem_lambda_source_old p.finish).2 hfinish⟩
      exact ⟨z, Or.inl ⟨p, hp, hfinish, rfl⟩⟩
    · obtain ⟨i, hp⟩ := hproxy
      let z : I.lambda.source :=
        ⟨.proxy i, I.mem_lambda_source_proxy i⟩
      exact ⟨z, Or.inr ⟨i, hp, rfl⟩⟩

/-- The exact stronger coverage assertion one would need in order to encode
all grounded parents of an arbitrary auxiliary input.  Legal-ladder source
coverage alone does not imply it, since a limiting parent need not itself be
a chosen obstruction record. -/
def AllGroundedLadderParentsSourceEncoded (I : Input Gamma J) : Prop :=
  ∀ parent ∈ I.ladder.paths,
    PopularAuxiliary.IsGroundedPath Gamma parent →
      IsSourceEncoded I parent

open Cardinal

variable {kappa : Cardinal.{u}}

/-- Every original source vertex is the initial vertex of a grounded parent
in the concrete auxiliary input's limiting ladder warp. -/
theorem KappaLadder.exists_grounded_ladderParent_of_mem_source
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {x : V} (hx : x ∈ Gamma.source) :
    ∃ parent ∈ (L.popularAuxiliaryInput hlegal).ladder.paths,
      parent.initial = x ∧
        PopularAuxiliary.IsGroundedPath Gamma parent := by
  obtain ⟨parent, hparent, hinitial⟩ :=
    hlegal.source_subset_initialSet_limitWarp hx
  refine ⟨parent, ?_, hinitial, ?_⟩
  · exact hparent
  · change parent.initial ∈ Gamma.source
    rw [hinitial]
    exact hx

/-- Set-level specialization of legal-ladder source coverage to the ladder
stored in the concrete popular-auxiliary input. -/
theorem KappaLadder.source_subset_initialSet_popularAuxiliary_ladder
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    Gamma.source ⊆
      Gamma.initialSet (L.popularAuxiliaryInput hlegal).ladder.paths := by
  simpa [Erdos599.DWeb.KappaLadder.popularAuxiliaryInput] using
    hlegal.source_subset_initialSet_limitWarp

/-- A chosen grounded obstruction record has its canonical Section 8
source encoding, including the explicit tagged vertex in `Lambda.source`.
Finite records use their terminal; ray records use their grounded proxy. -/
theorem KappaLadder.chosen_grounded_isSourceEncoded
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (a : Ladder.Stage kappa) (parent : Gamma.DPath)
    (hchosen : L.chosen a = some parent)
    (hground : PopularAuxiliary.IsGroundedPath Gamma parent) :
    IsSourceEncoded (L.popularAuxiliaryInput hlegal) parent := by
  let I := L.popularAuxiliaryInput hlegal
  have haGround : a ∈ L.phiGround :=
    ⟨parent, hchosen, hground⟩
  have haPhi : a ∈ L.phi :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hlegal.validBookkeeping).2 ⟨parent, hchosen⟩
  rcases parent with p | r
  · have haFinite : a ∈ L.phiFinite := by
      refine ⟨haPhi, ?_⟩
      intro haInfinite
      obtain ⟨q, hq, hqRay⟩ :=
        L.bookkeeping.chosen_isRay_of_mem_phiInfinite
          hlegal.validBookkeeping haInfinite
      have hqp : q = (.inl p : Gamma.DPath) :=
        Option.some.inj (hq.symm.trans hchosen)
      subst q
      change (some p.finish : Option V) = none at hqRay
      cases hqRay
    have hpFinite : p.finish ∈ I.finiteSource := by
      change p.finish ∈ L.groundedFiniteTerminalSet
      exact ⟨a, ⟨haGround, haFinite⟩, .inl p, hchosen, rfl⟩
    let z : I.lambda.source :=
      ⟨.old p.finish, (I.mem_lambda_source_old p.finish).2 hpFinite⟩
    exact ⟨z, Or.inl ⟨p, rfl, hpFinite, rfl⟩⟩
  · have haInfinite : a ∈ L.phiInfinite := by
      refine ⟨haPhi, .inr r, ?_, rfl⟩
      exact L.bookkeeping.chosen_mem_available
        hlegal.validBookkeeping hchosen
    let i : L.groundedInfiniteRecords :=
      ⟨.inr r, ⟨a, ⟨haGround, haInfinite⟩, hchosen⟩⟩
    let z : I.lambda.source :=
      ⟨.proxy i, I.mem_lambda_source_proxy i⟩
    exact ⟨z, Or.inr ⟨i, rfl, rfl⟩⟩

/-- The concrete, specialized form of the not-assumed stronger assertion.
This name lets later code state precisely when all grounded limiting parents,
rather than merely chosen grounded records, have auxiliary source encodings. -/
def KappaLadder.AllGroundedLimitParentsSourceEncoded
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) : Prop :=
  AllGroundedLadderParentsSourceEncoded
    (L.popularAuxiliaryInput hlegal)

end GroundingLegalSourceEncoding
end Erdos599
