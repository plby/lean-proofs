/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CountableExtensionFinal
import ErdosProblems.Erdos599.SingularProtectedLowerSelection

/-!
# Corrected protected cardinal induction

This logical assembly uses the actual protected split half-way output.
It does not use the historical exact-frontier strengthening. The countable
and singular extension cases below are concrete proved theorems. The regular
and half-way construction engines remain explicit conditional hypotheses;
this module does not assert that those unfinished engines are available.

All auxiliary webs are edge subwebs of one fixed ambient web. This is the
provenance needed to preserve hereditary subdivision incidence internally.
-/

noncomputable section

open Set Cardinal

namespace Erdos599.CardinalInduction.ProtectedCardinalAssembly

open Blueprint.LinkageBlueprint.CardinalInduction
open RegularProtectedAmbientRebuild SingularProtectedLowerSelection

universe u

variable {V : Type u}

/-- Extension uniformly over the unhindered edge subwebs of `Base`. -/
def ExtensionAtFor (Base : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ H : DWeb V,
    (∀ {x y : V}, H.graph.Adj x y → Base.graph.Adj x y) →
    H.IsUnhindered → ExtensionClauseAt H kappa

/-- Only normalized subwebs require the actual protected half-way output. -/
def HalfwayAtFor (Base : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ H : DWeb V,
    (∀ {x y : V}, H.graph.Adj x y → Base.graph.Adj x y) →
    H.IsNormalized → H.IsUnhindered →
    ∀ A0 : Set V, A0 ⊆ H.source → #A0 = kappa →
      Nonempty (LocalizedProtectedHalfwayGeometry H A0 kappa)

/-- The extension clause is obtained before half-way at this cardinal. -/
def ProtectedAtFor (Base : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ExtensionAtFor Base kappa ∧ (aleph0 ≤ kappa → HalfwayAtFor Base kappa)

/-- The simultaneous assertion at strictly smaller cardinals. -/
def ProtectedBelowFor (Base : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ rho, rho < kappa → ProtectedAtFor Base rho

/-- Extension through the current cardinal, as used by Assertion 9.31. -/
def ExtensionThroughFor (Base : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ rho, rho ≤ kappa → ExtensionAtFor Base rho

namespace ExtensionThroughFor

/-- A small-source auxiliary edge subweb is linkable using extension only.
Apply the extension clause at the auxiliary's own source cardinal and take
the empty linkage on the empty complementary source set.  No half-way
statement at a smaller cardinal is involved. -/
theorem linkable_of_source_mk_le
    {Base H : DWeb V} {kappa : Cardinal.{u}}
    (hext : ExtensionThroughFor Base kappa)
    (hHBase : ∀ {x y : V}, H.graph.Adj x y → Base.graph.Adj x y)
    (hH : H.IsUnhindered) (hsource : #H.source ≤ kappa) :
    IsLinkable H := by
  apply linkable_of_extension_at_source_card H
  exact hext #H.source hsource H hHBase hH

end ExtensionThroughFor

/-- The remaining regular construction, stated at normalized input only. -/
def RegularEngineFor (Base : DWeb V) : Prop :=
  ∀ kappa : Cardinal.{u}, aleph0 < kappa → kappa.IsRegular →
    ∀ G : DWeb V,
      (∀ {x y : V}, G.graph.Adj x y → Base.graph.Adj x y) →
      G.IsNormalized → G.IsUnhindered →
      ExtensionBelowFor G kappa → ProtectedHalfwayBelowFor G kappa →
      ExtensionClauseAt G kappa

/-- The remaining protected half-way construction. No endpoint-purity
condition at its stopover is imposed on the completed target track. -/
def HalfwayEngineFor (Base : DWeb V) : Prop :=
  ∀ kappa : Cardinal.{u}, aleph0 ≤ kappa →
    ExtensionThroughFor Base kappa → HalfwayAtFor Base kappa

namespace ProtectedBelowFor

/-- Lower extension transfers to a subweb by literal edge inclusion. -/
theorem extensionBelow
    {Base G : DWeb V} {kappa : Cardinal.{u}}
    (hlower : ProtectedBelowFor Base kappa)
    (hGBase : ∀ {x y : V}, G.graph.Adj x y → Base.graph.Adj x y) :
    ExtensionBelowFor G kappa := by
  intro rho hrho H hHG hH
  exact (hlower rho hrho).1 H (fun {_ _} hxy ↦ hGBase (hHG hxy)) hH

/-- The normalized protected half-way clause transfers in the same way. -/
theorem protectedHalfwayBelow
    {Base G : DWeb V} {kappa : Cardinal.{u}}
    (hlower : ProtectedBelowFor Base kappa)
    (hGBase : ∀ {x y : V}, G.graph.Adj x y → Base.graph.Adj x y) :
    ProtectedHalfwayBelowFor G kappa := by
  intro rho hrho hrhoInf H hHG hNorm hH A0 hA0 hcard
  exact (hlower rho hrho).2 hrhoInf H
    (fun {_ _} hxy ↦ hGBase (hHG hxy)) hNorm hH A0 hA0 hcard

end ProtectedBelowFor

/-- Concrete cardinal dispatch, with only the regular branch left as its
explicit engine premise. Normalization and both other branches are proved. -/
theorem extensionAt_of_lower
    {Base : DWeb V} (hregular : RegularEngineFor Base)
    (kappa : Cardinal.{u}) (hlower : ProtectedBelowFor Base kappa) :
    ExtensionAtFor Base kappa := by
  intro G hGBase hG
  have hnormBase : ∀ {x y : V},
      G.normalized.graph.Adj x y → Base.graph.Adj x y :=
    fun {_ _} hxy ↦ hGBase hxy.1
  cases extensionCardinalCase kappa with
  | zero hkappa =>
      subst kappa
      exact extensionClauseAt_countable G hG zero_le
  | countable _ hkappa =>
      exact extensionClauseAt_countable G hG hkappa
  | uncountableRegular hkappa hreg =>
      apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
      exact hregular kappa hkappa hreg G.normalized hnormBase
        G.normalized_isNormalized hG.normalized
        (hlower.extensionBelow hnormBase)
        (hlower.protectedHalfwayBelow hnormBase)
  | uncountableSingular hkappa hsingular =>
      apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
      exact SingularProtectedLowerSelection.extensionClauseAt_of_protectedLower
        kappa hkappa hsingular G.normalized G.normalized_isNormalized hG.normalized
        (hlower.extensionBelow hnormBase)
        (hlower.protectedHalfwayBelow hnormBase)

/-- The current extension step and strict lower induction together supply
all of the half-way construction's extension calls. -/
theorem extensionThrough_of_lower_and_current
    {Base : DWeb V} {kappa : Cardinal.{u}}
    (hlower : ProtectedBelowFor Base kappa)
    (hcurrent : ExtensionAtFor Base kappa) :
    ExtensionThroughFor Base kappa := by
  intro rho hrho
  rcases hrho.lt_or_eq with hlt | rfl
  · exact (hlower rho hlt).1
  · exact hcurrent

/-- Well-founded simultaneous induction under the two remaining concrete
construction engines. This is an honest conditional assembly theorem. -/
theorem protectedAt_of_engines
    {Base : DWeb V} (hregular : RegularEngineFor Base)
    (hhalfway : HalfwayEngineFor Base) :
    ∀ kappa : Cardinal.{u}, ProtectedAtFor Base kappa := by
  intro kappa
  induction kappa using Cardinal.lt_wf.induction with
  | h kappa ih =>
      have hlower : ProtectedBelowFor Base kappa := fun rho hrho ↦ ih rho hrho
      have hext : ExtensionAtFor Base kappa :=
        extensionAt_of_lower hregular kappa hlower
      exact ⟨hext, fun hkappa ↦ hhalfway kappa hkappa
        (extensionThrough_of_lower_and_current hlower hext)⟩

/-- Full linkability follows at the source cardinal, with the empty
complementary linkage. The engine premises remain visible. -/
theorem linkable_of_engines
    (Base : DWeb V) (hBase : Base.IsUnhindered)
    (hregular : RegularEngineFor Base) (hhalfway : HalfwayEngineFor Base) :
    IsLinkable Base := by
  apply linkable_of_extension_at_source_card Base
  exact (protectedAt_of_engines hregular hhalfway #Base.source).1
    Base (fun {_ _} hxy ↦ hxy) hBase

#print axioms extensionAt_of_lower
#print axioms protectedAt_of_engines
#print axioms linkable_of_engines

end Erdos599.CardinalInduction.ProtectedCardinalAssembly
