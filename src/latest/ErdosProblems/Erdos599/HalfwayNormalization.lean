/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction

/-!
# Transporting half-way linkages through normalization

Normalization only deletes edges.  Exact finite linkages therefore lift
memberwise, and the corresponding roof can only grow.  In particular a
stop-over which is trimmed in the normalized web is still trimmed in the
original web.

Quotient unhinderedness and height require more care: normalization need
not commute with quotienting, and a roof in the normalized web need not be
a roof after the deleted edges are restored.  The final theorems in this
file state the precise stability assumptions under which those two pieces,
and hence a bounded-altitude half-way linkage, transport.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Deleting edges can only enlarge a roof. -/
theorem DWeb.roof_subset_normalized_roof (Gamma : DWeb V) (S : Set V) :
    Gamma.roof S ⊆ Gamma.normalized.roof S := by
  intro x hx p hp
  let q := p.lift
    (fun {_ _} (he : Gamma.normalized.graph.Adj _ _) => he.1)
  have hq : Gamma.IsTargetPathFrom x q := by
    exact ⟨hp.1, hp.2⟩
  obtain ⟨s, hsq, hsS⟩ := hx q hq
  exact ⟨s, by simpa [q] using hsq, hsS⟩

/-- Every point essential after normalization was already essential before
normalization. -/
theorem DWeb.essential_normalized_subset (Gamma : DWeb V) (S : Set V) :
    Gamma.normalized.essential S ⊆ Gamma.essential S := by
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro hroof
  exact hs.2 (Gamma.roof_subset_normalized_roof (S \ {s}) hroof)

namespace CardinalInduction

/-- Trimmedness descends from the normalized web to the original web. -/
theorem IsTrimmedSeparator.of_normalized {C : Set V}
    (hC : IsTrimmedSeparator Gamma.normalized C) :
    IsTrimmedSeparator Gamma C := by
  apply Set.Subset.antisymm
  · exact Gamma.essential_subset C
  · intro c hc
    exact Gamma.essential_normalized_subset C (hC.symm ▸ hc)

/-- The suffix certificate in `LinksToTarget` is unchanged when a normalized
finite path is regarded as a path in the original graph. -/
theorem FinitePathSuffixMeets.liftNormalized
    {q : DirectedPath.FinitePath Gamma.normalized.graph}
    {a : V} {B : Set V} (h : FinitePathSuffixMeets q a B) :
    FinitePathSuffixMeets
      (q.lift (fun {_ _} (he : Gamma.normalized.graph.Adj _ _) => he.1))
      a B := by
  obtain ⟨before, after, hsupport, b, hbB, hb⟩ := h
  refine ⟨before, after, ?_, b, hbB, hb⟩
  simpa only [DirectedPath.FinitePath.lift,
    DirectedPath.Walk.support_lift] using hsupport

/-- The designated-source-to-target condition lifts memberwise from the
normalized web. -/
theorem LinksToTarget.liftNormalized {W : Set Gamma.normalized.DPath}
    {A0 : Set V} (hW : LinksToTarget Gamma.normalized W A0) :
    LinksToTarget Gamma (Gamma.liftNormalizedFamily W) A0 := by
  intro a ha
  obtain ⟨p, hpW, q, hpq, hinter, hsuffix⟩ := hW a ha
  subst p
  let q' := q.lift
    (fun {_ _} (he : Gamma.normalized.graph.Adj _ _) => he.1)
  refine ⟨Gamma.liftNormalizedPath (.inl q),
    ⟨(.inl q : Gamma.normalized.DPath), hpW, rfl⟩,
    q', rfl, ?_, ?_⟩
  · simpa only [q', DirectedPath.FinitePath.support_lift] using hinter
  · exact hsuffix.liftNormalized

/-- If the normalized quotient by the stop-over is literally the
normalization of the original quotient, quotient unhinderedness descends. -/
theorem quotientUnhindered_of_normalized
    {C : Set V}
    (hcommute : (Gamma.quotient C).normalized =
      Gamma.normalized.quotient C)
    (h : (Gamma.normalized.quotient C).IsUnhindered) :
    (Gamma.quotient C).IsUnhindered := by
  apply DWeb.IsUnhindered.of_normalized
  rw [hcommute]
  exact h

/-- A normalized stop-over lifts once quotient normalization is known to
commute for its stop-over set. -/
theorem IsHalfwayStopover.liftNormalized
    {W : Set Gamma.normalized.DPath} {C : Set V}
    (hcommute : (Gamma.quotient C).normalized =
      Gamma.normalized.quotient C)
    (hC : IsHalfwayStopover Gamma.normalized W C) :
    IsHalfwayStopover Gamma (Gamma.liftNormalizedFamily W) C := by
  exact
    { linkage := hC.linkage.liftNormalized
      minimal := hC.minimal.of_normalized
      quotient_unhindered :=
        quotientUnhindered_of_normalized hcommute
          hC.quotient_unhindered }

/-- Witness-oriented stop-over transport.  When the construction already
retains unhinderedness of the quotient in the original web, no commutation
identity is needed. -/
theorem IsHalfwayStopover.liftNormalized_of_quotientUnhindered
    {W : Set Gamma.normalized.DPath} {C : Set V}
    (hC : IsHalfwayStopover Gamma.normalized W C)
    (hquotient : (Gamma.quotient C).IsUnhindered) :
    IsHalfwayStopover Gamma (Gamma.liftNormalizedFamily W) C := by
  exact
    { linkage := hC.linkage.liftNormalized
      minimal := hC.minimal.of_normalized
      quotient_unhindered := hquotient }

/-- Exact witness-level condition needed to transport height through
normalization.  For every normalized quotient wave it supplies an original
quotient wave whose frontier roof contains the old normalized frontier
roof.  This formulation avoids imposing any unnecessarily global equality
of roofs. -/
def HeightWitnessTransportFromNormalized (Gamma : DWeb V) : Prop :=
  ∀ (X : Set V) (W : Set (Gamma.normalized.quotient X).DPath),
    (Gamma.normalized.quotient X).IsWave W →
      ∃ U : Set (Gamma.quotient X).DPath,
        (Gamma.quotient X).IsWave U ∧
          Gamma.normalized.roof
              ((Gamma.normalized.quotient X).terminalFrontier W) ⊆
            Gamma.roof ((Gamma.quotient X).terminalFrontier U)

/-- A height witness transports exactly under
`HeightWitnessTransportFromNormalized`. -/
theorem IsHeightWitness.of_normalized
    (htransport : HeightWitnessTransportFromNormalized Gamma)
    {Z X : Set V} (hX : IsHeightWitness Gamma.normalized Z X) :
    IsHeightWitness Gamma Z X := by
  obtain ⟨hXsource, W, hW, hroof⟩ := hX
  obtain ⟨U, hU, hroofTransport⟩ := htransport X W hW
  exact ⟨by simpa using hXsource, U, hU,
    hroof.trans hroofTransport⟩

/-- Consequently every explicit normalized height bound is an original
height bound under the same witness transport. -/
theorem HeightAtMost.of_normalized
    (htransport : HeightWitnessTransportFromNormalized Gamma)
    {Z : Set V} {kappa : Cardinal.{u}}
    (hZ : HeightAtMost Gamma.normalized Z kappa) :
    HeightAtMost Gamma Z kappa := by
  obtain ⟨X, hX, hcard⟩ := hZ
  exact ⟨X, hX.of_normalized htransport, hcard⟩

/-- Full transport of a qualified half-way linkage.  The two hypotheses
are precisely the pieces not supplied merely by edge deletion:

* normalized quotienting must agree with quotienting after normalization
  for the (existentially chosen) stop-over;
* normalized height witnesses must remain valid after restoring edges.
-/
theorem IsHalfwayLinkageOfAltitude.liftNormalized
    {A0 : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.normalized.DPath}
    (hquotient : ∀ C : Set V,
      (Gamma.quotient C).normalized = Gamma.normalized.quotient C)
    (hheight : HeightWitnessTransportFromNormalized Gamma)
    (hW : IsHalfwayLinkageOfAltitude Gamma.normalized A0 kappa W) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa
      (Gamma.liftNormalizedFamily W) := by
  obtain ⟨C, hC, hCheight⟩ := hW.exists_stopover
  exact halfwayLinkageOfAltitude_of_stopover
    (hC.liftNormalized (hquotient C))
    hW.2.1.liftNormalized
    (hCheight.of_normalized hheight)

/-- The most direct witness-oriented transport theorem.  It is useful when
the terminal construction was performed with normalized paths but kept its
quotient-unhindered and height certificates in the original web. -/
theorem IsHalfwayLinkageOfAltitude.liftNormalized_of_stopover
    {A0 C : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.normalized.DPath}
    (hW : IsHalfwayLinkageOfAltitude Gamma.normalized A0 kappa W)
    (hC : IsHalfwayStopover Gamma.normalized W C)
    (hquotient : (Gamma.quotient C).IsUnhindered)
    (hheight : HeightAtMost Gamma C kappa) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa
      (Gamma.liftNormalizedFamily W) := by
  exact halfwayLinkageOfAltitude_of_stopover
    (hC.liftNormalized_of_quotientUnhindered hquotient)
    hW.2.1.liftNormalized hheight

end CardinalInduction
end Erdos599
