/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.WaveLimits

/-!
# Lifting waves from essential stage webs

This file supplies the concrete transport used at a ladder stage.  A wave
in the essential part of a web can be lifted to the ambient web without
changing its initial or terminal frontier.  It also identifies a source
of an essential quotient stage with the terminal of a member of the
essential accumulated warp.
-/

namespace Erdos599

open Set
open DirectedPath

universe u

namespace DWeb

variable {V : Type u} (Q : DWeb V)

/-! ## A canonical maximal rung

The ladder recursion needs to make the same kind of choice at every
successor stage.  Keeping that choice as a named definition avoids putting
an additional choice function in the statement of the ladder constructor.
The two projections below are exactly the two clauses later bundled as
`RegularExtension.HasMaximalRungs`.
-/

/-- A fixed forward-extension-maximal wave of a web.  When the web is
hindered, the choice is made from the maximal hindrances, so that the
chosen rung records that obstruction. -/
noncomputable def chosenMaximalWave : Q.Wave := by
  classical
  by_cases h : ∃ W : Set Q.DPath, Q.IsHindrance W
  · exact Classical.choose (Q.exists_maximal_hindrance h)
  · exact Classical.choose Q.exists_maximal_wave

/-- The chosen wave is forward-extension maximal. -/
theorem chosenMaximalWave_isMax : IsMax Q.chosenMaximalWave := by
  classical
  rw [chosenMaximalWave]
  split
  next h => exact (Classical.choose_spec (Q.exists_maximal_hindrance h)).1
  next _ => exact Classical.choose_spec Q.exists_maximal_wave

/-- The chosen maximal wave roofs every wave. -/
theorem roofLE_chosenMaximalWave (W : Set Q.DPath) (hW : Q.IsWave W) :
    Q.RoofLE W Q.chosenMaximalWave.1 :=
  Q.roofLE_of_isMax Q.chosenMaximalWave_isMax ⟨W, hW⟩

/-- In a hindered web the chosen maximal wave is itself a hindrance. -/
theorem chosenMaximalWave_isHindrance_of_not_isUnhindered
    (hQ : ¬ Q.IsUnhindered) :
    Q.IsHindrance Q.chosenMaximalWave.1 := by
  classical
  have h : ∃ W : Set Q.DPath, Q.IsHindrance W := by
    simpa only [IsUnhindered, not_not] using hQ
  rw [chosenMaximalWave, dif_pos h]
  exact (Classical.choose_spec (Q.exists_maximal_hindrance h)).2

/-- In a loose web there is only the trivial wave, so the canonical
maximal choice is definitionally irrelevant and is equal to it.  This is
the fact used when a ladder has exhausted its marker candidates and all
later stages mark time. -/
theorem chosenMaximalWave_eq_trivialWave (hQ : Q.IsLoose) :
    Q.chosenMaximalWave.1 = Q.trivialWave := by
  exact hQ Q.chosenMaximalWave.1 Q.chosenMaximalWave.property

/-- Pathwise lift of a family from the essential part to the ambient web. -/
def liftEssentialPartFamily
    (U : Set Q.essentialPart.DPath) : Set Q.DPath :=
  Q.liftEssentialPartPath '' U

@[simp]
theorem initial_liftEssentialPartPath
    (p : Q.essentialPart.DPath) :
    (Q.liftEssentialPartPath p).initial = p.initial := by
  rcases p with p | r <;> rfl

@[simp]
theorem terminal?_liftEssentialPartPath
    (p : Q.essentialPart.DPath) :
    Q.terminal? (Q.liftEssentialPartPath p) =
      Q.essentialPart.terminal? p := by
  rcases p with p | r <;> rfl

@[simp]
theorem initialSet_liftEssentialPartFamily
    (U : Set Q.essentialPart.DPath) :
    Q.initialSet (Q.liftEssentialPartFamily U) =
      Q.essentialPart.initialSet U := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, by simp⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Q.liftEssentialPartPath q, ⟨q, hq, rfl⟩, by simp⟩

@[simp]
theorem terminalFrontier_liftEssentialPartFamily
    (U : Set Q.essentialPart.DPath) :
    Q.terminalFrontier (Q.liftEssentialPartFamily U) =
      Q.essentialPart.terminalFrontier U := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hp⟩
    exact ⟨q, hq, by simpa using hp⟩
  · rintro ⟨q, hq, hqterm⟩
    exact ⟨Q.liftEssentialPartPath q, ⟨q, hq, rfl⟩,
      by simpa using hqterm⟩

/-- Lifting along the induced essential-part inclusion preserves
pairwise disjointness. -/
theorem IsWarp.liftEssentialPartFamily
    {U : Set Q.essentialPart.DPath} (hU : Q.essentialPart.IsWarp U) :
    Q.IsWarp (Q.liftEssentialPartFamily U) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint (Q.liftEssentialPartPath p₀).support
    (Q.liftEssentialPartPath q₀).support
  rw [Q.support_liftEssentialPartPath, Q.support_liftEssentialPartPath]
  apply hU hp₀ hq₀
  intro h
  exact hpq (congrArg Q.liftEssentialPartPath h)

/-- Every vertex of a finite target path can itself reach the target along
the corresponding suffix. -/
theorem finitePath_support_subset_reachableToTarget
    (p : FinitePath Q.graph) (hp : p.finish ∈ Q.target) :
    p.support ⊆ Q.reachableToTarget := by
  intro x hx
  refine ⟨p.suffixFrom x hx, p.suffixFrom_start x hx, ?_⟩
  rwa [p.suffixFrom_finish x hx]

/-- A wave in the essential induced subweb lifts to a wave in the ambient
web.  Separation is proved by restricting each ambient target path to the
essential part; every vertex of such a path is target-reachable. -/
theorem isWave_liftEssentialPartFamily
    {U : Set Q.essentialPart.DPath} (hU : Q.essentialPart.IsWave U) :
    Q.IsWave (Q.liftEssentialPartFamily U) := by
  refine ⟨hU.1.liftEssentialPartFamily Q, ?_, ?_⟩
  · rw [Q.initialSet_liftEssentialPartFamily]
    exact hU.2.1.trans Set.inter_subset_left
  · intro a ha p hp
    have hreach : p.support ⊆ Q.reachableToTarget :=
      Q.finitePath_support_subset_reachableToTarget p hp.2
    let hrestrict : ∀ {x y : V}, Q.graph.Adj x y →
        x ∈ p.support → y ∈ p.support →
          Q.essentialPart.graph.Adj x y :=
      fun e hu hv ↦ ⟨e, hreach hu, hreach hv⟩
    let q : FinitePath Q.essentialPart.graph :=
      p.restrictGraphOnSupport hrestrict
    have hqstart : q.start = a := by
      simpa only [q, FinitePath.restrictGraphOnSupport] using hp.1
    have hqfinish : q.finish ∈ Q.essentialPart.target := by
      change q.finish ∈ Q.target
      simpa only [q, FinitePath.restrictGraphOnSupport] using hp.2
    have ha' : a ∈ Q.essentialPart.source := ⟨ha, ⟨p, hp⟩⟩
    obtain ⟨x, hxq, hxT⟩ := hU.2.2 ha' q ⟨hqstart, hqfinish⟩
    refine ⟨x, ?_, ?_⟩
    · have hsupport : q.support = p.support :=
        FinitePath.support_restrictGraphOnSupport p hrestrict
      rw [hsupport] at hxq
      exact hxq
    · rw [Q.terminalFrontier_liftEssentialPartFamily]
      exact hxT

/-- Under the exact accumulated-stage separation invariant, the source of
the quotient by the full accumulated frontier is its essential frontier.
No restriction on the initial vertices of accumulated paths is needed;
in particular this applies in the presence of fresh marker paths. -/
theorem quotient_source_eq_essential_terminalFrontier_of_roofsSource
    {W : Set Q.DPath}
    (hroof : Q.source ⊆ Q.roof (Q.terminalFrontier W)) :
    (Q.quotient (Q.terminalFrontier W)).source =
      Q.essential (Q.terminalFrontier W) := by
  rw [Q.quotient_source, Set.union_comm]
  exact RelationalRoof.essential_union_eq_of_subset_roof
    Q.graph.Adj Q.target hroof

/-- Every source point of the essential quotient stage is the terminal of
an essential member of the accumulated warp.  This is the concrete bridge
`A(ℰ(Γ / W)) = ter[Ess(W)]` used in the ladder successor step. -/
theorem exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
    {W : Set Q.DPath}
    (hroof : Q.source ⊆ Q.roof (Q.terminalFrontier W))
    {x : V}
    (hx : x ∈
      (Q.quotient (Q.terminalFrontier W)).essentialPart.source) :
    ∃ p ∈ Q.essentialWarpPart W, Q.terminal? p = some x := by
  have hxSource : x ∈ (Q.quotient (Q.terminalFrontier W)).source := hx.1
  rw [Q.quotient_source_eq_essential_terminalFrontier_of_roofsSource
    hroof] at hxSource
  rw [← Q.terminalFrontier_essentialWarpPart W] at hxSource
  exact hxSource

end DWeb

end Erdos599
