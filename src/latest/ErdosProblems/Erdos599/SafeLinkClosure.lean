/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CommonQuotient
import ErdosProblems.Erdos599.FiniteWaveReduction
import ErdosProblems.Erdos599.SafeLink

/-!
# The countable closure in Proposition 6.3

This file joins the two already-proved halves of the closing-up argument in
Section 6 of Aharoni--Berger.  The first half constructs the literal sequence
`X_i` and the maximal quotient waves `W_i`, and proves that the raw union of
the `X_i` is countable.  The second half works after all waves have been
transported to one common quotient.  It proves that the finite closure clauses
pass to the countable up-arrow.

The two layers are deliberately kept separate.  This makes the use of the raw
union `⋃ i, X i` explicit, and prevents quotient transport from being hidden in
an equality of path types.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

theorem hasFiniteCharacter_cast {H K : DWeb V} (hHK : H = K)
    {W : Set H.DPath} (hW : H.HasFiniteCharacter W) :
    ∀ {p : K.DPath}, p ∈ (hHK ▸ W) →
      ∃ q : DirectedPath.FinitePath K.graph, p = .inl q := by
  subst K
  exact hW

theorem hasFiniteCharacter_wave_cast {H K : DWeb V} (hHK : H = K)
    (W : H.Wave) (hW : H.HasFiniteCharacter W.1) :
    ∀ {p : K.DPath}, p ∈ (hHK ▸ W).1 →
      ∃ q : DirectedPath.FinitePath K.graph, p = .inl q := by
  subst K
  exact hW

/-- Quotienting a wave by the admissible-suffix construction always removes
rays. -/
theorem hasFiniteCharacter_generalWaveQuotient_basic
    (X : Set V) (U : Set G.DPath) :
    (G.quotient X).HasFiniteCharacter (G.generalWaveQuotient X U) := by
  intro p hp
  unfold generalWaveQuotient admissibleWarpQuotient at hp
  rcases hp with hp | hp
  · obtain ⟨q, hpq⟩ := hp
    rcases q with ⟨q, hq⟩
    obtain ⟨r, _hrU, _hrfinish, hqr⟩ := hq
    subst q
    refine ⟨G.restrictFinitePathToQuotient X
      (G.terminalRoofSuffix X r)
      (G.pathQuotientAdmissible_terminalRoofSuffix X r _hrfinish).1
      (G.pathQuotientAdmissible_terminalRoofSuffix X r _hrfinish).2, ?_⟩
    exact hpq.trans rfl
  · obtain ⟨x, _hx, rfl⟩ := hp
    exact ⟨DirectedPath.FinitePath.trivial (G.quotient X).graph x, rfl⟩

theorem hasFiniteCharacter_waveToLargerQuotient_basic
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    (G.quotient Y).HasFiniteCharacter
      (G.waveToLargerQuotient hNoEnter hXY W).1 := by
  let Z : ((G.quotient X).quotient Y).Wave :=
    ⟨(G.quotient X).generalWaveQuotient Y W.1,
      (G.quotient X).isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have heq : (G.quotient X).quotient Y = G.quotient Y := by
    calc
      (G.quotient X).quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport : G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    simp only [waveToLargerQuotient, Z, heq]
  rw [htransport]
  intro p hp
  exact hasFiniteCharacter_wave_cast
    (H := (G.quotient X).quotient Y) (K := G.quotient Y) heq Z
    ((G.quotient X).hasFiniteCharacter_generalWaveQuotient_basic Y W.1)
    (p := p) hp

/-- Quotient-wave paths over the root-deleted web cannot use the deleted
root when their commitment set is off-root. -/
theorem root_not_mem_vertexSet_sectionSixLift
    (a : V) {X : Set V} (hXa : X ⊆ ({a} : Set V)ᶜ)
    {W : Set (((G.delete {a}).quotient X).DPath)}
    (hW : ((G.delete {a}).quotient X).IsWave W) :
    a ∉ (G.delete {a}).vertexSet
      (SafeLink.liftQuotientFamily (G.delete {a}) X W) := by
  intro haVertex
  obtain ⟨p, ⟨q, hqW, rfl⟩, hap⟩ := haVertex
  have hqSource : q.initial ∈ ((G.delete {a}).quotient X).source :=
    hW.2.1 ⟨q, hqW, rfl⟩
  have hqUnion : q.initial ∈ (G.delete {a}).source ∪ X :=
    ((G.delete {a}).essential_subset _) hqSource
  have hqNotA : q.initial ∉ ({a} : Set V) := by
    rcases hqUnion with hqH | hqX
    · exact hqH.2
    · exact hXa hqX
  have havoid := G.liftDeletePath_avoids ({a} : Set V)
    ((G.delete {a}).liftQuotientPath X q) (by simpa using hqNotA)
  apply Set.disjoint_left.1 havoid
  · simpa using hap
  · exact Set.mem_singleton a

/-! ## The literal maximal-wave recursion -/

/-- The maximal wave selected at commitment set `X`, represented in the
original path type. -/
def sectionSixMaximalWaveLift (X : Set V) : Set G.DPath :=
  SafeLink.maximalQuotientWaveLift G X

theorem isWarp_sectionSixMaximalWaveLift (X : Set V) :
    G.IsWarp (G.sectionSixMaximalWaveLift X) :=
  SafeLink.isWarp_maximalQuotientWaveLift G X

/-- The literal sequence `X_i` in Proposition 6.3, with `W_i` chosen to be
the canonical maximal wave in `G / X_i`.

`F z` is the finite boundary obstruction and `K t` is the countable grounding
set (called `G_t` in the paper). -/
def sectionSixMaximalClosureStage
    (F K : V → Set V) (Y Q T : Set V) (y : V) : ℕ → Set V :=
  G.closureStage
    (G.closingStep G.sectionSixMaximalWaveLift F K Y Q T) (F y)

@[simp]
theorem sectionSixMaximalClosureStage_zero
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    G.sectionSixMaximalClosureStage F K Y Q T y 0 = F y :=
  rfl

@[simp]
theorem sectionSixMaximalClosureStage_succ
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    G.sectionSixMaximalClosureStage F K Y Q T y (n + 1) =
      G.closingStep G.sectionSixMaximalWaveLift F K Y Q T
        (G.sectionSixMaximalClosureStage F K Y Q T y n) :=
  rfl

theorem sectionSixMaximalClosureStage_mono
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    Monotone (G.sectionSixMaximalClosureStage F K Y Q T y) :=
  G.closureStage_monotone G.sectionSixMaximalWaveLift F K Y Q T (F y)

/-- The raw union `X = ⋃ i, X_i` from Proposition 6.3. -/
def sectionSixMaximalClosure
    (F K : V → Set V) (Y Q T : Set V) (y : V) : Set V :=
  commonQuotientSet (G.sectionSixMaximalClosureStage F K Y Q T y)

theorem sectionSixMaximalClosureStage_subset
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    G.sectionSixMaximalClosureStage F K Y Q T y n ⊆
      G.sectionSixMaximalClosure F K Y Q T y :=
  subset_commonQuotientSet _ n

/-- Every `X_i` is countable.  No cardinal assumption on the ambient vertex
type is used. -/
theorem sectionSixMaximalClosureStage_countable
    {F K : V → Set V} {Y Q T : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    ∀ n, (G.sectionSixMaximalClosureStage F K Y Q T y n).Countable := by
  apply G.closureStage_countable
  · exact (hF y).countable
  · intro X _hX
    exact G.isWarp_sectionSixMaximalWaveLift X
  · exact hF
  · exact hK

/-- The raw union `X = ⋃ i, X_i` is countable. -/
theorem sectionSixMaximalClosure_countable
    {F K : V → Set V} {Y Q T : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    (G.sectionSixMaximalClosure F K Y Q T y).Countable := by
  apply Set.countable_iUnion
  exact G.sectionSixMaximalClosureStage_countable hF hK

/-- The bundled maximal quotient wave `W_i`. -/
def sectionSixMaximalWave
    (F K : V → Set V) (Y Q T : Set V) (y : V) (i : ℕ) :
    (G.quotient (G.sectionSixMaximalClosureStage F K Y Q T y i)).Wave :=
  SafeLink.maximalQuotientWave G
    (G.sectionSixMaximalClosureStage F K Y Q T y i)

theorem sectionSixMaximalWave_isMax
    (F K : V → Set V) (Y Q T : Set V) (y : V) (i : ℕ) :
    IsMax (G.sectionSixMaximalWave F K Y Q T y i) :=
  SafeLink.maximalQuotientWave_isMax G
    (G.sectionSixMaximalClosureStage F K Y Q T y i)

/-- `W_i`, transported to the common quotient by the raw union. -/
def sectionSixCommonStage
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (i : ℕ) :
    (G.quotient (G.sectionSixMaximalClosure F K Y Q T y)).Wave :=
  G.commonQuotientStage hNoEnter
    (G.sectionSixMaximalClosureStage F K Y Q T y)
    (G.sectionSixMaximalWave F K Y Q T y) i

/-- The countable up-arrow of all transported `W_i`. -/
def sectionSixCommonWave
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    (G.quotient (G.sectionSixMaximalClosure F K Y Q T y)).Wave :=
  G.commonQuotientOmegaArrow hNoEnter
    (G.sectionSixMaximalClosureStage F K Y Q T y)
    (G.sectionSixMaximalWave F K Y Q T y)

theorem isWave_sectionSixCommonWave
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    (G.quotient (G.sectionSixMaximalClosure F K Y Q T y)).IsWave
      (G.sectionSixCommonWave hNoEnter F K Y Q T y).1 :=
  (G.sectionSixCommonWave hNoEnter F K Y Q T y).2

/-- Every transported stage is roofed by the final countable up-arrow. -/
theorem sectionSixCommonStage_roofLE
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (i : ℕ) :
    (G.quotient (G.sectionSixMaximalClosure F K Y Q T y)).RoofLE
      (G.sectionSixCommonStage hNoEnter F K Y Q T y i).1
      (G.sectionSixCommonWave hNoEnter F K Y Q T y).1 :=
  G.roofLE_commonQuotientOmegaArrow hNoEnter
    (G.sectionSixMaximalClosureStage F K Y Q T y)
    (G.sectionSixMaximalWave F K Y Q T y) i

/-- The final up-arrow introduces no vertex outside the transported stage
waves. -/
theorem sectionSixCommonWave_vertexSet_subset
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    let H := G.quotient (G.sectionSixMaximalClosure F K Y Q T y)
    H.vertexSet (G.sectionSixCommonWave hNoEnter F K Y Q T y).1 ⊆
      ⋃ i, H.vertexSet
        (G.sectionSixCommonStage hNoEnter F K Y Q T y i).1 := by
  exact DWeb.vertexSet_omegaArrow_subset_iUnion
    (G.quotient (G.sectionSixMaximalClosure F K Y Q T y))
    (G.sectionSixCommonStage hNoEnter F K Y Q T y)

/-! ## Dependent accumulated stages

The preceding construction is useful when only the maximal wave at each
commitment set is needed.  Proposition 6.3 uses a little more information:
the wave at the next commitment set must also absorb the wave already built.
The dependent stage below records that invariant in its type.
-/

/-- A commitment set together with a wave in its exact quotient. -/
structure SectionSixAccumStage where
  carrier : Set V
  wave : (G.quotient carrier).Wave

/-- A stage wave represented in the original path type. -/
def sectionSixAccumStageLift (s : G.SectionSixAccumStage) : Set G.DPath :=
  SafeLink.liftQuotientFamily G s.carrier s.wave.1

theorem isWarp_sectionSixAccumStageLift (s : G.SectionSixAccumStage) :
    G.IsWarp (G.sectionSixAccumStageLift s) :=
  SafeLink.isWarp_liftQuotientFamily G s.carrier s.wave.2.1

/-- The next commitment set, closed under the current accumulated wave. -/
def sectionSixAccumNextCarrier
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) : Set V :=
  G.closingStep (fun _ ↦ G.sectionSixAccumStageLift s) F K Y Q T s.carrier

theorem sectionSixAccumStage_carrier_subset_next
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    s.carrier ⊆ G.sectionSixAccumNextCarrier F K Y Q T s :=
  G.subset_closingStep (fun _ ↦ G.sectionSixAccumStageLift s)
    F K Y Q T s.carrier

/-- The dependent successor.  First transport the old accumulator to the
larger quotient, then take its finite-character roof-maximal extension.  This
keeps every accumulated finite thread and prevents a successor choice from
replacing it by a ray. -/
def sectionSixAccumNext
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) : G.SectionSixAccumStage := by
  let X' := G.sectionSixAccumNextCarrier F K Y Q T s
  let old : (G.quotient X').Wave :=
    G.waveToLargerQuotient hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s) s.wave
  let next : (G.quotient X').Wave :=
    (G.quotient X').finiteRoofMaximalExtension old
  exact {
    carrier := X'
    wave := next }

@[simp]
theorem sectionSixAccumNext_carrier
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    (G.sectionSixAccumNext hNoEnter F K Y Q T s).carrier =
      G.sectionSixAccumNextCarrier F K Y Q T s :=
  rfl

/-- The old stage transported to the successor quotient. -/
def sectionSixAccumOldInNext
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).Wave :=
  G.waveToLargerQuotient hNoEnter
    (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s) s.wave

/-- The transported old wave forward-extends to the chosen successor. -/
theorem sectionSixAccumOldInNext_le_next
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    G.sectionSixAccumOldInNext hNoEnter F K Y Q T s ≤
      (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave := by
  exact (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s))
    |>.le_finiteRoofMaximalExtension
      (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s)

/-- The wave chosen at every successor stage roofs every wave in its stage
quotient. -/
theorem sectionSixAccumNext_roofs
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage)
    (W : (G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).Wave) :
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).RoofLE
      W.1 (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 := by
  exact (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s))
    |>.roofLE_finiteRoofMaximalExtension
      (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s) W

theorem sectionSixAccumNext_isRoofMaximal
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).IsRoofMaximal
      (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave := by
  intro W _
  exact G.sectionSixAccumNext_roofs hNoEnter F K Y Q T s W

theorem sectionSixAccumNext_hasFiniteCharacter
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s))
      |>.HasFiniteCharacter
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 := by
  apply (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s))
    |>.finiteRoofMaximalExtension_hasFiniteCharacter
  exact G.hasFiniteCharacter_waveToLargerQuotient_basic hNoEnter
    (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s) s.wave

theorem sectionSixAccumNext_roofs_old
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    let H := G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)
    H.RoofLE
      (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1
      (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 := by
  let H := G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)
  let old := G.sectionSixAccumOldInNext hNoEnter F K Y Q T s
  exact H.roofLE_of_forwardExtension
    (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.2
    (G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s)

/-- The source-faithful dependent recursion `(X_i,A_i)`: `A_i` is the
accumulated wave in `G / X_i`. -/
def sectionSixAccumStage
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    ℕ → G.SectionSixAccumStage
  | 0 => {
      carrier := F y
      wave := (SafeLink.maximalQuotientWave G (F y)).finitePathSubfamily }
  | n + 1 => G.sectionSixAccumNext hNoEnter F K Y Q T
      (sectionSixAccumStage hNoEnter F K Y Q T y n)

@[simp]
theorem sectionSixAccumStage_zero_carrier
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    (sectionSixAccumStage G hNoEnter F K Y Q T y 0).carrier = F y :=
  rfl

@[simp]
theorem sectionSixAccumStage_succ_carrier
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (sectionSixAccumStage G hNoEnter F K Y Q T y (n + 1)).carrier =
      G.sectionSixAccumNextCarrier F K Y Q T
        (sectionSixAccumStage G hNoEnter F K Y Q T y n) :=
  rfl

theorem sectionSixAccumStage_carrier_subset_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier ⊆
      (sectionSixAccumStage G hNoEnter F K Y Q T y (n + 1)).carrier := by
  rw [G.sectionSixAccumStage_succ_carrier]
  exact G.sectionSixAccumStage_carrier_subset_next F K Y Q T _

theorem sectionSixAccumStage_carrier_mono
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    Monotone (fun n ↦
      (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier) := by
  apply monotone_nat_of_le_succ
  exact G.sectionSixAccumStage_carrier_subset_succ
    hNoEnter F K Y Q T y

/-- Every dependent stage contains only finite paths. -/
theorem sectionSixAccumStage_hasFiniteCharacter
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    ∀ n, (G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier)
        |>.HasFiniteCharacter
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1
  | 0 => by
      exact (SafeLink.maximalQuotientWave G (F y))
        |>.finitePathSubfamily_hasFiniteCharacter
  | n + 1 => by
      exact G.sectionSixAccumNext_hasFiniteCharacter hNoEnter F K Y Q T
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n)

/-- Every carrier in the dependent recursion is countable. -/
theorem sectionSixAccumStage_carrier_countable
    (hNoEnter : G.NoEdgeEnters G.source)
    {F K : V → Set V} {Y Q T : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    ∀ n,
      (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier.Countable
  | 0 => (hF y).countable
  | n + 1 => by
      rw [G.sectionSixAccumStage_succ_carrier]
      apply G.closingStep_countable
      · exact G.isWarp_sectionSixAccumStageLift _
      · exact sectionSixAccumStage_carrier_countable
          hNoEnter hF hK n
      · exact hF
      · exact hK

/-- If all inserted obstruction and grounding sets lie off the root in the
tree, then every dependent commitment stage does as well.  The only subtle
case is the tree-intersection term: its paths live over `G.delete {a}`, so
the distinguished root cannot occur on them. -/
theorem sectionSixAccumStage_carrier_subset_offRoot
    (a : V) (hNoEnter : (G.delete {a}).NoEdgeEnters (G.delete {a}).source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (hF : ∀ z, F z ⊆ T \ {a}) (hK : ∀ t, K t ⊆ T \ {a}) :
    ∀ n, (sectionSixAccumStage (G.delete {a}) hNoEnter
      F K Y Q T y n).carrier ⊆ T \ {a}
  | 0 => by simpa using hF y
  | n + 1 => by
      rw [(G.delete {a}).sectionSixAccumStage_succ_carrier]
      intro x hx
      change x ∈ (G.delete {a}).closingStep
        (fun _ ↦ (G.delete {a}).sectionSixAccumStageLift
          (sectionSixAccumStage (G.delete {a}) hNoEnter F K Y Q T y n))
        F K Y Q T
        (sectionSixAccumStage (G.delete {a}) hNoEnter F K Y Q T y n).carrier at hx
      simp only [closingStep, Set.mem_union] at hx
      rcases hx with ((hxOld | hxF) | hxK) | hxMeet
      · exact sectionSixAccumStage_carrier_subset_offRoot
          a hNoEnter F K Y Q T y hF hK n hxOld
      · simp only [Set.mem_iUnion] at hxF
        obtain ⟨z, _hz, hxFz⟩ := hxF
        exact hF z hxFz
      · simp only [Set.mem_iUnion] at hxK
        obtain ⟨t, _ht, hxKt⟩ := hxK
        exact hK t hxKt
      · refine ⟨hxMeet.2, ?_⟩
        intro hxa
        subst x
        have haVertex : a ∈ (G.delete {a}).vertexSet
            ((G.delete {a}).sectionSixAccumStageLift
              (sectionSixAccumStage (G.delete {a}) hNoEnter
                F K Y Q T y n)) := by
          rw [meetingVertexSet] at hxMeet
          obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hxMeet.1
          obtain ⟨hpMeeting, hap⟩ := Set.mem_iUnion.mp hp
          exact ⟨p, hpMeeting.1, hap⟩
        exact G.root_not_mem_vertexSet_sectionSixLift a
          (sectionSixAccumStage_carrier_subset_offRoot
            a hNoEnter F K Y Q T y hF hK n |>.trans
              (by intro v hv; simpa using hv.2))
          (sectionSixAccumStage (G.delete {a}) hNoEnter
            F K Y Q T y n).wave.2 haVertex

/-- The raw union of the dependent commitment sets. -/
def sectionSixAccumClosure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) : Set V :=
  ⋃ n, (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier

theorem sectionSixAccumStage_carrier_subset_closure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier ⊆
      sectionSixAccumClosure G hNoEnter F K Y Q T y := by
  change (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier ⊆
    ⋃ i, (sectionSixAccumStage G hNoEnter F K Y Q T y i).carrier
  exact Set.subset_iUnion
    (fun i : ℕ ↦ (sectionSixAccumStage G hNoEnter F K Y Q T y i).carrier) n

theorem sectionSixAccumClosure_countable
    (hNoEnter : G.NoEdgeEnters G.source)
    {F K : V → Set V} {Y Q T : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    (sectionSixAccumClosure G hNoEnter F K Y Q T y).Countable := by
  apply Set.countable_iUnion
  exact sectionSixAccumStage_carrier_countable G hNoEnter hF hK

/-- Each finite boundary obstruction encountered by the accumulated stage
wave is inserted into the next carrier. -/
theorem sectionSixAccum_F_subset_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {z : V}
    (hz : z ∈ Y ∩ G.meetingVertexSet
      (G.sectionSixAccumStageLift
        (sectionSixAccumStage G hNoEnter F K Y Q T y n))
      (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier) :
    F z ⊆
      (sectionSixAccumStage G hNoEnter F K Y Q T y (n + 1)).carrier := by
  intro x hx
  rw [G.sectionSixAccumStage_succ_carrier]
  exact Or.inl (Or.inl (Or.inr
    (Set.mem_iUnion_of_mem z (Set.mem_iUnion_of_mem hz hx))))

theorem sectionSixAccum_F_subset_closure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {z : V}
    (hz : z ∈ Y ∩ G.meetingVertexSet
      (G.sectionSixAccumStageLift
        (sectionSixAccumStage G hNoEnter F K Y Q T y n))
      (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier) :
    F z ⊆ G.sectionSixAccumClosure hNoEnter F K Y Q T y :=
  (G.sectionSixAccum_F_subset_succ hNoEnter F K Y Q T y n hz).trans
    (G.sectionSixAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y (n + 1))

/-- Every grounding set indexed at stage `n` is inserted at stage `n+1`. -/
theorem sectionSixAccum_K_subset_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {t : V}
    (ht : t ∈
      (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier \ Q) :
    K t ⊆
      (sectionSixAccumStage G hNoEnter F K Y Q T y (n + 1)).carrier := by
  intro x hx
  rw [G.sectionSixAccumStage_succ_carrier]
  exact Or.inl (Or.inr
    (Set.mem_iUnion_of_mem t (Set.mem_iUnion_of_mem ht hx)))

theorem sectionSixAccum_K_subset_closure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {t : V}
    (ht : t ∈
      (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier \ Q) :
    K t ⊆ G.sectionSixAccumClosure hNoEnter F K Y Q T y :=
  (G.sectionSixAccum_K_subset_succ hNoEnter F K Y Q T y n ht).trans
    (G.sectionSixAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y (n + 1))

/-- Every tree vertex on a current accumulated-wave path meeting `X_n` is
inserted into `X_{n+1}`. -/
theorem sectionSixAccum_meetingTree_subset_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    G.meetingVertexSet
        (G.sectionSixAccumStageLift
          (sectionSixAccumStage G hNoEnter F K Y Q T y n))
        (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier ∩ T ⊆
      (sectionSixAccumStage G hNoEnter F K Y Q T y (n + 1)).carrier := by
  intro x hx
  rw [G.sectionSixAccumStage_succ_carrier]
  exact Or.inr hx

theorem sectionSixAccum_meetingTree_subset_closure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    G.meetingVertexSet
        (G.sectionSixAccumStageLift
          (sectionSixAccumStage G hNoEnter F K Y Q T y n))
        (sectionSixAccumStage G hNoEnter F K Y Q T y n).carrier ∩ T ⊆
      G.sectionSixAccumClosure hNoEnter F K Y Q T y :=
  (G.sectionSixAccum_meetingTree_subset_succ
    hNoEnter F K Y Q T y n).trans
      (G.sectionSixAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y (n + 1))

/-- A dependent stage transported to the quotient by the raw union. -/
def sectionSixAccumCommonStage
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).Wave :=
  G.waveToLargerQuotient hNoEnter
    (G.sectionSixAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y n)
    (sectionSixAccumStage G hNoEnter F K Y Q T y n).wave

/-- The final common-quotient up-arrow of the dependent accumulated stages. -/
def sectionSixAccumCommonWave
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).Wave :=
  (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrow
    (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y)

theorem isWave_sectionSixAccumCommonWave
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).IsWave
      (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1 :=
  (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).2

theorem sectionSixAccumCommonStage_roofLE
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    let H := G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)
    H.RoofLE
      (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y n).1
      (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1 := by
  exact DWeb.roofLE_omegaArrow
    (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y))
    (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n

theorem sectionSixAccumCommonWave_vertexSet_subset
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    let H := G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)
    H.vertexSet (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1 ⊆
      ⋃ n, H.vertexSet
        (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y n).1 := by
  exact DWeb.vertexSet_omegaArrow_subset_iUnion
    (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y))
    (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y)

/-! ## Closing up along the finite accumulated arrows -/

/-- The concrete finite closure sequence after all stage waves live in one
fixed web.  At stage `n` the recurrence uses the actual finite accumulated
arrow `W_0 ↑ ⋯ ↑ W_n`. -/
def omegaArrowClosureStage
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) : ℕ → Set V :=
  SafeLink.sectionSixClosureStage F K Y T Q
    (fun n ↦ (G.omegaArrowStage W n).1) y

/-- The union of the finite closing-up stages in the common web. -/
def omegaArrowClosure
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) : Set V :=
  ⋃ n, G.omegaArrowClosureStage W F K Y T Q y n

@[simp]
theorem omegaArrowClosureStage_zero
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) :
    G.omegaArrowClosureStage W F K Y T Q y 0 = F y :=
  rfl

@[simp]
theorem omegaArrowClosureStage_succ
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) (n : ℕ) :
    G.omegaArrowClosureStage W F K Y T Q y (n + 1) =
      let X := G.omegaArrowClosureStage W F K Y T Q y n
      X ∪
        (⋃ z ∈ Y ∩ SafeLink.verticesMeeting
          (G.omegaArrowStage W n).1 X, F z) ∪
        (⋃ t ∈ X \ Q, K t) ∪
        (SafeLink.verticesMeeting (G.omegaArrowStage W n).1 X ∩ T) :=
  rfl

theorem omegaArrowClosureStage_mono
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) :
    Monotone (G.omegaArrowClosureStage W F K Y T Q y) :=
  SafeLink.sectionSixClosureStage_mono F K Y T Q
    (fun n ↦ (G.omegaArrowStage W n).1) y

theorem omegaArrowClosureStage_countable
    (W : ℕ → G.Wave) {F K : V → Set V}
    {Y T Q : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    ∀ n, (G.omegaArrowClosureStage W F K Y T Q y n).Countable := by
  exact SafeLink.sectionSixClosureStage_countable hF hK
    (fun n ↦ (G.omegaArrowStage W n).2.1)

theorem omegaArrowClosure_countable
    (W : ℕ → G.Wave) {F K : V → Set V}
    {Y T Q : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    (G.omegaArrowClosure W F K Y T Q y).Countable := by
  apply Set.countable_iUnion
  exact G.omegaArrowClosureStage_countable W hF hK

theorem safeLink_verticesMeeting_eq_verticesMeetingSet
    (U : Set G.DPath) (X : Set V) :
    SafeLink.verticesMeeting U X = G.verticesMeetingSet U X := by
  ext x
  simp only [SafeLink.verticesMeeting, SafeLink.pathsMeeting,
    verticesMeetingSet, pathsMeetingSet, vertexSet, Set.mem_iUnion,
    Set.mem_setOf_eq]
  aesop

/-- Every finite accumulated arrow is below the final countable arrow in
roof order. -/
theorem roofLE_omegaArrowStage (W : ℕ → G.Wave) (n : ℕ) :
    G.RoofLE (G.omegaArrowStage W n).1 (G.omegaArrow W).1 := by
  apply G.roofLE_of_forwardExtension (G.omegaArrow W).2
  exact G.le_waveChainUpperWave (Set.range (G.omegaArrowStage W))
    (G.omegaArrowStage_range_nonempty W)
    (G.omegaArrowStage_range_isChain W) (Set.mem_range_self n)

/-- A tree-restricted version of the closing-up transfer in
`CommonQuotient`. -/
theorem verticesMeetingSet_omegaArrow_inter_subset_iUnion_of_step
    (W : ℕ → G.Wave) (X : ℕ → Set V) (hX : Monotone X)
    (T : Set V)
    (hstep : ∀ n,
      G.verticesMeetingSet (G.omegaArrowStage W n).1 (X n) ∩ T ⊆
        X (n + 1)) :
    G.verticesMeetingSet (G.omegaArrow W).1 (⋃ n, X n) ∩ T ⊆
      ⋃ n, X n := by
  rintro z ⟨⟨q, ⟨hqW, hqX⟩, hzq⟩, hzT⟩
  obtain ⟨x, hxq, hxUnion⟩ := hqX
  obtain ⟨k, hxXk⟩ := Set.mem_iUnion.mp hxUnion
  obtain ⟨m, hkm, p, hpStage, hxp, hzp⟩ :=
    G.exists_later_omegaArrowStage_path_containing_pair W k hqW hxq hzq
  have hxXm : x ∈ X m := hX hkm hxXk
  have hzStage : z ∈
      G.verticesMeetingSet (G.omegaArrowStage W m).1 (X m) :=
    ⟨p, ⟨hpStage, ⟨x, hxp, hxXm⟩⟩, hzp⟩
  exact Set.mem_iUnion_of_mem (m + 1) (hstep m ⟨hzStage, hzT⟩)

/-- Clause (a): a point roofed by the first wave remains roofed by the
countable up-arrow. -/
theorem omegaArrow_roofs_seed
    (W : ℕ → G.Wave) {y : V}
    (hy : y ∈ G.roof (G.terminalFrontier (W 0).1)) :
    y ∈ G.roof (G.terminalFrontier (G.omegaArrow W).1) :=
  G.roofLE_omegaArrow W 0 hy

/-- Clause (b) for the concrete accumulated-arrow closure. -/
theorem omegaArrowClosure_F
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) {z : V}
    (hz : z ∈ Y ∩ G.verticesMeetingSet (G.omegaArrow W).1
      (G.omegaArrowClosure W F K Y T Q y)) :
    F z ⊆ G.omegaArrowClosure W F K Y T Q y := by
  let X := G.omegaArrowClosureStage W F K Y T Q y
  have hmono : Monotone X :=
    G.omegaArrowClosureStage_mono W F K Y T Q y
  apply G.boundary_subset_iUnion_of_omegaArrow_step W X hmono Y F
  · intro n z hzStage
    intro x hxF
    change x ∈ G.omegaArrowClosureStage W F K Y T Q y (n + 1)
    rw [G.omegaArrowClosureStage_succ]
    exact Or.inl (Or.inl (Or.inr
      (Set.mem_iUnion_of_mem z (Set.mem_iUnion_of_mem
        (by simpa [G.safeLink_verticesMeeting_eq_verticesMeetingSet] using hzStage)
        hxF))))
  · simpa only [omegaArrowClosure] using hz

/-- The set-inclusion half of clause (c): every grounding set indexed by a
point of `X \ Q` is contained in `X`. -/
theorem omegaArrowClosure_K
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) {t : V}
    (ht : t ∈ G.omegaArrowClosure W F K Y T Q y \ Q) :
    K t ⊆ G.omegaArrowClosure W F K Y T Q y := by
  obtain ⟨n, htStage⟩ := Set.mem_iUnion.mp ht.1
  intro x hxK
  apply Set.mem_iUnion_of_mem (n + 1)
  rw [G.omegaArrowClosureStage_succ]
  exact Or.inl (Or.inr
    (Set.mem_iUnion_of_mem t
      (Set.mem_iUnion_of_mem ⟨htStage, ht.2⟩ hxK)))

/-- Clause (d): the tree vertices on final up-arrow paths meeting the raw
union already belong to that union. -/
theorem omegaArrowClosure_meetingTree
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V) :
    G.verticesMeetingSet (G.omegaArrow W).1
        (G.omegaArrowClosure W F K Y T Q y) ∩ T ⊆
      G.omegaArrowClosure W F K Y T Q y := by
  let X := G.omegaArrowClosureStage W F K Y T Q y
  apply G.verticesMeetingSet_omegaArrow_inter_subset_iUnion_of_step
    W X (G.omegaArrowClosureStage_mono W F K Y T Q y) T
  intro n z hz
  change z ∈ G.omegaArrowClosureStage W F K Y T Q y (n + 1)
  rw [G.omegaArrowClosureStage_succ]
  exact Or.inr ⟨by
    simpa [G.safeLink_verticesMeeting_eq_verticesMeetingSet] using hz.1, hz.2⟩

/-- Roof inclusion plus exclusion from the new essential frontier promotes
strict-roof membership.  This is the exact local implication needed for the
strict-roof half of clause (c). -/
theorem mem_strictRoof_of_roofLE_of_not_mem_essential
    {U Z : Set G.DPath} {t : V}
    (hUZ : G.RoofLE U Z)
    (ht : t ∈ G.strictRoof (G.terminalFrontier U))
    (htEss : t ∉ G.essential (G.terminalFrontier Z)) :
    t ∈ G.strictRoof (G.terminalFrontier Z) :=
  ⟨hUZ ht.1, htEss⟩

/-- The strict-roof half of clause (c), isolated from the set-theoretic
closure.  The two premises are precisely the grounding-wave invariant and
the essential-frontier exclusion supplied by the arrow construction. -/
theorem omegaArrowClosure_strictRoof
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V)
    (hground : ∀ n {t : V},
      t ∈ G.omegaArrowClosureStage W F K Y T Q y n \ Q →
        t ∈ G.strictRoof
          (G.terminalFrontier (G.omegaArrowStage W n).1))
    (havoid : ∀ n, Disjoint
      (G.essential (G.terminalFrontier (G.omegaArrow W).1))
      (G.strictRoof
        (G.terminalFrontier (G.omegaArrowStage W n).1))) :
    G.omegaArrowClosure W F K Y T Q y \ Q ⊆
      G.strictRoof (G.terminalFrontier (G.omegaArrow W).1) := by
  intro t ht
  obtain ⟨n, htStage⟩ := Set.mem_iUnion.mp ht.1
  apply G.mem_strictRoof_of_roofLE_of_not_mem_essential
    (G.roofLE_omegaArrowStage W n)
    (hground n ⟨htStage, ht.2⟩)
  intro htEss
  exact Set.disjoint_left.1 (havoid n) htEss
    (hground n ⟨htStage, ht.2⟩)

/-- The four closure conclusions in one theorem.  Unlike a record-valued
assumption, all set-theoretic parts are proved from the concrete recurrence;
only the graph-specific seed and strict-frontier inputs remain explicit. -/
theorem omegaArrowClosure_invariants
    (W : ℕ → G.Wave) (F K : V → Set V)
    (Y T Q : Set V) (y : V)
    (hy : y ∈ G.roof (G.terminalFrontier (W 0).1))
    (hground : ∀ n {t : V},
      t ∈ G.omegaArrowClosureStage W F K Y T Q y n \ Q →
        t ∈ G.strictRoof
          (G.terminalFrontier (G.omegaArrowStage W n).1))
    (havoid : ∀ n, Disjoint
      (G.essential (G.terminalFrontier (G.omegaArrow W).1))
      (G.strictRoof
        (G.terminalFrontier (G.omegaArrowStage W n).1))) :
    y ∈ G.roof (G.terminalFrontier (G.omegaArrow W).1) ∧
      (∀ z ∈ Y ∩ G.verticesMeetingSet (G.omegaArrow W).1
          (G.omegaArrowClosure W F K Y T Q y),
        F z ⊆ G.omegaArrowClosure W F K Y T Q y) ∧
      (∀ t ∈ G.omegaArrowClosure W F K Y T Q y \ Q,
        K t ⊆ G.omegaArrowClosure W F K Y T Q y ∧
        t ∈ G.strictRoof (G.terminalFrontier (G.omegaArrow W).1)) ∧
      G.verticesMeetingSet (G.omegaArrow W).1
          (G.omegaArrowClosure W F K Y T Q y) ∩ T ⊆
        G.omegaArrowClosure W F K Y T Q y := by
  refine ⟨G.omegaArrow_roofs_seed W hy, ?_, ?_,
    G.omegaArrowClosure_meetingTree W F K Y T Q y⟩
  · intro z hz
    exact G.omegaArrowClosure_F W F K Y T Q y hz
  · intro t ht
    exact ⟨G.omegaArrowClosure_K W F K Y T Q y ht,
      G.omegaArrowClosure_strictRoof W F K Y T Q y hground havoid ht⟩

end DWeb

end Erdos599
