/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Wave
import ErdosProblems.Erdos599.Bridge
import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.WaveLimits

/-!
# The Aharoni--Berger assembly for Erdős Problem 599

This file formalizes the reductions in Section 5 of Aharoni and Berger's
proof of the infinite Menger theorem.  It deliberately does not postulate the
deep theorem that every unhindered web is linkable.  Instead, the two
directions expose the graph-theoretic obligations which the concrete path,
quotient, and splicing modules must discharge.

The forward reduction says that an orthogonal packing--separator pair in an
unhindered web is a linkage: truncate the packing at the separator to obtain a
wave, and unhinderedness forces that wave to start at every source.

For the reverse reduction we first choose a forward-extension-maximal wave by
Zorn, trim it to the essential part of its terminal frontier, and call that
frontier `maximalSeparator`.  The normalized quotient by this frontier is
loose and therefore unhindered.  A linkage in the quotient can then be
spliced onto the trimmed wave.  `MaximalWaveQuotientAssembly` records exactly
the concrete obligations of that last operation: the quotient is loose and
splicing a quotient linkage gives a target packing meeting the old frontier
exactly once.

All hypotheses in the final assembly theorems are local theorem parameters.
There is no global declaration standing for the Aharoni--Berger core.
-/

namespace Erdos599
namespace AharoniBerger

open Set
open WaveCore

universe u v w

variable {V : Type u} {Path : Type v}

/-! ## Directed packing and orthogonality -/

/-- A pairwise disjoint family of finite directed paths from `A` to `B`.

Unlike a linkage, a packing need not start at every point of `A`.  The target
condition in particular excludes rays, since every member has a terminal
vertex in `B`. -/
structure DirectedPacking (D : RoofedPathSystem V Path)
    (A B : Set V) (P : Set Path) : Prop where
  isWarp : D.toDirectedPathSystem.IsWarp P
  starts_in_source : D.toDirectedPathSystem.initialSet P ⊆ A
  ends_in_target : ∀ {p}, p ∈ P →
    ∃ b ∈ B, D.terminal p = some b

/-- A directed linkage is a target packing which starts at every source. -/
structure DirectedLinkage (D : RoofedPathSystem V Path)
    (A B : Set V) (P : Set Path) : Prop extends
    DirectedPacking D A B P where
  covers_source : D.toDirectedPathSystem.initialSet P = A

/-- The web represented by `D`, with source `A` and target `B`, is linkable. -/
def DirectedLinkable (D : RoofedPathSystem V Path) (A B : Set V) : Prop :=
  ∃ P : Set Path, DirectedLinkage D A B P

/-- `S` consists of exactly one vertex from each member of `P`.

The subset clause rules out extraneous vertices of `S`, including the
otherwise-vacuous empty-packing/oversized-separator formulation. -/
structure OrthogonalAt (D : RoofedPathSystem V Path)
    (P : Set Path) (S : Set V) : Prop where
  subset_vertexSet : S ⊆ D.toDirectedPathSystem.vertexSet P
  unique_on_path : ∀ p ∈ P,
    ∃! s : V, s ∈ S ∧ s ∈ D.support p

/-- A directed Aharoni--Berger witness: a target packing together with an
`A`--target separator orthogonal to it. -/
structure MengerPair (D : RoofedPathSystem V Path)
    (A B : Set V) (P : Set Path) (S : Set V) : Prop where
  packing : DirectedPacking D A B P
  separates : D.Separates A S
  orthogonal : OrthogonalAt D P S

/-- The directed infinite Menger conclusion for one source and target pair. -/
def DirectedMenger (D : RoofedPathSystem V Path) (A B : Set V) : Prop :=
  ∃ (P : Set Path) (S : Set V), MengerPair D A B P S

namespace DirectedPacking

variable {D : RoofedPathSystem V Path} {A B : Set V} {P : Set Path}

theorem member_isFinite (hP : DirectedPacking D A B P)
    {p : Path} (hp : p ∈ P) : D.toDirectedPathSystem.IsFinite p := by
  obtain ⟨b, _hbB, hpb⟩ := hP.ends_in_target hp
  exact ⟨b, hpb⟩

end DirectedPacking

namespace DirectedLinkage

variable {D : RoofedPathSystem V Path} {A B : Set V} {P : Set Path}

theorem starts_exactly (hP : DirectedLinkage D A B P) :
    D.toDirectedPathSystem.initialSet P = A :=
  hP.covers_source

theorem toPacking (hP : DirectedLinkage D A B P) :
    DirectedPacking D A B P :=
  hP.toDirectedPacking

end DirectedLinkage

/-! ## The easy Section 5 reduction -/

/-- The properties of the path family obtained by truncating an orthogonal
packing at its selected separator vertices.

The first field is the substantive path-truncation lemma: the truncated
family is a wave.  The other fields retain the source threads and record the
literal truncation and terminal-frontier facts needed by later concrete
adapters. -/
structure IsSeparatorTruncation (D : RoofedPathSystem V Path)
    (A : Set V) (P : Set Path) (S : Set V) (W : Set Path) : Prop where
  isWave : D.IsWave A W
  initialSet_eq : D.toDirectedPathSystem.initialSet W =
    D.toDirectedPathSystem.initialSet P
  terminalSet_eq : D.toDirectedPathSystem.terminalSet W = S
  vertexSet_subset : D.toDirectedPathSystem.vertexSet W ⊆
    D.toDirectedPathSystem.vertexSet P

/-- A loose web is unhindered.  This is the elementary implication used
after passing to the quotient by a maximal wave. -/
theorem isUnhindered_of_isLoose (D : RoofedPathSystem V Path) (A : Set V)
    (hloose : D.IsLoose A) : D.IsUnhindered A := by
  rw [D.isUnhindered_iff A]
  intro W hW
  rw [hloose W hW, D.toDirectedPathSystem.initialSet_trivialWarp]

/-- Section 5, forward direction: an orthogonal packing--separator theorem
implies linkability of every unhindered web, once the elementary truncation
operation has been supplied.

No property of `B` is used beyond the fact that the original packing ends
there.  Unhinderedness forces the truncated wave, hence the original
packing, to contain a path starting at every source. -/
theorem linkage_of_mengerPair_of_unhindered
    (D : RoofedPathSystem V Path) (A B : Set V)
    (hunhindered : D.IsUnhindered A)
    {P : Set Path} {S : Set V} (hpair : MengerPair D A B P S)
    (htruncate : ∃ W : Set Path, IsSeparatorTruncation D A P S W) :
    DirectedLinkage D A B P := by
  obtain ⟨W, hW⟩ := htruncate
  have hstartsW : D.toDirectedPathSystem.initialSet W = A :=
    (D.isUnhindered_iff A).mp hunhindered W hW.isWave
  refine
    { toDirectedPacking := hpair.packing
      covers_source := ?_ }
  rw [← hW.initialSet_eq]
  exact hstartsW

/-- Pointwise formulation of the easy reduction. -/
theorem directedLinkable_of_directedMenger_of_unhindered
    (D : RoofedPathSystem V Path) (A B : Set V)
    (hmenger : DirectedMenger D A B)
    (htruncate : ∀ {P : Set Path} {S : Set V},
      MengerPair D A B P S →
        ∃ W : Set Path, IsSeparatorTruncation D A P S W)
    (hunhindered : D.IsUnhindered A) :
    DirectedLinkable D A B := by
  obtain ⟨P, S, hpair⟩ := hmenger
  exact ⟨P, linkage_of_mengerPair_of_unhindered D A B hunhindered hpair
    (htruncate hpair)⟩

/-! ## The maximal-wave separator -/

variable (D : RoofedPathSystem V Path)

/-- The separator retained from a maximal wave is the essential part of its
terminal frontier.  The definition makes sense for every wave; maximality is
used only to prove that the associated quotient is loose. -/
def maximalSeparator {A : Set V} (M : D.AbstractWave A) : Set V :=
  D.Essential (D.toDirectedPathSystem.terminalSet M.1)

@[simp]
theorem terminalSet_essentialTrim_eq_maximalSeparator {A : Set V}
    (M : D.AbstractWave A) :
    D.toDirectedPathSystem.terminalSet (D.essentialTrim M.1) =
      maximalSeparator D M := by
  exact D.terminalSet_essentialTrim M.1

/-- Essential trimming of the chosen wave is still a wave. -/
theorem essentialTrim_isWave_of_abstractWave {A : Set V}
    (M : D.AbstractWave A) :
    D.IsWave A (D.essentialTrim M.1) :=
  D.isWave_essentialTrim M.2

/-- The essential terminal frontier remains a separator. -/
theorem maximalSeparator_separates {A : Set V}
    (M : D.AbstractWave A) :
    D.Separates A (maximalSeparator D M) := by
  exact D.separates_essential M.2.2.2

/-! ## Loose quotient and splice contract -/

/-- The concrete data needed after choosing a maximal wave.

Here `Q` is the roofed path system of the normalized quotient by
`maximalSeparator D M`.  A concrete quotient module proves
`quotient_isLoose` from forward-extension maximality.  Its path-splicing
lemma then proves the last two fields.  Keeping those obligations separate
lets the Section 5 assembly prove separation itself, rather than hiding the
desired theorem in the contract. -/
structure MaximalWaveQuotientAssembly
    {QPath : Type w} (Q : RoofedPathSystem V QPath)
    (A B : Set V) (M : D.AbstractWave A) : Type (max v w) where
  quotient_isLoose : Q.IsLoose (maximalSeparator D M)
  splice : Set QPath → Set Path
  splice_isPacking : ∀ {L : Set QPath},
    DirectedLinkage Q (maximalSeparator D M) B L →
      DirectedPacking D A B (splice L)
  splice_isOrthogonal : ∀ {L : Set QPath},
    DirectedLinkage Q (maximalSeparator D M) B L →
      OrthogonalAt D (splice L) (maximalSeparator D M)

namespace MaximalWaveQuotientAssembly

variable {D : RoofedPathSystem V Path}
variable {QPath : Type w} {Q : RoofedPathSystem V QPath}
variable {A B : Set V} {M : D.AbstractWave A}

/-- A linkage in the loose quotient splices to an orthogonal
packing--separator pair in the original web. -/
theorem mengerPair_of_linkage
    (H : MaximalWaveQuotientAssembly D Q A B M)
    {L : Set QPath}
    (hL : DirectedLinkage Q (maximalSeparator D M) B L) :
    MengerPair D A B (H.splice L) (maximalSeparator D M) := by
  exact
    { packing := H.splice_isPacking hL
      separates := maximalSeparator_separates D M
      orthogonal := H.splice_isOrthogonal hL }

end MaximalWaveQuotientAssembly

/-! ## The reverse Section 5 assembly -/

/-- The exact chain-upper-bound premise used to obtain a maximal wave by
Zorn.  In the concrete development it is discharged by the iterated-arrow
limit theorem. -/
abbrev WaveChainUpperBounds (D : RoofedPathSystem V Path) (A : Set V) : Prop :=
  ∀ c : Set (D.AbstractWave A),
    IsChain (· ≤ ·) c → c.Nonempty →
      ∃ ub : D.AbstractWave A, ∀ W ∈ c, W ≤ ub

/-- Section 5, reverse direction, for one web.

The proof follows the source assembly exactly:

1. extend the trivial wave to a forward-extension-maximal wave `M`;
2. retain the essential terminal frontier `maximalSeparator D M`;
3. use looseness to see that the quotient is unhindered;
4. apply the locally supplied unhindered-web theorem in the quotient;
5. splice that quotient linkage to the essential trim of `M`.

The deep theorem is the explicit parameter `hunhindered_linkable`; this file
does not install it as a global assumption. -/
theorem directedMenger_of_unhinderedLinkability
    (D : RoofedPathSystem V Path) (A B : Set V)
    (hchain : WaveChainUpperBounds D A)
    (hquotient : ∀ (M : D.AbstractWave A), IsMax M →
      ∃ (QPath : Type w) (Q : RoofedPathSystem V QPath),
        Nonempty (MaximalWaveQuotientAssembly D Q A B M))
    (hunhindered_linkable :
      ∀ (QPath : Type w) (Q : RoofedPathSystem V QPath) (X : Set V),
        Q.IsUnhindered X → DirectedLinkable Q X B) :
    DirectedMenger D A B := by
  let W₀ : D.AbstractWave A :=
    ⟨D.toDirectedPathSystem.trivialWarp A, D.isWave_trivialWarp A⟩
  obtain ⟨M, _hW₀M, hMmax⟩ :=
    D.exists_maximal_forward_extension A W₀ hchain
  obtain ⟨QPath, Q, hassembly⟩ := hquotient M hMmax
  let H : MaximalWaveQuotientAssembly D Q A B M := hassembly.some
  have hquotient_unhindered :
      Q.IsUnhindered (maximalSeparator D M) :=
    isUnhindered_of_isLoose Q (maximalSeparator D M) H.quotient_isLoose
  obtain ⟨L, hL⟩ :=
    hunhindered_linkable QPath Q (maximalSeparator D M)
      hquotient_unhindered
  exact ⟨H.splice L, maximalSeparator D M, H.mengerPair_of_linkage hL⟩

/-- The directed infinite Menger assertion, universally quantified over the
path presentation and the source and target sets on one vertex type. -/
def DirectedMengerPrinciple (V : Type u) : Prop :=
  ∀ (Path : Type v) (D : RoofedPathSystem V Path) (A B : Set V),
    DirectedMenger D A B

/-- The unhindered-web theorem, universally quantified over the same class
of path presentations and webs. -/
def UnhinderedLinkabilityPrinciple (V : Type u) : Prop :=
  ∀ (Path : Type v) (D : RoofedPathSystem V Path) (A B : Set V),
    D.IsUnhindered A → DirectedLinkable D A B

/-- The genuine Section 5 equivalence is an equivalence of universal
theorems over all webs.  This matters in the reverse direction: the
unhindered-web theorem is applied not to the original web but to the loose
quotient produced from a maximal wave.

The remaining parameters are precisely the elementary concrete facts used
by that reduction: separator truncation, upper bounds for chains of waves,
and the loose-quotient/splice construction. -/
theorem sectionFive_equivalence
    (htruncate :
      ∀ (Path : Type v) (D : RoofedPathSystem V Path) (A B : Set V)
        {P : Set Path} {S : Set V},
        MengerPair D A B P S →
          ∃ W : Set Path, IsSeparatorTruncation D A P S W)
    (hchain :
      ∀ (Path : Type v) (D : RoofedPathSystem V Path) (A : Set V),
        WaveChainUpperBounds D A)
    (hquotient :
      ∀ (Path : Type v) (D : RoofedPathSystem V Path) (A B : Set V)
        (M : D.AbstractWave A), IsMax M →
          ∃ (QPath : Type v) (Q : RoofedPathSystem V QPath),
            Nonempty (MaximalWaveQuotientAssembly D Q A B M)) :
    DirectedMengerPrinciple.{u, v} V ↔
      UnhinderedLinkabilityPrinciple.{u, v} V := by
  constructor
  · intro hmenger Path D A B hunhindered
    exact directedLinkable_of_directedMenger_of_unhindered
      D A B (hmenger Path D A B) (htruncate Path D A B) hunhindered
  · intro hunhindered_linkable Path D A B
    exact directedMenger_of_unhinderedLinkability
      D A B (hchain Path D A) (hquotient Path D A B)
        (fun QPath Q X hX ↦
          hunhindered_linkable QPath Q X B hX)

/-! ## Concrete-web Section 5 adapters

The preceding statements retain the relation-generic `RoofedPathSystem`
interface used while the concrete path library was being developed.  The
rest of this file specializes the reverse implication to the canonical
`DWeb` model.  In particular, maximal waves are now obtained from the
proved direct-limit theorem `DWeb.exists_maximal_wave`; no chain-upper-bound
hypothesis remains.

The quotient is literally `DWeb.quotient`, linkages use the canonical
endpoint-pure cardinal-induction predicate, and the splice below constructs
a family of bundled `Bridge.DirectedABPath`s. -/

variable {V : Type u}

/-- Local short name for the canonical, endpoint-pure linkage predicate
used by the cardinal-induction development. -/
abbrev ConcreteIsLinkageBetween (G : DWeb V) (A C : Set V)
    (W : Set G.DPath) : Prop :=
  CardinalInduction.IsLinkageBetween G A C W

/-- Local short name for canonical concrete linkability. -/
abbrev ConcreteIsLinkable (G : DWeb V) : Prop :=
  CardinalInduction.IsLinkable G

/-- The essential terminal frontier of a concrete maximal wave. -/
def concreteMaximalSeparator (G : DWeb V) (M : G.Wave) : Set V :=
  G.terminalFrontier (G.essentialWarpPart M.1)

theorem concreteMaximalSeparator_eq_essential (G : DWeb V) (M : G.Wave) :
    concreteMaximalSeparator G M =
      G.essential (G.terminalFrontier M.1) := by
  exact G.terminalFrontier_essentialWarpPart M.1

/-- Essential trimming preserves the concrete wave. -/
theorem essentialWarpPart_isWave (G : DWeb V) (M : G.Wave) :
    G.IsWave (G.essentialWarpPart M.1) :=
  M.property.essentialWarpPart

/-- The essential frontier retained from a concrete wave still separates
the source from the target, expressed in the concrete roof calculus. -/
theorem source_subset_roof_concreteMaximalSeparator
    (G : DWeb V) (M : G.Wave) :
    G.source ⊆ G.roof (concreteMaximalSeparator G M) := by
  rw [concreteMaximalSeparator_eq_essential, G.roof_essential]
  exact M.property.2.2

/-- Observation 3.24 in the normalized concrete form: the quotient source
is exactly the essential frontier retained from the maximal wave. -/
theorem quotient_concreteMaximalSeparator_source
    (G : DWeb V) (M : G.Wave) :
    (G.quotient (concreteMaximalSeparator G M)).source =
      concreteMaximalSeparator G M := by
  rw [concreteMaximalSeparator_eq_essential]
  exact G.quotient_source_essentialTerminalFrontier_of_isWave M.property

/-! ### Concrete path splicing at the maximal separator -/

namespace ConcreteSplicing

open DirectedPath

noncomputable section

variable (G : DWeb V) (M : G.Wave)

/-- Every noninitial vertex of a quotient walk avoids both the deleted
strict roof and the commitment set. -/
theorem quotientWalk_tail_avoids {S : Set V} {a b : V}
    (p : Walk (G.quotient S).graph a b) :
    ∀ {x}, x ∈ p.support.tail →
      x ∉ G.strictRoof S ∧ x ∉ S := by
  induction p with
  | nil => simp
  | @cons u v w e p ih =>
      intro x hx
      simp only [Walk.support_cons, List.tail_cons] at hx
      have hx' : x = v ∨ x ∈ p.support.tail := by
        cases p <;> simpa using hx
      exact hx'.elim (fun h ↦ h ▸ e.2.2) (fun h ↦ ih h)

/-- Every vertex of the retained frontier terminates a finite member of the
essential part of the old wave. -/
theorem exists_leftFinite
    (s : concreteMaximalSeparator G M) :
    ∃ p : FinitePath G.graph,
      (Sum.inl p : G.DPath) ∈ G.essentialWarpPart M.1 ∧
        p.finish = s.1 := by
  obtain ⟨p, hp, hterm⟩ := s.2
  rcases p with p | r
  · exact ⟨p, hp, Option.some.inj hterm⟩
  · simp at hterm

/-- The old-wave path selected at one retained frontier vertex. -/
noncomputable def leftFinite
    (s : concreteMaximalSeparator G M) : FinitePath G.graph :=
  (exists_leftFinite G M s).choose

theorem leftFinite_mem
    (s : concreteMaximalSeparator G M) :
    (Sum.inl (leftFinite G M s) : G.DPath) ∈
      G.essentialWarpPart M.1 :=
  (exists_leftFinite G M s).choose_spec.1

theorem leftFinite_finish
    (s : concreteMaximalSeparator G M) :
    (leftFinite G M s).finish = s.1 :=
  (exists_leftFinite G M s).choose_spec.2

variable {L : Set (G.quotient (concreteMaximalSeparator G M)).DPath}

/-- A quotient linkage has one finite path starting at every retained
frontier vertex. -/
theorem exists_rightFinite
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    ∃ q : FinitePath
        (G.quotient (concreteMaximalSeparator G M)).graph,
      (Sum.inl q : (G.quotient
        (concreteMaximalSeparator G M)).DPath) ∈ L ∧
        q.start = s.1 := by
  have hsSource : s.1 ∈
      (G.quotient (concreteMaximalSeparator G M)).source := by
    rw [quotient_concreteMaximalSeparator_source G M]
    exact s.2
  have hsInitial : s.1 ∈
      (G.quotient (concreteMaximalSeparator G M)).initialSet L := by
    rw [hL.2.2.1]
    exact hsSource
  obtain ⟨q, hqL, hqstart⟩ := hsInitial
  obtain ⟨q', rfl⟩ := hL.2.1 hqL
  exact ⟨q', hqL, hqstart⟩

/-- The quotient-linkage path selected at one retained frontier vertex. -/
noncomputable def rightFinite
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    FinitePath (G.quotient (concreteMaximalSeparator G M)).graph :=
  (exists_rightFinite G M hL s).choose

theorem rightFinite_mem
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    (Sum.inl (rightFinite G M hL s) :
      (G.quotient (concreteMaximalSeparator G M)).DPath) ∈ L :=
  (exists_rightFinite G M hL s).choose_spec.1

theorem rightFinite_start
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    (rightFinite G M hL s).start = s.1 :=
  (exists_rightFinite G M hL s).choose_spec.2

/-- Lift the selected quotient path to the original digraph. -/
noncomputable def liftedRightFinite
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) : FinitePath G.graph :=
  (rightFinite G M hL s).lift
    (fun {_ _} h ↦ G.quotient_adj_imp h)

theorem liftedRightFinite_start
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    (liftedRightFinite G M hL s).start = s.1 := by
  exact rightFinite_start G M hL s

/-- Display the lifted quotient walk with the old path's terminal as its
initial endpoint. -/
noncomputable def rightWalk
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    Walk G.graph (leftFinite G M s).finish
      (liftedRightFinite G M hL s).finish :=
  RelationalRoof.castStart G.graph.Adj
    ((liftedRightFinite_start G M hL s).trans
      (leftFinite_finish G M s).symm)
    (liftedRightFinite G M hL s).walk

theorem rightWalk_isPath
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    (rightWalk G M hL s).IsPath := by
  rw [Walk.IsPath, rightWalk, RelationalRoof.support_castStart]
  exact (liftedRightFinite G M hL s).isPath

/-- An old-wave path is disjoint from the tail of every selected quotient
path.  This is the key geometric fact behind both simplicity and pairwise
disjointness of the splice. -/
theorem left_support_disjoint_right_tail
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s t : concreteMaximalSeparator G M) :
    (leftFinite G M s).walk.support.Disjoint
      (rightWalk G M hL t).support.tail := by
  rw [List.disjoint_left]
  intro x hxleft hxright
  have hxroof : x ∈ G.roof (concreteMaximalSeparator G M) := by
    apply (essentialWarpPart_isWave G M).self_roofing
    exact ⟨Sum.inl (leftFinite G M s), leftFinite_mem G M s, hxleft⟩
  have hxrightLift : x ∈
      (liftedRightFinite G M hL t).walk.support.tail := by
    simpa only [rightWalk, RelationalRoof.support_castStart] using hxright
  have hsupport :
      (liftedRightFinite G M hL t).walk.support =
        (rightFinite G M hL t).walk.support := by
    change ((rightFinite G M hL t).walk.lift
      (fun {_ _} h ↦ G.quotient_adj_imp h)).support = _
    rw [Walk.support_lift]
  have hxright' : x ∈ (rightFinite G M hL t).walk.support.tail := by
    rw [hsupport] at hxrightLift
    exact hxrightLift
  have havoid := quotientWalk_tail_avoids G
    (rightFinite G M hL t).walk hxright'
  by_cases hxessential : x ∈
      G.essential (concreteMaximalSeparator G M)
  · exact havoid.2
      (G.essential_subset (concreteMaximalSeparator G M) hxessential)
  · exact havoid.1 ⟨hxroof, hxessential⟩

/-- The finite simple path obtained by splicing the old-wave prefix to the
lifted quotient-linkage suffix. -/
noncomputable def splicedFinitePath
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) : FinitePath G.graph :=
  (leftFinite G M s).appendWalkOfDisjoint (rightWalk G M hL s)
    (rightWalk_isPath G M hL s)
    (left_support_disjoint_right_tail G M hL s s)

theorem rightWalk_support
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    (rightWalk G M hL s).support =
      (rightFinite G M hL s).walk.support := by
  rw [rightWalk, RelationalRoof.support_castStart]
  change ((rightFinite G M hL s).walk.lift
    (fun {_ _} h ↦ G.quotient_adj_imp h)).support = _
  rw [Walk.support_lift]

theorem mem_splicedFinitePath_support_iff
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) (x : V) :
    x ∈ (splicedFinitePath G M hL s).support ↔
      x ∈ (leftFinite G M s).walk.support ∨
        x ∈ (rightFinite G M hL s).walk.support.tail := by
  change x ∈ (splicedFinitePath G M hL s).walk.support ↔ _
  simp only [splicedFinitePath, FinitePath.appendWalkOfDisjoint,
    FinitePath.appendWalk_support, List.mem_append,
    rightWalk_support G M hL s]

theorem leftFinite_ne {s t : concreteMaximalSeparator G M}
    (hst : s ≠ t) :
    (Sum.inl (leftFinite G M s) : G.DPath) ≠
      Sum.inl (leftFinite G M t) := by
  intro h
  have hp : leftFinite G M s = leftFinite G M t := Sum.inl.inj h
  apply hst
  apply Subtype.ext
  rw [← leftFinite_finish G M s, hp, leftFinite_finish G M t]

theorem rightFinite_ne
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    {s t : concreteMaximalSeparator G M} (hst : s ≠ t) :
    (Sum.inl (rightFinite G M hL s) :
      (G.quotient (concreteMaximalSeparator G M)).DPath) ≠
      Sum.inl (rightFinite G M hL t) := by
  intro h
  have hp : rightFinite G M hL s = rightFinite G M hL t :=
    Sum.inl.inj h
  apply hst
  apply Subtype.ext
  rw [← rightFinite_start G M hL s, hp, rightFinite_start G M hL t]

/-- Splices indexed by distinct separator vertices are vertex-disjoint. -/
theorem splicedFinitePath_disjoint
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    {s t : concreteMaximalSeparator G M} (hst : s ≠ t) :
    Disjoint (splicedFinitePath G M hL s).support
      (splicedFinitePath G M hL t).support := by
  rw [Set.disjoint_left]
  intro x hxs hxt
  rw [mem_splicedFinitePath_support_iff G M hL s x] at hxs
  rw [mem_splicedFinitePath_support_iff G M hL t x] at hxt
  rcases hxs with hxs | hxs <;> rcases hxt with hxt | hxt
  · have hd := DWeb.IsWarp.disjoint G
      (M.property.1.essentialWarpPart)
      (leftFinite_mem G M s) (leftFinite_mem G M t)
      (leftFinite_ne G M hst)
    exact Set.disjoint_left.1 hd hxs hxt
  · have hd := left_support_disjoint_right_tail G M hL s t
    rw [rightWalk_support G M hL t] at hd
    exact List.disjoint_left.1 hd hxs hxt
  · have hd := left_support_disjoint_right_tail G M hL t s
    rw [rightWalk_support G M hL s] at hd
    exact List.disjoint_left.1 hd hxt hxs
  · have hd := DWeb.IsWarp.disjoint
      (G.quotient (concreteMaximalSeparator G M)) hL.1
      (rightFinite_mem G M hL s) (rightFinite_mem G M hL t)
      (rightFinite_ne G M hL hst)
    exact Set.disjoint_left.1 hd
      (List.mem_of_mem_tail hxs) (List.mem_of_mem_tail hxt)

/-- The bundled original-web `source`--`target` path produced at one
separator vertex. -/
noncomputable def splicedABPath
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    Bridge.DirectedABPath G.graph G.source G.target where
  path := splicedFinitePath G M hL s
  start_mem := by
    apply M.property.2.1
    exact ⟨Sum.inl (leftFinite G M s),
      (leftFinite_mem G M s).1, rfl⟩
  finish_mem := by
    apply CardinalInduction.IsLinkageBetween.terminalFrontier_subset hL
    exact ⟨Sum.inl (rightFinite G M hL s),
      rightFinite_mem G M hL s, rfl⟩

/-- The family of all spliced original-web paths. -/
noncomputable def splicedFamily
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L) :
    Set (Bridge.DirectedABPath G.graph G.source G.target) :=
  Set.range (splicedABPath G M hL)

theorem splicedFamily_isPacking
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L) :
    Bridge.DirectedIsPathPacking (splicedFamily G M hL) := by
  rintro p ⟨s, rfl⟩ q ⟨t, rfl⟩ hpq
  apply splicedFinitePath_disjoint G M hL
  intro hst
  subst t
  exact hpq rfl

theorem separator_mem_splicedFinitePath
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) :
    s.1 ∈ (splicedFinitePath G M hL s).support := by
  rw [mem_splicedFinitePath_support_iff G M hL s s.1]
  left
  rw [← leftFinite_finish G M s]
  exact (leftFinite G M s).finish_mem_support

/-- An old essential-wave path meets the retained frontier only at its
terminal.  Pairwise disjointness of the old warp supplies the argument. -/
theorem eq_separator_of_mem_left_support
    (s : concreteMaximalSeparator G M) {x : V}
    (hxS : x ∈ concreteMaximalSeparator G M)
    (hxleft : x ∈ (leftFinite G M s).support) :
    x = s.1 := by
  let t : concreteMaximalSeparator G M := ⟨x, hxS⟩
  by_contra hxs
  have hst : s ≠ t := by
    intro h
    apply hxs
    exact (congrArg Subtype.val h).symm
  have hd := DWeb.IsWarp.disjoint G
    (M.property.1.essentialWarpPart)
    (leftFinite_mem G M s) (leftFinite_mem G M t)
    (leftFinite_ne G M hst)
  apply Set.disjoint_left.1 hd hxleft
  change x ∈ (leftFinite G M t).support
  have hxfinish : x = (leftFinite G M t).finish := by
    rw [leftFinite_finish G M t]
  rw [hxfinish]
  exact (leftFinite G M t).finish_mem_support

/-- The chosen separator is met exactly at the gluing vertex by each
spliced path. -/
theorem eq_separator_of_mem_spliced_support
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L)
    (s : concreteMaximalSeparator G M) {x : V}
    (hxS : x ∈ concreteMaximalSeparator G M)
    (hxpath : x ∈ (splicedFinitePath G M hL s).support) :
    x = s.1 := by
  rw [mem_splicedFinitePath_support_iff G M hL s x] at hxpath
  rcases hxpath with hxleft | hxright
  · exact eq_separator_of_mem_left_support G M s hxS hxleft
  · exact False.elim
      ((quotientWalk_tail_avoids G
        (rightFinite G M hL s).walk hxright).2 hxS)

theorem splicedFamily_isOrthogonal
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L) :
    Bridge.DirectedIsOrthogonal (splicedFamily G M hL)
      (concreteMaximalSeparator G M) := by
  constructor
  · intro x hxS
    let s : concreteMaximalSeparator G M := ⟨x, hxS⟩
    simp only [Set.mem_iUnion]
    exact ⟨splicedABPath G M hL s, ⟨s, rfl⟩,
      separator_mem_splicedFinitePath G M hL s⟩
  · intro p hp
    obtain ⟨s, rfl⟩ := hp
    refine ⟨s.1, ⟨s.2, separator_mem_splicedFinitePath G M hL s⟩, ?_⟩
    intro x hx
    exact eq_separator_of_mem_spliced_support G M hL s hx.1 hx.2

end

end ConcreteSplicing

/-- The roof formulation of separation is exactly the separator predicate
used by the final directed-to-undirected bridge. -/
theorem concreteMaximalSeparator_isABSeparator
    (G : DWeb V) (M : G.Wave) :
    Bridge.DirectedIsABSeparator G.graph G.source G.target
      (concreteMaximalSeparator G M) := by
  intro q
  have hmeet :=
    source_subset_roof_concreteMaximalSeparator G M q.start_mem q.path
      ⟨rfl, q.finish_mem⟩
  obtain ⟨v, hvq, hvS⟩ := hmeet
  exact ⟨v, hvS, hvq⟩

/-- What the concrete path-splicing operation must return from one quotient
linkage.  Separation is intentionally absent: it is proved independently
from the maximal wave above, so this record does not hide the desired
Menger conclusion. -/
structure ConcreteSpliceWitness (G : DWeb V) (M : G.Wave) where
  paths : Set (Bridge.DirectedABPath G.graph G.source G.target)
  isPacking : Bridge.DirectedIsPathPacking paths
  isOrthogonal :
    Bridge.DirectedIsOrthogonal paths (concreteMaximalSeparator G M)

/-- The fully concrete splice operation.  No graph-theoretic premise beyond
the quotient linkage remains: all choices of old and new path threads and
all disjointness proofs are supplied above. -/
noncomputable def concreteSpliceWitnessOfLinkage
    (G : DWeb V) (M : G.Wave)
    {L : Set (G.quotient (concreteMaximalSeparator G M)).DPath}
    (hL : ConcreteIsLinkageBetween
      (G.quotient (concreteMaximalSeparator G M))
      (G.quotient (concreteMaximalSeparator G M)).source
      (G.quotient (concreteMaximalSeparator G M)).target L) :
    ConcreteSpliceWitness G M where
  paths := ConcreteSplicing.splicedFamily G M hL
  isPacking := ConcreteSplicing.splicedFamily_isPacking G M hL
  isOrthogonal := ConcreteSplicing.splicedFamily_isOrthogonal G M hL

namespace ConcreteSpliceWitness

/-- Add the independently proved separator property to a concrete splice. -/
theorem directedMengerConclusion {G : DWeb V} {M : G.Wave}
    (H : ConcreteSpliceWitness G M) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  exact ⟨H.paths, concreteMaximalSeparator G M, H.isPacking,
    concreteMaximalSeparator_isABSeparator G M, H.isOrthogonal⟩

end ConcreteSpliceWitness

/-- The concrete elementary implication from looseness to unhinderedness. -/
theorem concrete_isUnhindered_of_isLoose (G : DWeb V)
    (hloose : G.IsLoose) : G.IsUnhindered := by
  rw [G.isUnhindered_iff]
  intro W hW
  rw [hloose W hW, G.initialSet_trivialWave]

/-- Concrete reverse Section 5 assembly for one web.

The maximal wave comes from the proved Zorn/direct-limit construction.  Its
normalized quotient is loose, hence unhindered; the locally supplied deep
theorem links that quotient; and the concrete splice gives the path family
orthogonal to the already verified separator. -/
theorem directedMengerConclusion_of_unhinderedWebTheorem
    (G : DWeb V)
    (unhindered_web_theorem : ∀ (Q : DWeb V),
      Q.IsUnhindered → ConcreteIsLinkable Q) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  obtain ⟨M, hMmax⟩ := G.exists_maximal_wave
  let Q := G.quotient (concreteMaximalSeparator G M)
  have hQloose : Q.IsLoose := by
    dsimp only [Q]
    rw [concreteMaximalSeparator_eq_essential]
    exact G.quotient_essentialTerminalFrontier_isLoose_of_isMax
      M.property hMmax
  have hQunhindered : Q.IsUnhindered :=
    concrete_isUnhindered_of_isLoose Q hQloose
  obtain ⟨L, hL⟩ := unhindered_web_theorem Q hQunhindered
  exact (concreteSpliceWitnessOfLinkage G M hL).directedMengerConclusion

/-- Universal concrete adapter in precisely the form consumed by
`Bridge.erdos_599_of_directed_menger`.  The deep theorem remains a local
premise; no project-local assumption is introduced. -/
theorem directedMenger_of_unhinderedWebTheorem
    (unhindered_web_theorem : ∀ (G : DWeb V),
      G.IsUnhindered → ConcreteIsLinkable G)
    (D : Digraph V) (A B : Set V) :
    Bridge.DirectedMengerConclusion D A B := by
  let G : DWeb V :=
    { graph := D
      source := A
      target := B }
  exact directedMengerConclusion_of_unhinderedWebTheorem G
    unhindered_web_theorem

end AharoniBerger
end Erdos599
