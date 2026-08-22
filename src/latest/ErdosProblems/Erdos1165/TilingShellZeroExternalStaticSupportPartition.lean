/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedShellExternalTracePartition

/-!
# External shell-zero atoms refined by their static moved support

The source and fixed-central replacement clocks share an external retained
word, but they do not share current-favorite data.  The additional common
coordinate carrier is the *static* set of domino bases moved by the central
replacement.  At the source clock this is `V₂(I₁)`; at the replacement clock
it is `V₂(I₁) ∪ V₂(I₀)`.  Refining by this set gives a sound common static
split without identifying the two pathwise `V₂(I₁)` supports.
-/

open Set

namespace Erdos1165.TilingShellZeroExternalStaticSupportPartition

open HLOZShellZeroReplacementWindows LazyDecomposition
open TilingOrientedShellExternalTracePartition
open TilingOrientedShellZeroSourcePartition TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The source-clock static support: every moved coordinate starts in `I₁`. -/
def sourceStaticSupport (t : DominoTiling) (o : Orientation)
    (m k w : ℕ) (s : WalkPath) : Finset Point :=
  orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w) s
    (creationTimeNat m k s)

/-- The replacement-clock static support: retained `I₁` and new `I₀`
coordinates together recover the original moved carrier. -/
def replacementStaticSupport (t : DominoTiling) (o : Orientation)
    (m k w total central : ℕ) (s : WalkPath) : Finset Point :=
  let n := creationTimeNat m (replacementCreationRank k total central) s
  orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w) s n ∪
    orientedTilingVTwoBases t o (shellZeroReplacementTotalWindow m w) s n

/-- A valid external source atom refined by the exact static moved support. -/
def orientedValidShellZeroExactSourceStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  orientedValidShellZeroExactSourceExternalTraceAtom t o m k w low
      externalLow externalHigh total z ∩
    {s | sourceStaticSupport t o m k w s = S}

/-- A valid fixed-central replacement atom refined by the same static moved
support, now read as `V₂(I₁) ∪ V₂(I₀)` at the raised clock. -/
def orientedValidShellZeroReplacementStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  orientedValidShellZeroReplacementExternalTraceAtom t o m k w low
      externalLow externalHigh total central z ∩
    {s | replacementStaticSupport t o m k w total central s = S}

theorem iUnion_sourceStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    (⋃ S : Finset Point,
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k w low
        externalLow externalHigh total z S) =
      orientedValidShellZeroExactSourceExternalTraceAtom t o m k w low
        externalLow externalHigh total z := by
  ext s
  simp only [orientedValidShellZeroExactSourceStaticSupportAtom,
    Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨S, hs, _⟩
    exact hs
  · intro hs
    exact ⟨sourceStaticSupport t o m k w s, hs, rfl⟩

theorem iUnion_replacementStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    (⋃ S : Finset Point,
      orientedValidShellZeroReplacementStaticSupportAtom t o m k w low
        externalLow externalHigh total central z S) =
      orientedValidShellZeroReplacementExternalTraceAtom t o m k w low
        externalLow externalHigh total central z := by
  ext s
  simp only [orientedValidShellZeroReplacementStaticSupportAtom,
    Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨S, hs, _⟩
    exact hs
  · intro hs
    exact ⟨replacementStaticSupport t o m k w total central s, hs, rfl⟩

/-- Full valid exact-source coverage by the corrected `(z,S)` carriers. -/
theorem iUnion_all_sourceStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) :
    (⋃ p : OrientedTilingTypedExternalWordCode t × Finset Point,
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k w low
        externalLow externalHigh total p.1 p.2) =
      orientedShellZeroExactSourceEvent t o m k w low externalLow
        externalHigh total ∩ validStepWalk := by
  ext s
  simp only [Set.mem_iUnion,
    orientedValidShellZeroExactSourceStaticSupportAtom,
    orientedValidShellZeroExactSourceExternalTraceAtom,
    orientedShellZeroExactSourceExternalTraceAtom,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨⟨hsource, _⟩, hvalid⟩, _⟩
    exact ⟨hsource, hvalid⟩
  · rintro ⟨hsource, hvalid⟩
    let z := fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s
    let S := sourceStaticSupport t o m k w s
    exact ⟨(z, S), ⟨⟨hsource, rfl⟩, hvalid⟩, rfl⟩

/-- Full valid fixed-central replacement coverage by `(z,S)`, with `S`
read at the raised clock as the union of its `I₁` and `I₀` parts. -/
theorem iUnion_all_replacementStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ) :
    (⋃ p : OrientedTilingTypedExternalWordCode t × Finset Point,
      orientedValidShellZeroReplacementStaticSupportAtom t o m k w low
        externalLow externalHigh total central p.1 p.2) =
      orientedShellZeroFixedCentralReplacementEvent t o m k w low externalLow
        externalHigh total central ∩ validStepWalk := by
  ext s
  simp only [Set.mem_iUnion,
    orientedValidShellZeroReplacementStaticSupportAtom,
    orientedValidShellZeroReplacementExternalTraceAtom,
    orientedShellZeroReplacementExternalTraceAtom,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨⟨hreplacement, _⟩, hvalid⟩, _⟩
    exact ⟨hreplacement, hvalid⟩
  · rintro ⟨hreplacement, hvalid⟩
    let rank := replacementCreationRank k total central
    let z := fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m rank s) s
    let S := replacementStaticSupport t o m k w total central s
    exact ⟨(z, S), ⟨⟨hreplacement, rfl⟩, hvalid⟩, rfl⟩

theorem pairwise_disjoint_sourceStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) :
    Pairwise fun p q : OrientedTilingTypedExternalWordCode t × Finset Point ↦
      Disjoint
        (orientedValidShellZeroExactSourceStaticSupportAtom t o m k w low
          externalLow externalHigh total p.1 p.2)
        (orientedValidShellZeroExactSourceStaticSupportAtom t o m k w low
          externalLow externalHigh total q.1 q.2) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro s hs ht
  apply hpq
  apply Prod.ext
  · exact hs.1.1.2.symm.trans ht.1.1.2
  · exact hs.2.symm.trans ht.2

theorem pairwise_disjoint_replacementStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ) :
    Pairwise fun p q : OrientedTilingTypedExternalWordCode t × Finset Point ↦
      Disjoint
        (orientedValidShellZeroReplacementStaticSupportAtom t o m k w low
          externalLow externalHigh total central p.1 p.2)
        (orientedValidShellZeroReplacementStaticSupportAtom t o m k w low
          externalLow externalHigh total central q.1 q.2) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro s hs ht
  apply hpq
  apply Prod.ext
  · exact hs.1.1.2.symm.trans ht.1.1.2
  · exact hs.2.symm.trans ht.2

/-- Supported source carriers are indexed by both the physical external word
and the static moved support. -/
abbrev SupportedSourceStaticSupportIndex
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) :=
  {p : OrientedTilingTypedExternalWordCode t × Finset Point //
    (orientedValidShellZeroExactSourceStaticSupportAtom t o m k w low
      externalLow externalHigh total p.1 p.2).Nonempty}

end

end Erdos1165.TilingShellZeroExternalStaticSupportPartition
