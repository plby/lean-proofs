/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZGapRandomClockScreen
import ErdosProblems.Erdos1165.HLOZSourceOrientedExternalLocalTime
import ErdosProblems.Erdos1165.WalkHorizontalReflection
import ErdosProblems.Erdos1165.WalkOneStepShift

/-!
# Finite source transport table for normalized dominant endpoints

The temporal orientation in a source atom is selected **after** normalizing a
raw shell site to the dominant endpoint of its tiling domino.  It therefore
need not equal the raw band's orientation.  In particular, column tilings
require both endpoint orientations.

This module records the finite table independently of the stopped source
predicate.  Event-specific clock, `D_eta`, `Theta`, and typed-fibre transport
lemmas can use `transportedEndpointSourceEvent`; all scalar window parameters
are passed to the target event unchanged.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceEndpointTransportTable

open LazyDecomposition SpatialInsertionFiber TilingLazyDecomposition
open HLOZGapRandomClockScreen

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The two classes after dominant-endpoint normalization. -/
inductive DominantEndpointClass
  | canonical
  | opposite
  deriving DecidableEq

/-- Replace only the temporal endpoint orientation of a band.  Every scalar,
rank, beta, and phase field is definitionally unchanged. -/
def endpointBandWithOrientation (o : Orientation)
    (band : RandomClockBand) : RandomClockBand :=
  { band with orientation := o }

@[simp] theorem endpointBandWithOrientation_orientation
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).orientation = o := rfl

@[simp] theorem endpointBandWithOrientation_vertexPhase
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).vertexPhase = band.vertexPhase := rfl

@[simp] theorem endpointBandWithOrientation_oldRank
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).oldRank = band.oldRank := rfl

@[simp] theorem endpointBandWithOrientation_newRank
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).newRank = band.newRank := rfl

@[simp] theorem endpointBandWithOrientation_returns
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).returns = band.returns := rfl

@[simp] theorem endpointBandWithOrientation_externalThreshold
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).externalThreshold =
      band.externalThreshold := rfl

@[simp] theorem endpointBandWithOrientation_lazyCap
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).lazyCap = band.lazyCap := rfl

@[simp] theorem endpointBandWithOrientation_beta
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).beta = band.beta := rfl

@[simp] theorem endpointBandWithOrientation_scale
    (o : Orientation) (band : RandomClockBand) :
    (endpointBandWithOrientation o band).scale = band.scale := rfl

/-- The endpoint orientation selected by the checkerboard class of the
normalized dominant endpoint. -/
def dominantEndpointOrientation (x : Point) : Orientation :=
  if EvenPoint x then .even else .shifted

theorem dominantEndpointOrientation_compatible (x : Point) :
    OrientationCompatible (dominantEndpointOrientation x) x := by
  unfold dominantEndpointOrientation
  by_cases hx : EvenPoint x
  · rw [if_pos hx]
    exact hx
  · have hodd : OddPoint x :=
      (PreStoppingSpatialLaw.evenPoint_or_oddPoint x).resolve_left hx
    rw [if_neg hx]
    exact hodd

/-- Canonical/opposite classification of the normalized endpoint. -/
def dominantEndpointClass (t : DominoTiling) (x : Point) :
    DominantEndpointClass :=
  if IsTilingBase t x then .canonical else .opposite

/-- The two impossible checker combinations are made explicit.  Column
tilings allow either temporal orientation in either spatial class. -/
def EndpointTransportAdmissible
    (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass) : Prop :=
  match t, cls with
  | .checker _, .canonical => o = .even
  | .checker _, .opposite => o = .shifted
  | .evenColumns, _ | .oddColumns, _ => True

/-- Opposite checker endpoints become bases for the reversed checker
direction after deleting the first step. -/
def shiftedCheckerTarget (d : Tilings.CheckerDirection) : DominoTiling :=
  .checker (oppositeDirection d)

/-- Reflection swaps the two horizontal column pairings. -/
def reflectedColumnTarget : DominoTiling → DominoTiling
  | .evenColumns => .oddColumns
  | .oddColumns => .evenColumns
  | .checker d => .checker d

/-- Target tiling in the finite transport table. -/
def sourceTransportTargetTiling
    (t : DominoTiling) (cls : DominantEndpointClass) : DominoTiling :=
  match cls, t with
  | .canonical, t => t
  | .opposite, .checker d => shiftedCheckerTarget d
  | .opposite, .evenColumns => .oddColumns
  | .opposite, .oddColumns => .evenColumns

/-- Target temporal orientation.  The checker one-step shift turns the old
shifted endpoint chain into the target even endpoint chain.  Horizontal
reflection preserves checkerboard parity. -/
def sourceTransportTargetOrientation
    (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass) : Orientation :=
  match cls, t with
  | .canonical, _ => o
  | .opposite, .checker _ => .even
  | .opposite, .evenColumns | .opposite, .oddColumns => o

/-- Law-preserving path transform in the table. -/
def sourceTransportPath
    (t : DominoTiling) (cls : DominantEndpointClass) : WalkPath → WalkPath :=
  match cls, t with
  | .canonical, _ => id
  | .opposite, .checker _ => oneStepRecenter
  | .opposite, .evenColumns | .opposite, .oddColumns => horizontalReflectPath

theorem measurable_sourceTransportPath
    (t : DominoTiling) (cls : DominantEndpointClass) :
    Measurable (sourceTransportPath t cls) := by
  cases cls <;> cases t <;>
    simp only [sourceTransportPath] <;>
    first | exact measurable_id | exact measurable_oneStepRecenter |
      exact measurable_horizontalReflectPath

/-- Every row of the finite table preserves simple-random-walk probability. -/
theorem simpleRandomWalk_preimage_sourceTransportPath
    (t : DominoTiling) (cls : DominantEndpointClass)
    {A : Set WalkPath} (hA : MeasurableSet A) :
    simpleRandomWalk (sourceTransportPath t cls ⁻¹' A) =
      simpleRandomWalk A := by
  cases cls <;> cases t <;>
    simp only [sourceTransportPath]
  · rfl
  · rfl
  · rfl
  · exact simpleRandomWalk_preimage_oneStepRecenter hA
  · exact simpleRandomWalk_preimage_horizontalReflectPath hA
  · exact simpleRandomWalk_preimage_horizontalReflectPath hA

/-- The checker spatial class determines the normalized endpoint's temporal
orientation. -/
theorem checker_admissible_of_class_and_compatible
    (d : Tilings.CheckerDirection) (o : Orientation)
    (cls : DominantEndpointClass) (x : Point)
    (hclass : dominantEndpointClass (.checker d) x = cls)
    (hcompatible : OrientationCompatible o x) :
    EndpointTransportAdmissible (.checker d) o cls := by
  have hbaseIff : IsTilingBase (.checker d) x ↔ EvenPoint x := by
    simpa only [IsTilingBase, canonicalEastTiling] using
      (isTilingBase_canonicalEast_iff_evenPoint x)
  cases cls with
  | canonical =>
      have hbase : IsTilingBase (.checker d) x := by
        by_contra hnot
        simp [dominantEndpointClass, hnot] at hclass
      have heven : EvenPoint x := hbaseIff.mp hbase
      cases o with
      | even => rfl
      | shifted =>
          exfalso
          change OddPoint x at hcompatible
          rw [OddPoint, heven] at hcompatible
          exact zero_ne_one hcompatible
  | opposite =>
      have hnot : ¬ IsTilingBase (.checker d) x := by
        intro hbase
        simp [dominantEndpointClass, hbase] at hclass
      have hnotEven : ¬ EvenPoint x := fun heven ↦ hnot (hbaseIff.mpr heven)
      cases o with
      | even => exact (hnotEven hcompatible).elim
      | shifted => rfl

/-- The actual normalized dominant endpoint always selects an admissible row
of the table. -/
theorem endpointTransportAdmissible_dominantEndpoint
    (t : DominoTiling) (x : Point) :
    EndpointTransportAdmissible t (dominantEndpointOrientation x)
      (dominantEndpointClass t x) := by
  cases t with
  | checker d =>
      exact checker_admissible_of_class_and_compatible d
        (dominantEndpointOrientation x) (dominantEndpointClass (.checker d) x)
        x rfl (dominantEndpointOrientation_compatible x)
  | evenColumns => trivial
  | oddColumns => trivial

/-- An event family with the exact shared numerical parameters appearing in
the source screen. -/
abbrev EndpointSourceEventFamily :=
  DominoTiling → Orientation →
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Set WalkPath

/-- Pull a target endpoint-source event back along the selected table row.
The seven numerical parameters are passed literally and unchanged. -/
def transportedEndpointSourceEvent
    (source : EndpointSourceEventFamily)
    (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass)
    (m rank width low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  sourceTransportPath t cls ⁻¹'
    source (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls)
      m rank width low externalLow externalHigh cut

theorem simpleRandomWalk_transportedEndpointSourceEvent
    (source : EndpointSourceEventFamily)
    (t : DominoTiling) (o : Orientation)
    (cls : DominantEndpointClass)
    (m rank width low externalLow externalHigh cut : ℕ)
    (hmeas : MeasurableSet
      (source (sourceTransportTargetTiling t cls)
        (sourceTransportTargetOrientation t o cls)
        m rank width low externalLow externalHigh cut)) :
    simpleRandomWalk
        (transportedEndpointSourceEvent source t o cls m rank width low
          externalLow externalHigh cut) =
      simpleRandomWalk
        (source (sourceTransportTargetTiling t cls)
          (sourceTransportTargetOrientation t o cls)
          m rank width low externalLow externalHigh cut) := by
  exact simpleRandomWalk_preimage_sourceTransportPath t cls hmeas

end

end Erdos1165.HLOZSourceEndpointTransportTable
