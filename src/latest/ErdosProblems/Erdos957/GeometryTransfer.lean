import ErdosProblems.Erdos957.GeometryStatement
import ErdosProblems.Erdos957.BisectorPolar
import ErdosProblems.Erdos957.CyclicWindow
import ErdosProblems.Erdos957.CollisionGlue

/-!
# Final geometry-to-certificate composition for Erdős problem 957

This module contains only the checked composition after the genuinely local
case and collision witnesses have been constructed.  The cyclic hull data,
bisector frame, and cyclic-window geometry are the canonical production
objects coming from the radial hull order and its lifted edge directions.

No declaration below assumes a transfer, an incoming-token estimate, or a
capacity bound.  The remaining nonempty-source input is precisely a family
of actual `LocalCase` values together with the primitive role/collision
witnesses consumed by `CollisionGlue`.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957GeometryTransfer

open Erdos957
open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957GeometryLocalityBridge
open Erdos957HullGeometryBridge
open Erdos957BisectorPolar
open Erdos957CyclicWindowConstructor
open Erdos957CollisionInstantiation
open Erdos957Overcharge
open Erdos957TurnSum.HullOrderBridge

/-- The cyclic geometry record genuinely produced from a radial hull order. -/
abbrev producedHullData {A : Finset Erdos957.Point}
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order) : CyclicHullData A :=
  cyclicHullDataOfOrder R.order L

/-- The genuine bisector frame on the produced cyclic geometry. -/
noncomputable abbrev producedFlatFrame {A : Finset Erdos957.Point}
    (hA : IsOneSeparated A) (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order) :
    (producedHullData R L).FlatAlignedFrameData :=
  bisectorFlatAlignedFrameData R.order L hA

/-- The actual cyclic-window geometry used by locality for the produced
radial order and bisector frame. -/
noncomputable def producedCyclicWindowGeometry {A : Finset Erdos957.Point}
    (hA : IsOneSeparated A) (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L)) :
    CyclicWindowGeometry W (producedFlatFrame hA R L) :=
  cyclicWindowGeometry hA R L W

/-- Package role-uniqueness witnesses with the already checked genuine
cyclic-window constructor.  Whole-arrival degree control now discharges the
former degree-five picture premises automatically. -/
noncomputable def roleCollisionWitnessesOfComponents
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L))
    (hlocal : HasLocalCases (producedHullData R L) W
      (producedFlatFrame hA R L).chart)
    (sideOf : Source (producedHullData R L) W →
      Erdos957GeometryCore.Vertex A → Bool)
    (sameSide : ∀ {s t : Source (producedHullData R L) W} {v},
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal s v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal t v →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W s.1 s.property)).1) →
      sideOf s v = sideOf t v → s = t) :
    RoleCollisionWitnesses (producedHullData R L) W
      (producedFlatFrame hA R L) hlocal where
  locality := ⟨producedCyclicWindowGeometry hA R L W⟩
  sideOf := sideOf
  same_side_unique_in_window := sameSide

/-- The strengthened local-row datatype makes all four formerly dangerous
degree-five collision pictures automatic.  Consequently the only collision
input still needed after local cases are selected is the primitive same-side
uniqueness statement inside the genuine seven-vertex window. -/
noncomputable def roleCollisionWitnessesOfSideUniqueness
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L))
    (hlocal : HasLocalCases (producedHullData R L) W
      (producedFlatFrame hA R L).chart)
    (sideOf : Source (producedHullData R L) W →
      Erdos957GeometryCore.Vertex A → Bool)
    (sameSide : ∀ {s t : Source (producedHullData R L) W} {v},
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal s v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal t v →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W s.1 s.property)).1) →
      sideOf s v = sideOf t v → s = t) :
    RoleCollisionWitnesses (producedHullData R L) W
      (producedFlatFrame hA R L) hlocal :=
  roleCollisionWitnessesOfComponents hA R L W hlocal
    sideOf sameSide

/-- Package the strictly smaller side-free collision input: among actual
formula-retaining rows in one seven-window, three pairwise distinct sources
cannot select the same target. -/
noncomputable def noThreeRoleCollisionWitnessesOfComponents
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L))
    (hlocal : HasLocalCases (producedHullData R L) W
      (producedFlatFrame hA R L).chart)
    (hnoThree : ∀ {a b c : Source (producedHullData R L) W} {v},
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal a v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal b v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal c v →
      b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
      c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
      a ≠ b → a ≠ c → b ≠ c → False) :
    NoThreeRoleCollisionWitnesses (producedHullData R L) W
      (producedFlatFrame hA R L) hlocal where
  locality := ⟨producedCyclicWindowGeometry hA R L W⟩
  no_three_in_window := hnoThree

/-- Package the honest weight-aware collision input with the produced cyclic
window geometry.  Three and four contributing rows are allowed; the local
geometry gives the sharp source-count bound and proves the capacity estimate
for actual triples and quadruples. -/
noncomputable def weightedCollisionWitnessesOfComponents
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L))
    (hlocal : HasLocalCases (producedHullData R L) W
      (producedFlatFrame hA R L).chart)
    (hcard : ∀ v,
      (Finset.univ.filter fun s : Source (producedHullData R L) W ↦
        0 < sourceTokens (producedHullData R L) W
          (producedFlatFrame hA R L).chart hlocal s v).card ≤ 4)
    (htriple : ∀ {a b c : Source (producedHullData R L) W} {v},
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal a v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal b v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal c v →
      b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
      c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
      a ≠ b → a ≠ c → b ≠ c →
      Fits ((unitDistanceGraph A).degree v)
        (sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal a v +
          sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal b v +
          sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal c v))
    (hquadruple : ∀ {a b c d : Source (producedHullData R L) W} {v},
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal a v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal b v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal c v →
      0 < sourceTokens (producedHullData R L) W
        (producedFlatFrame hA R L).chart hlocal d v →
      b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
      c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
      d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (producedHullData R L).next j
          (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
      a ≠ b → a ≠ c → a ≠ d →
      b ≠ c → b ≠ d → c ≠ d →
      Fits ((unitDistanceGraph A).degree v)
        (sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal a v +
          sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal b v +
          sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal c v +
          sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal d v)) :
    WeightedCollisionWitnesses (producedHullData R L) W
      (producedFlatFrame hA R L) hlocal where
  locality := ⟨producedCyclicWindowGeometry hA R L W⟩
  contributors_card_le_four := hcard
  triple_fits_in_window := htriple
  quadruple_fits_in_window := hquadruple

/-- Once actual local cases and role collision witnesses exist, all
remaining row extension, Boolean pigeonhole, ten-pair overcharge, and
capacity arithmetic produce the required transfer certificate. -/
theorem transferCert_of_roleCollisionWitnesses
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L))
    (hlocal : HasLocalCases (producedHullData R L) W
      (producedFlatFrame hA R L).chart)
    (C : RoleCollisionWitnesses (producedHullData R L) W
      (producedFlatFrame hA R L) hlocal) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A)
      (producedHullData R L).H
      (distinguishedVertices (producedHullData R L) W)
      (sourceVertices (producedHullData R L) W)) :=
  C.transferCert hA

/-- The side-free no-three window certificate has the same production
transfer consequence. -/
theorem transferCert_of_noThreeRoleCollisionWitnesses
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L))
    (hlocal : HasLocalCases (producedHullData R L) W
      (producedFlatFrame hA R L).chart)
    (C : NoThreeRoleCollisionWitnesses (producedHullData R L) W
      (producedFlatFrame hA R L) hlocal) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A)
      (producedHullData R L).H
      (distinguishedVertices (producedHullData R L) W)
      (sourceVertices (producedHullData R L) W)) :=
  C.transferCert hA

/-- The weight-aware window certificate produces the same transfer
certificate while permitting geometrically safe three-source columns. -/
theorem transferCert_of_weightedCollisionWitnesses
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (producedHullData R L))
    (hlocal : HasLocalCases (producedHullData R L) W
      (producedFlatFrame hA R L).chart)
    (C : WeightedCollisionWitnesses (producedHullData R L) W
      (producedFlatFrame hA R L) hlocal) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A)
      (producedHullData R L).H
      (distinguishedVertices (producedHullData R L) W)
      (sourceVertices (producedHullData R L) W)) :=
  C.transferCert hA

/--
Pure final composition with the source-empty branch discharged internally.

The input `build` is the exact remaining nonempty-source theorem: it returns
actual local cases and primitive role collision witnesses, not a transfer or
capacity estimate.  `RoleCollisionWitnesses` itself contains the genuine
cyclic-window geometry through `SourceLocalityCertificates`.
-/
theorem geometryProducesTransfer_of_nonempty_roleCollisionWitnesses
    (build : ∀ (A : Finset Erdos957.Point) (hA : IsOneSeparated A)
      (R : RadiallySortedCyclicHullOrder A)
      (L : LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (producedHullData R L)),
      (sourceVertices (producedHullData R L) W).Nonempty →
      ∃ hlocal : HasLocalCases (producedHullData R L) W
          (producedFlatFrame hA R L).chart,
        Nonempty (RoleCollisionWitnesses (producedHullData R L) W
          (producedFlatFrame hA R L) hlocal)) :
    GeometryProducesTransfer := by
  intro A hA R L
  dsimp only
  intro W
  let P := producedHullData R L
  by_cases hB : sourceVertices P W = ∅
  · exact transferCert_of_sourceVertices_eq_empty hA P W hB
  · have hBne : (sourceVertices P W).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hB
    obtain ⟨hlocal, ⟨C⟩⟩ := build A hA R L W hBne
    exact C.transferCert hA

/-- Final source-empty/nonempty composition using the minimal side-free
window collision certificate. -/
theorem geometryProducesTransfer_of_nonempty_noThreeRoleCollisionWitnesses
    (build : ∀ (A : Finset Erdos957.Point) (hA : IsOneSeparated A)
      (R : RadiallySortedCyclicHullOrder A)
      (L : LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (producedHullData R L)),
      (sourceVertices (producedHullData R L) W).Nonempty →
      ∃ hlocal : HasLocalCases (producedHullData R L) W
          (producedFlatFrame hA R L).chart,
        Nonempty (NoThreeRoleCollisionWitnesses
          (producedHullData R L) W (producedFlatFrame hA R L) hlocal)) :
    GeometryProducesTransfer := by
  intro A hA R L
  dsimp only
  intro W
  let P := producedHullData R L
  by_cases hB : sourceVertices P W = ∅
  · exact transferCert_of_sourceVertices_eq_empty hA P W hB
  · have hBne : (sourceVertices P W).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hB
    obtain ⟨hlocal, ⟨C⟩⟩ := build A hA R L W hBne
    exact C.transferCert hA

/-- Final source-empty/nonempty composition using the honest weight-aware
collision certificate. -/
theorem geometryProducesTransfer_of_nonempty_weightedCollisionWitnesses
    (build : ∀ (A : Finset Erdos957.Point) (hA : IsOneSeparated A)
      (R : RadiallySortedCyclicHullOrder A)
      (L : LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (producedHullData R L)),
      (sourceVertices (producedHullData R L) W).Nonempty →
      ∃ hlocal : HasLocalCases (producedHullData R L) W
          (producedFlatFrame hA R L).chart,
        Nonempty (WeightedCollisionWitnesses
          (producedHullData R L) W (producedFlatFrame hA R L) hlocal)) :
    GeometryProducesTransfer := by
  intro A hA R L
  dsimp only
  intro W
  let P := producedHullData R L
  by_cases hB : sourceVertices P W = ∅
  · exact transferCert_of_sourceVertices_eq_empty hA P W hB
  · have hBne : (sourceVertices P W).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hB
    obtain ⟨hlocal, ⟨C⟩⟩ := build A hA R L W hBne
    exact C.transferCert hA

/-- Smallest checked final interface: for every nonempty source family,
construct the actual local rows and prove only that three pairwise distinct
arrivals cannot share a target inside the genuine seven-window.  The
bisector frame, window locality, collision arithmetic, and empty-source
branch are all supplied internally. -/
theorem geometryProducesTransfer_of_nonempty_localCases_and_noThree
    (build : ∀ (A : Finset Erdos957.Point) (hA : IsOneSeparated A)
      (R : RadiallySortedCyclicHullOrder A)
      (L : LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (producedHullData R L)),
      (sourceVertices (producedHullData R L) W).Nonempty →
      ∃ hlocal : HasLocalCases (producedHullData R L) W
          (producedFlatFrame hA R L).chart,
        ∀ {a b c : Source (producedHullData R L) W} {v},
          0 < sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal a v →
          0 < sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal b v →
          0 < sourceTokens (producedHullData R L) W
            (producedFlatFrame hA R L).chart hlocal c v →
          b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
            (sevenShift (producedHullData R L).next j
              (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
          c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
            (sevenShift (producedHullData R L).next j
              (sourceIndex (producedHullData R L) W a.1 a.property)).1) →
          a ≠ b → a ≠ c → b ≠ c → False) :
    GeometryProducesTransfer := by
  intro A hA R L
  dsimp only
  intro W
  let P := producedHullData R L
  by_cases hB : sourceVertices P W = ∅
  · exact transferCert_of_sourceVertices_eq_empty hA P W hB
  · have hBne : (sourceVertices P W).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hB
    obtain ⟨hlocal, hnoThree⟩ := build A hA R L W hBne
    exact (noThreeRoleCollisionWitnessesOfComponents
      hA R L W hlocal hnoThree).transferCert hA

end Erdos957GeometryTransfer
