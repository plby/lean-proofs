/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos58.AlternativeSharp
import ErdosProblems.Erdos58.Structural.BoundaryApplication
import ErdosProblems.Erdos58.Structural.EndpointApplication
import ErdosProblems.Erdos58.Structural.FanApplication
import ErdosProblems.Erdos58.Structural.LongestCycleBridge
import ErdosProblems.Erdos58.Structural.LongestPath

/-!
# Assembly lemmas for the non-independent longest-path branch

This file contains only unconditional bridges between the representations
used by the longest-path, endpoint-counting, and boundary modules.  In
particular, no odd-cycle family or splicing certificate is an input.

The principal theorem, `endpoint_count_of_longestExteriorPath`, constructs
an `EndpointConfiguration` from an actual longest exterior path and raw
cyclic-position facts, then applies the proved endpoint count.  Both the
path-chord positions and the selected cycle attachments are enumerated here
from their adjacency-defined finsets.  The remaining orientation facts are
isolated in `CyclicOrientation`; they say only where graph neighbours occur
on the chosen oriented cycle.

The final two lemmas record the exact degree split available before the
remaining case analysis and transport the checked `j = 1` equal-neighbour
boundary theorem to `LongestExteriorPath`.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace LongestExteriorPath

variable {C : Erdos58.LongestOddCycle G}

/-- Reverse a longest exterior path.  Global maximality is unchanged. -/
def reverse (P : LongestExteriorPath C) : LongestExteriorPath C where
  first := P.last
  last := P.first
  path := P.path.reverse
  isPath := P.isPath.reverse
  maximal := by
    intro x y q hq
    simpa using P.maximal q hq

@[simp] lemma reverse_length (P : LongestExteriorPath C) :
    P.reverse.path.length = P.path.length := by
  simp [reverse]

/-- The ambient path with its endpoints made definitionally equal to the
underlying vertices of `P.first` and `P.last`. -/
def exactExteriorHom (C : Erdos58.LongestOddCycle G) : exteriorGraph C →g G where
  toFun := fun x ↦ (x : V)
  map_rel' := by
    intro x y hxy
    exact SimpleGraph.induce_adj.mp hxy

def exactAmbientPath (P : LongestExteriorPath C) :
    G.Walk (P.first : V) (P.last : V) :=
  P.path.map (exactExteriorHom C)

@[simp] lemma exactAmbientPath_length (P : LongestExteriorPath C) :
    P.exactAmbientPath.length = P.path.length := by
  exact SimpleGraph.Walk.length_map (exactExteriorHom C) P.path

lemma exactAmbientPath_getVert (P : LongestExteriorPath C) (n : ℕ) :
    P.exactAmbientPath.getVert n = (P.path.getVert n : V) := by
  exact SimpleGraph.Walk.getVert_map
    (f := exactExteriorHom C) (p := P.path) n

lemma exactAmbientPath_isPath (P : LongestExteriorPath C) :
    P.exactAmbientPath.IsPath := by
  exact P.isPath.map Subtype.coe_injective

lemma exactAmbientPath_avoids_cycle (P : LongestExteriorPath C) {v : V}
    (hv : v ∈ P.exactAmbientPath.support) : v ∉ C.carrier := by
  have houtside :
      ∀ z ∈ (P.path.map (exactExteriorHom C)).support, z ∉ C.carrier := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, _hw, rfl⟩ := hz
    exact w.property
  exact houtside v hv

/-- Regard the selected longest exterior path as the actual exterior path
expected by the boundary-cycle constructions. -/
def toBoundaryExteriorPath (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length) :
    ExteriorPath (toEndpointLongestOddCycle C) where
  left := P.first
  right := P.last
  walk := P.exactAmbientPath
  isPath := P.exactAmbientPath_isPath
  positive := by
    simpa using hpos
  avoids_cycle := by
    classical
    intro v hv hvC
    exact P.exactAmbientPath_avoids_cycle hv
      ((mem_toEndpointLongestOddCycle_support_iff C v).mp hvC)

end LongestExteriorPath

namespace CaseAssembly

open EndpointApplication

variable {C : Erdos58.LongestOddCycle G}

/-- The first endpoint's cycle-neighbour positions occurring strictly
between position `0` and a selected attachment of the other endpoint. -/
def selectedCycleNeighborPositions (P : LongestExteriorPath C) (bPos : ℕ) :
    Finset ℕ :=
  (EndpointApplication.cycleNeighborPositions C.walk (P.first : V)).filter
    fun n ↦ 0 < n ∧ n < bPos

/-- Raw graph-theoretic data for an orientation of the
endpoint lemma.  These fields do not assume the existence of any cycle
length or of any spliced cycle. -/
structure CyclicOrientation (P : LongestExteriorPath C) where
  bPos : ℕ
  bPos_le : bPos ≤ C.walk.length
  bPos_adj : G.Adj (P.last : V) (C.walk.getVert bPos)
  selected_pos :
    ∀ n ∈ selectedCycleNeighborPositions P bPos, 0 < n

namespace CyclicOrientation

variable {P : LongestExteriorPath C}

/-- The number of selected first-endpoint attachments in this orientation. -/
abbrev attachmentCount (D : CyclicOrientation P) : ℕ :=
  (selectedCycleNeighborPositions P D.bPos).card

/-- The number of additional first-endpoint neighbours after the compulsory
first edge of the exterior path, including the terminal endpoint when the
two endpoints are adjacent. -/
abbrev chordCount (_D : CyclicOrientation P) : ℕ :=
  (EndpointApplication.interiorChordPositions P.exactAmbientPath).card

/-- Increasing enumeration of the selected cycle-neighbour positions. -/
def attachmentPos (D : CyclicOrientation P) :
    Fin D.attachmentCount → ℕ :=
  (selectedCycleNeighborPositions P D.bPos).orderEmbOfFin rfl

lemma attachmentPos_strictMono (D : CyclicOrientation P) :
    StrictMono D.attachmentPos :=
  (selectedCycleNeighborPositions P D.bPos).orderEmbOfFin rfl |>.strictMono

lemma attachmentPos_mem (D : CyclicOrientation P)
    (i : Fin D.attachmentCount) :
    D.attachmentPos i ∈ selectedCycleNeighborPositions P D.bPos := by
  exact Finset.orderEmbOfFin_mem _ rfl i

lemma attachmentPos_pos (D : CyclicOrientation P)
    (i : Fin D.attachmentCount) : 0 < D.attachmentPos i :=
  D.selected_pos _ (D.attachmentPos_mem i)

lemma attachmentPos_lt (D : CyclicOrientation P)
    (i : Fin D.attachmentCount) : D.attachmentPos i < D.bPos := by
  exact (Finset.mem_filter.mp (D.attachmentPos_mem i)).2.2

lemma attachmentPos_enumerates (D : CyclicOrientation P) :
    Finset.univ.image D.attachmentPos =
      selectedCycleNeighborPositions P D.bPos := by
  exact Finset.image_orderEmbOfFin_univ _ rfl

/-- Increasing enumeration of the actual additional path-neighbour
positions. -/
def chordPos (D : CyclicOrientation P) : Fin D.chordCount → ℕ :=
  (EndpointApplication.interiorChordPositions P.exactAmbientPath).orderEmbOfFin rfl

lemma chordPos_strictMono (D : CyclicOrientation P) :
    StrictMono D.chordPos :=
  (EndpointApplication.interiorChordPositions P.exactAmbientPath).orderEmbOfFin rfl
    |>.strictMono

lemma chordPos_enumerates (D : CyclicOrientation P) :
    Finset.univ.image D.chordPos =
      EndpointApplication.interiorChordPositions P.exactAmbientPath := by
  exact Finset.image_orderEmbOfFin_univ _ rfl

/-- Construct the actual endpoint configuration.  Every walk in
the result is the ambient image of the selected longest exterior path. -/
def toEndpointConfiguration (D : CyclicOrientation P)
    (hpos : 0 < P.path.length) :
    EndpointApplication.EndpointConfiguration G D.attachmentCount D.chordCount where
  longestCycle := toEndpointLongestOddCycle C
  aVertex := P.first
  bVertex := P.last
  path := P.exactAmbientPath
  path_isPath := P.exactAmbientPath_isPath
  path_positive := by simpa using hpos
  path_avoids_cycle := by
    classical
    intro v hv hvC
    exact P.exactAmbientPath_avoids_cycle hv
      ((mem_toEndpointLongestOddCycle_support_iff C v).mp hvC)
  chordPos := D.chordPos
  chordPos_strictMono := D.chordPos_strictMono
  chordPos_enumerates := D.chordPos_enumerates
  aPos := D.attachmentPos
  aPos_strictMono := D.attachmentPos_strictMono
  aPos_pos := D.attachmentPos_pos
  bPos := D.bPos
  aPos_lt_bPos := D.attachmentPos_lt
  bPos_le := by
    simpa [toEndpointLongestOddCycle] using D.bPos_le
  aPos_enumerates := by
    simpa [selectedCycleNeighborPositions, toEndpointLongestOddCycle] using
      D.attachmentPos_enumerates
  bPos_adj := by
    simpa [toEndpointLongestOddCycle] using D.bPos_adj

/-- The proved endpoint count, applied to an actual longest exterior path.
Its only extra inputs are raw adjacency/order facts on the chosen
orientation of the actual longest odd cycle. -/
theorem endpoint_count_of_longestExteriorPath [Finite V]
    (D : CyclicOrientation P) (hpos : 0 < P.path.length)
    (hattach : 0 < D.attachmentCount) :
    EndpointCount.ceilHalf D.attachmentCount + D.chordCount ≤
      (oddCycleLengths G).ncard := by
  exact (D.toEndpointConfiguration hpos).endpoint_count_from_configuration hattach

/-- Zero-chord specialization of `endpoint_count_of_longestExteriorPath`.
The no-chord condition is an adjacency-defined finset equality, not a
splicing certificate. -/
theorem endpoint_count_no_chords_of_longestExteriorPath [Finite V]
    (D : CyclicOrientation P) (hpos : 0 < P.path.length)
    (hattach : 0 < D.attachmentCount)
    (hno : EndpointApplication.interiorChordPositions P.exactAmbientPath = ∅) :
    EndpointCount.ceilHalf D.attachmentCount ≤
      (oddCycleLengths G).ncard := by
  have hcount : D.chordCount = 0 := by
    simp [CyclicOrientation.chordCount, hno]
  simpa [hcount] using D.endpoint_count_of_longestExteriorPath hpos hattach

end CyclicOrientation

/-! ## Canonical rotation at the last endpoint's attachment -/

/-- Rotate the selected longest odd cycle so that the chosen attachment is
the duplicated base/terminal vertex. -/
def rotatedEndpointLongestOddCycle [DecidableEq V] (C : Erdos58.LongestOddCycle G)
    (b : Fin C.walk.length) : EndpointCount.LongestOddCycle G := by
  let x := C.walk.getVert b
  have hx : x ∈ C.walk.support := C.walk.getVert_mem_support b
  exact
    { base := x
      cycle := C.walk.rotate x hx
      isCycle := C.walk_isCycle.rotate hx
      odd_length := by simpa using C.odd
      longest := by
        intro n hn
        simpa using C.maximal hn }

lemma mem_rotatedEndpointLongestOddCycle_support_iff
    [DecidableEq V]
    (C : Erdos58.LongestOddCycle G) (b : Fin C.walk.length) (v : V) :
    v ∈ (rotatedEndpointLongestOddCycle C b).cycle.support ↔ v ∈ C.carrier := by
  let x := C.walk.getVert b
  have hx : x ∈ C.walk.support := C.walk.getVert_mem_support b
  change v ∈ (C.walk.rotate x hx).support ↔ v ∈ C.carrier
  rw [SimpleGraph.Walk.mem_support_rotate_iff]
  exact (mem_toEndpointLongestOddCycle_support_iff C v)

/-- Raw rotated orientation based at an actual cycle attachment of the last
endpoint.  The first endpoint's selected positions and both enumerations
are derived below, rather than stored as certificates. -/
structure RotatedCyclicOrientation (P : LongestExteriorPath C) where
  basePos : Fin C.walk.length
  base_adj : G.Adj (P.last : V) (C.walk.getVert basePos)

namespace RotatedCyclicOrientation

variable [DecidableEq V] {P : LongestExteriorPath C}

abbrev longestCycle (D : RotatedCyclicOrientation P) :
    EndpointCount.LongestOddCycle G :=
  rotatedEndpointLongestOddCycle C D.basePos

def selectedPositions (D : RotatedCyclicOrientation P) : Finset ℕ :=
  (EndpointApplication.cycleNeighborPositions
    D.longestCycle.cycle (P.first : V)).filter fun n ↦
      0 < n ∧ n < D.longestCycle.cycle.length

abbrev attachmentCount (D : RotatedCyclicOrientation P) : ℕ :=
  D.selectedPositions.card

abbrev chordCount (_D : RotatedCyclicOrientation P) : ℕ :=
  (EndpointApplication.interiorChordPositions P.exactAmbientPath).card

def attachmentPos (D : RotatedCyclicOrientation P) :
    Fin D.attachmentCount → ℕ :=
  D.selectedPositions.orderEmbOfFin rfl

def chordPos (D : RotatedCyclicOrientation P) : Fin D.chordCount → ℕ :=
  (EndpointApplication.interiorChordPositions P.exactAmbientPath).orderEmbOfFin rfl

/-- Actual endpoint configuration obtained by rotating at the chosen last
attachment and using the duplicated terminal occurrence as `bPos`. -/
def toEndpointConfiguration (D : RotatedCyclicOrientation P)
    (hpos : 0 < P.path.length) :
    EndpointApplication.EndpointConfiguration G D.attachmentCount D.chordCount where
  longestCycle := D.longestCycle
  aVertex := P.first
  bVertex := P.last
  path := P.exactAmbientPath
  path_isPath := P.exactAmbientPath_isPath
  path_positive := by simpa using hpos
  path_avoids_cycle := by
    intro v hv hvC
    exact P.exactAmbientPath_avoids_cycle hv
      ((mem_rotatedEndpointLongestOddCycle_support_iff C D.basePos v).mp hvC)
  chordPos := D.chordPos
  chordPos_strictMono :=
    (EndpointApplication.interiorChordPositions P.exactAmbientPath).orderEmbOfFin rfl
      |>.strictMono
  chordPos_enumerates := Finset.image_orderEmbOfFin_univ _ rfl
  aPos := D.attachmentPos
  aPos_strictMono := D.selectedPositions.orderEmbOfFin rfl |>.strictMono
  aPos_pos := by
    intro i
    exact (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem D.selectedPositions rfl i)).2.1
  bPos := D.longestCycle.cycle.length
  aPos_lt_bPos := by
    intro i
    exact (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem D.selectedPositions rfl i)).2.2
  bPos_le := le_rfl
  aPos_enumerates := by
    exact Finset.image_orderEmbOfFin_univ _ rfl
  bPos_adj := by
    change G.Adj (P.last : V)
      ((C.walk.rotate (C.walk.getVert D.basePos)
        (C.walk.getVert_mem_support D.basePos)).getVert
          (C.walk.rotate (C.walk.getVert D.basePos)
            (C.walk.getVert_mem_support D.basePos)).length)
    simpa only [SimpleGraph.Walk.getVert_length] using D.base_adj

theorem endpoint_count [Finite V] (D : RotatedCyclicOrientation P)
    (hpos : 0 < P.path.length) (hattach : 0 < D.attachmentCount) :
    EndpointCount.ceilHalf D.attachmentCount + D.chordCount ≤
      (oddCycleLengths G).ncard :=
  (D.toEndpointConfiguration hpos).endpoint_count_from_configuration hattach

end RotatedCyclicOrientation

/-! ## Cardinal bridges for endpoint degree counting -/

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private lemma image_cycleNeighborPositions_eq
    (x : V) (N : Finset V)
    (hN : ∀ v, v ∈ N ↔ G.Adj x v ∧ v ∈ C.carrier) :
    (EndpointApplication.cycleNeighborPositions C.walk x).image
        (fun i ↦ C.walk.getVert i) =
      N := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hadj : G.Adj x (C.walk.getVert i) :=
      (EndpointApplication.mem_cycleNeighborPositions_iff.mp hi).2
    exact (hN _).mpr ⟨hadj,
      (mem_toEndpointLongestOddCycle_support_iff C _).mp
        (C.walk.getVert_mem_support i)⟩
  · intro hv
    have hv' := (hN v).mp hv
    have hsupport : v ∈ C.walk.support := by
      exact (mem_toEndpointLongestOddCycle_support_iff C v).mpr hv'.2
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hsupport
    have hlength : 0 < C.walk.length := by
      rw [C.walk_length]
      have := C.three_le
      omega
    let m := if n = C.walk.length then 0 else n
    have hmlt : m < C.walk.length := by
      dsimp [m]
      split_ifs with h
      · omega
      · omega
    let i : Fin C.walk.length := ⟨m, hmlt⟩
    have hiv : C.walk.getVert i = v := by
      dsimp [i, m]
      split_ifs with h
      · subst n
        simpa only [SimpleGraph.Walk.getVert_length,
          SimpleGraph.Walk.getVert_zero] using hn
      · exact hn
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hiv⟩
    apply EndpointApplication.mem_cycleNeighborPositions_iff.mpr
    exact ⟨i.isLt, hiv ▸ hv'.1⟩

/-- Mapping proper positions of the canonical cycle to vertices identifies
the position-valued and vertex-valued first-endpoint neighbour finsets. -/
lemma image_cycleNeighborPositions_first
    (P : LongestExteriorPath C) :
    (EndpointApplication.cycleNeighborPositions C.walk (P.first : V)).image
        (fun i ↦ C.walk.getVert i) =
      P.firstCycleNeighbors := by
  apply image_cycleNeighborPositions_eq (C := C) (P.first : V)
    P.firstCycleNeighbors
  exact P.mem_firstCycleNeighbors

lemma card_cycleNeighborPositions_first (P : LongestExteriorPath C) :
    (EndpointApplication.cycleNeighborPositions C.walk (P.first : V)).card =
      P.firstCycleNeighbors.card := by
  classical
  let s := EndpointApplication.cycleNeighborPositions C.walk (P.first : V)
  have hinj : Set.InjOn (fun n : ℕ ↦ C.walk.getVert n) s := by
    intro i hi j hj hij
    have hil := (EndpointApplication.mem_cycleNeighborPositions_iff.mp hi).1
    have hjl := (EndpointApplication.mem_cycleNeighborPositions_iff.mp hj).1
    exact C.walk_isCycle.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hij
  have hcard := Finset.card_image_of_injOn hinj
  calc
    (EndpointApplication.cycleNeighborPositions C.walk (P.first : V)).card =
        ((EndpointApplication.cycleNeighborPositions C.walk (P.first : V)).image
          fun i ↦ C.walk.getVert i).card :=
      by simpa only [s] using hcard.symm
    _ = P.firstCycleNeighbors.card :=
      congrArg Finset.card (image_cycleNeighborPositions_first P)

/-- The analogous position/vertex cardinality bridge at the last endpoint. -/
lemma image_cycleNeighborPositions_last
    (P : LongestExteriorPath C) :
    (EndpointApplication.cycleNeighborPositions C.walk (P.last : V)).image
        (fun i ↦ C.walk.getVert i) =
      P.lastCycleNeighbors := by
  apply image_cycleNeighborPositions_eq (C := C) (P.last : V)
    P.lastCycleNeighbors
  exact P.mem_lastCycleNeighbors

lemma card_cycleNeighborPositions_last (P : LongestExteriorPath C) :
    (EndpointApplication.cycleNeighborPositions C.walk (P.last : V)).card =
      P.lastCycleNeighbors.card := by
  classical
  let s := EndpointApplication.cycleNeighborPositions C.walk (P.last : V)
  have hinj : Set.InjOn (fun n : ℕ ↦ C.walk.getVert n) s := by
    intro i hi j hj hij
    have hil := (EndpointApplication.mem_cycleNeighborPositions_iff.mp hi).1
    have hjl := (EndpointApplication.mem_cycleNeighborPositions_iff.mp hj).1
    exact C.walk_isCycle.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hij
  have hcard := Finset.card_image_of_injOn hinj
  calc
    (EndpointApplication.cycleNeighborPositions C.walk (P.last : V)).card =
        ((EndpointApplication.cycleNeighborPositions C.walk (P.last : V)).image
          fun i ↦ C.walk.getVert i).card :=
      by simpa only [s] using hcard.symm
    _ = P.lastCycleNeighbors.card :=
      congrArg Finset.card (image_cycleNeighborPositions_last P)

/-- Forgetting the `Fin` bound identifies the boundary module's cyclic
positions with the natural-number positions used by the endpoint module. -/
lemma image_boundaryCycleNeighborPositions_val (x : V) :
    (Structural.cycleNeighborPositions (toEndpointLongestOddCycle C) x).image
        (fun i : Fin (toEndpointLongestOddCycle C).cycle.length ↦ (i : ℕ)) =
      EndpointApplication.cycleNeighborPositions C.walk x := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    apply EndpointApplication.mem_cycleNeighborPositions_iff.mpr
    exact ⟨i.isLt,
      (Structural.mem_cycleNeighborPositions
        (toEndpointLongestOddCycle C) x i).mp hi⟩
  · intro hn
    have hn' := EndpointApplication.mem_cycleNeighborPositions_iff.mp hn
    let i : Fin (toEndpointLongestOddCycle C).cycle.length :=
      ⟨n, by simpa [toEndpointLongestOddCycle] using hn'.1⟩
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    exact (Structural.mem_cycleNeighborPositions
      (toEndpointLongestOddCycle C) x i).mpr hn'.2

lemma card_boundaryCycleNeighborPositions_eq_endpoint (x : V) :
    (Structural.cycleNeighborPositions (toEndpointLongestOddCycle C) x).card =
      (EndpointApplication.cycleNeighborPositions C.walk x).card := by
  classical
  have hinj : Set.InjOn
      (fun i : Fin (toEndpointLongestOddCycle C).cycle.length ↦ (i : ℕ))
      (Structural.cycleNeighborPositions (toEndpointLongestOddCycle C) x) := by
    intro i _hi j _hj hij
    exact Fin.ext hij
  have hcard := Finset.card_image_of_injOn hinj
  rw [image_boundaryCycleNeighborPositions_val (C := C) x] at hcard
  exact hcard.symm

lemma card_boundaryCycleNeighborPositions_first (P : LongestExteriorPath C) :
    (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).card =
      P.firstCycleNeighbors.card := by
  rw [card_boundaryCycleNeighborPositions_eq_endpoint,
    card_cycleNeighborPositions_first]

lemma card_boundaryCycleNeighborPositions_last (P : LongestExteriorPath C) :
    (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.last : V)).card =
      P.lastCycleNeighbors.card := by
  rw [card_boundaryCycleNeighborPositions_eq_endpoint,
    card_cycleNeighborPositions_last]

private lemma image_endpointCycleNeighborPositions_eq
    (L : EndpointCount.LongestOddCycle G)
    (hsupport : ∀ v : V, v ∈ L.cycle.support ↔ v ∈ C.carrier)
    (x : V) (N : Finset V)
    (hN : ∀ v, v ∈ N ↔ G.Adj x v ∧ v ∈ C.carrier) :
    (EndpointApplication.cycleNeighborPositions L.cycle x).image
        (fun i ↦ L.cycle.getVert i) = N := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hadj : G.Adj x (L.cycle.getVert i) :=
      (EndpointApplication.mem_cycleNeighborPositions_iff.mp hi).2
    exact (hN _).mpr ⟨hadj, (hsupport _).mp (L.cycle.getVert_mem_support i)⟩
  · intro hv
    have hv' := (hN v).mp hv
    have hmem : v ∈ L.cycle.support := (hsupport v).mpr hv'.2
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
    have hlength : 0 < L.cycle.length :=
      Nat.zero_lt_of_lt L.isCycle.three_le_length
    let m := if n = L.cycle.length then 0 else n
    have hmlt : m < L.cycle.length := by
      dsimp [m]
      split_ifs <;> omega
    have hget : L.cycle.getVert m = v := by
      dsimp [m]
      split_ifs with h
      · subst n
        simpa only [SimpleGraph.Walk.getVert_length,
          SimpleGraph.Walk.getVert_zero] using hn
      · exact hn
    apply Finset.mem_image.mpr
    refine ⟨m, ?_, hget⟩
    exact EndpointApplication.mem_cycleNeighborPositions_iff.mpr
      ⟨hmlt, hget ▸ hv'.1⟩

lemma image_rotatedSelectedPositions_first
    {P : LongestExteriorPath C} (D : RotatedCyclicOrientation P) :
    D.selectedPositions.image
        (fun n ↦ D.longestCycle.cycle.getVert n) =
      P.firstCycleNeighbors.erase (C.walk.getVert D.basePos) := by
  classical
  have htotal := image_endpointCycleNeighborPositions_eq
    (C := C) D.longestCycle
    (fun v ↦ mem_rotatedEndpointLongestOddCycle_support_iff
      C D.basePos v)
    (P.first : V) P.firstCycleNeighbors P.mem_firstCycleNeighbors
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      have hzero : n = 0 := by
        apply D.longestCycle.isCycle.getVert_injOn'
          (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega)
        simpa [RotatedCyclicOrientation.longestCycle,
          rotatedEndpointLongestOddCycle] using heq
      omega
    · rw [← htotal]
      exact Finset.mem_image.mpr ⟨n, hn'.1, rfl⟩
  · intro hv
    have hv' := Finset.mem_erase.mp hv
    rw [← htotal] at hv'
    obtain ⟨n, hn, hnv⟩ := Finset.mem_image.mp hv'.2
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, hnv⟩
    apply Finset.mem_filter.mpr
    refine ⟨hn, ?_, (EndpointApplication.mem_cycleNeighborPositions_iff.mp hn).1⟩
    by_contra hnzero
    have hnzero' : n = 0 := by omega
    subst n
    apply hv'.1
    simpa [RotatedCyclicOrientation.longestCycle,
      rotatedEndpointLongestOddCycle] using hnv.symm

lemma RotatedCyclicOrientation.attachmentCount_eq_card_erase
    {P : LongestExteriorPath C} (D : RotatedCyclicOrientation P) :
    D.attachmentCount =
      (P.firstCycleNeighbors.erase (C.walk.getVert D.basePos)).card := by
  classical
  have hinj : Set.InjOn
      (fun n : ℕ ↦ D.longestCycle.cycle.getVert n) D.selectedPositions := by
    intro i hi j hj hij
    have hi' := (Finset.mem_filter.mp hi).2.2
    have hj' := (Finset.mem_filter.mp hj).2.2
    exact D.longestCycle.isCycle.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hij
  calc
    D.attachmentCount =
        (D.selectedPositions.image
          (fun n ↦ D.longestCycle.cycle.getVert n)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (P.firstCycleNeighbors.erase (C.walk.getVert D.basePos)).card :=
      congrArg Finset.card (image_rotatedSelectedPositions_first D)

lemma RotatedCyclicOrientation.attachmentCount_eq_firstCycle_card
    {P : LongestExteriorPath C} (D : RotatedCyclicOrientation P)
    (hnot : ¬G.Adj (P.first : V) (C.walk.getVert D.basePos)) :
    D.attachmentCount = P.firstCycleNeighbors.card := by
  have hmem : C.walk.getVert D.basePos ∉ P.firstCycleNeighbors := by
    rw [P.mem_firstCycleNeighbors]
    exact fun h ↦ hnot h.1
  rw [D.attachmentCount_eq_card_erase,
    Finset.erase_eq_of_notMem hmem]

lemma RotatedCyclicOrientation.reservesOneFirstCycleNeighbor
    {P : LongestExteriorPath C} (D : RotatedCyclicOrientation P)
    (hadj : G.Adj (P.first : V) (C.walk.getVert D.basePos)) :
    D.attachmentCount + 1 = P.firstCycleNeighbors.card := by
  have hcarrier : C.walk.getVert D.basePos ∈ C.carrier :=
    (mem_toEndpointLongestOddCycle_support_iff C _).mp
      (C.walk.getVert_mem_support D.basePos)
  have hmem : C.walk.getVert D.basePos ∈ P.firstCycleNeighbors :=
    (P.mem_firstCycleNeighbors _).mpr ⟨hadj, hcarrier⟩
  have hp : 0 < P.firstCycleNeighbors.card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  rw [D.attachmentCount_eq_card_erase,
    Finset.card_erase_of_mem hmem]
  omega

/-- Choose the extra last-endpoint attachment and rotate there.  Since the
chosen vertex is not adjacent to the first endpoint, all first-endpoint
cycle neighbours occur at selected positive positions. -/
noncomputable def rotatedOrientation_of_extraRightNeighbor
    {P : LongestExteriorPath C}
    (hextra :
      (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V) \
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).Nonempty) :
    {D : RotatedCyclicOrientation P //
      D.attachmentCount = P.firstCycleNeighbors.card} := by
  classical
  let b := hextra.choose
  have hb := hextra.choose_spec
  have hbLast : b ∈ Structural.cycleNeighborPositions
      (toEndpointLongestOddCycle C) (P.last : V) :=
    (Finset.mem_sdiff.mp hb).1
  have hbNotFirst : b ∉ Structural.cycleNeighborPositions
      (toEndpointLongestOddCycle C) (P.first : V) :=
    (Finset.mem_sdiff.mp hb).2
  let D : RotatedCyclicOrientation P :=
    { basePos := b
      base_adj := (Structural.mem_cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.last : V) b).mp hbLast }
  refine ⟨D, D.attachmentCount_eq_firstCycle_card ?_⟩
  intro hadj
  exact hbNotFirst ((Structural.mem_cycleNeighborPositions
    (toEndpointLongestOddCycle C) (P.first : V) b).mpr hadj)

/-- In the equal-neighbour case choose any common attachment and rotate
there.  Its position-zero occurrence is reserved, while every other first
endpoint attachment is selected. -/
noncomputable def rotatedOrientation_of_commonNeighbor
    {P : LongestExteriorPath C}
    (hsame :
      Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V) =
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V))
    (hnonempty :
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).Nonempty) :
    {D : RotatedCyclicOrientation P //
      D.attachmentCount + 1 = P.firstCycleNeighbors.card} := by
  classical
  let b := hnonempty.choose
  have hbFirst : b ∈ Structural.cycleNeighborPositions
      (toEndpointLongestOddCycle C) (P.first : V) := hnonempty.choose_spec
  have hbLast : b ∈ Structural.cycleNeighborPositions
      (toEndpointLongestOddCycle C) (P.last : V) := by
    rw [← hsame]
    exact hbFirst
  let D : RotatedCyclicOrientation P :=
    { basePos := b
      base_adj := (Structural.mem_cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.last : V) b).mp hbLast }
  refine ⟨D, D.reservesOneFirstCycleNeighbor ?_⟩
  exact (Structural.mem_cycleNeighborPositions
    (toEndpointLongestOddCycle C) (P.first : V) b).mp hbFirst

/-- Positions of all exterior neighbours of the first endpoint on the
selected longest path. -/
def firstExteriorNeighborPositions (P : LongestExteriorPath C) : Finset ℕ := by
  classical
  exact Finset.Icc 1 P.exactAmbientPath.length |>.filter fun n ↦
    G.Adj (P.first : V) (P.exactAmbientPath.getVert n)

lemma mem_firstExteriorNeighborPositions_iff (P : LongestExteriorPath C)
    (n : ℕ) :
    n ∈ firstExteriorNeighborPositions P ↔
      1 ≤ n ∧ n ≤ P.exactAmbientPath.length ∧
        G.Adj (P.first : V) (P.exactAmbientPath.getVert n) := by
  classical
  simp [firstExteriorNeighborPositions, and_assoc]

/-- The position-valued exterior neighbours map exactly to the vertex-valued
neighbour finset supplied by `LongestPath`. -/
lemma image_firstExteriorNeighborPositions (P : LongestExteriorPath C) :
    (firstExteriorNeighborPositions P).image
        (fun n ↦ P.exactAmbientPath.getVert n) =
      P.firstExteriorNeighbors := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    have hn' := (mem_firstExteriorNeighborPositions_iff P n).mp hn
    rw [P.mem_firstExteriorNeighbors]
    exact ⟨hn'.2.2,
      P.exactAmbientPath_avoids_cycle
        (P.exactAmbientPath.getVert_mem_support n)⟩
  · intro hv
    rw [P.mem_firstExteriorNeighbors] at hv
    let w : ↑(C.carrierᶜ) := ⟨v, hv.2⟩
    have hwAdj : (exteriorGraph C).Adj P.first w :=
      SimpleGraph.induce_adj.mpr hv.1
    have hwMem : w ∈ P.path.support := P.first_neighbor_mem_support hwAdj
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwMem
    have hnpos : 1 ≤ n := by
      by_contra hnpos
      have hnzero : n = 0 := by omega
      subst n
      have heq : (P.first : V) = v := by
        calc
          (P.first : V) = (P.path.getVert 0 : ↑(C.carrierᶜ)) := by simp
          _ = (w : V) := congrArg Subtype.val hn
          _ = v := rfl
      exact G.irrefl (heq ▸ hv.1)
    have hget : P.exactAmbientPath.getVert n = v := by
      rw [P.exactAmbientPath_getVert]
      exact congrArg Subtype.val hn
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, hget⟩
    apply mem_firstExteriorNeighborPositions_iff P n |>.mpr
    simpa only [P.exactAmbientPath_length, hget] using
      (show 1 ≤ n ∧ n ≤ P.path.length ∧ G.Adj (P.first : V) v from
        ⟨hnpos, hnle, hv.1⟩)

/-- Position-valued exterior neighbours have the same cardinality as the
vertex-valued neighbour finset supplied by longest-path maximality. -/
lemma card_firstExteriorNeighborPositions (P : LongestExteriorPath C) :
    (firstExteriorNeighborPositions P).card =
      P.firstExteriorNeighbors.card := by
  classical
  have hinj : Set.InjOn
      (fun n : ℕ ↦ P.exactAmbientPath.getVert n)
      (firstExteriorNeighborPositions P) := by
    intro a ha b hb hab
    have ha' := (mem_firstExteriorNeighborPositions_iff P a).mp ha
    have hb' := (mem_firstExteriorNeighborPositions_iff P b).mp hb
    exact P.exactAmbientPath_isPath.getVert_injOn
      ha'.2.1 hb'.2.1 hab
  rw [← image_firstExteriorNeighborPositions P]
  exact (Finset.card_image_of_injOn hinj).symm

/-! ## The augmented fan in the common-singleton branch -/

/-- Append a common cycle neighbour to the last endpoint of the exterior
path.  The resulting simple spine starts at the first endpoint and ends at
the common neighbour. -/
def commonNeighborAugmentedSpine (P : LongestExteriorPath C)
    (base : Fin C.walk.length)
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base)) :
    G.Walk (P.first : V) (C.walk.getVert base) :=
  P.exactAmbientPath.concat hbaseLast

lemma commonNeighborAugmentedSpine_isPath
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base)) :
    (commonNeighborAugmentedSpine P base hbaseLast).IsPath := by
  apply P.exactAmbientPath_isPath.concat
  · intro hmem
    exact P.exactAmbientPath_avoids_cycle hmem
      ((mem_toEndpointLongestOddCycle_support_iff C _).mp
        (C.walk.getVert_mem_support base))

@[simp] lemma commonNeighborAugmentedSpine_length
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base)) :
    (commonNeighborAugmentedSpine P base hbaseLast).length =
      P.exactAmbientPath.length + 1 := by
  simp [commonNeighborAugmentedSpine]

/-- The selected exterior-neighbour positions used in the augmented fan.
They are the first `2*j` elements of the ordered adjacency-defined finset. -/
noncomputable def commonNeighborExteriorPosition {j : ℕ}
    (P : LongestExteriorPath C)
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card) :
    Fin (2 * j) → ℕ := fun i ↦
  (firstExteriorNeighborPositions P).orderEmbOfFin rfl
    ⟨i, i.isLt.trans_le hmany⟩

lemma commonNeighborExteriorPosition_mem {j : ℕ}
    (P : LongestExteriorPath C)
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card)
    (i : Fin (2 * j)) :
    commonNeighborExteriorPosition P hmany i ∈
      firstExteriorNeighborPositions P := by
  exact Finset.orderEmbOfFin_mem _ rfl _

lemma commonNeighborExteriorPosition_injective {j : ℕ}
    (P : LongestExteriorPath C)
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card) :
    Function.Injective (commonNeighborExteriorPosition P hmany) := by
  intro a b hab
  have hlift :
      (⟨a, a.isLt.trans_le hmany⟩ : Fin
          (firstExteriorNeighborPositions P).card) =
        ⟨b, b.isLt.trans_le hmany⟩ :=
    ((firstExteriorNeighborPositions P).orderEmbOfFin rfl).injective hab
  apply Fin.ext
  exact congrArg
    (fun z : Fin (firstExteriorNeighborPositions P).card ↦ z.val) hlift

/-- Put the common cycle neighbour after all selected exterior neighbours.
The `Fin.lastCases` presentation makes it the last marked fan position. -/
noncomputable def commonNeighborAugmentedPosition {j : ℕ}
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base))
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card) :
    Fin (2 * j + 1) → ℕ :=
  Fin.lastCases (commonNeighborAugmentedSpine P base hbaseLast).length
    (commonNeighborExteriorPosition P hmany)

lemma commonNeighborAugmentedPosition_pos {j : ℕ}
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base))
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card)
    (i : Fin (2 * j + 1)) :
    0 < commonNeighborAugmentedPosition P base hbaseLast hmany i := by
  induction i using Fin.lastCases with
  | last => simp [commonNeighborAugmentedPosition]
  | cast i =>
      have hi := (mem_firstExteriorNeighborPositions_iff P _).mp
        (commonNeighborExteriorPosition_mem P hmany i)
      simp only [commonNeighborAugmentedPosition, Fin.lastCases_castSucc]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one hi.1

lemma commonNeighborAugmentedPosition_le {j : ℕ}
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base))
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card)
    (i : Fin (2 * j + 1)) :
    commonNeighborAugmentedPosition P base hbaseLast hmany i ≤
      (commonNeighborAugmentedSpine P base hbaseLast).length := by
  induction i using Fin.lastCases with
  | last => simp [commonNeighborAugmentedPosition]
  | cast i =>
      have hi := (mem_firstExteriorNeighborPositions_iff P _).mp
        (commonNeighborExteriorPosition_mem P hmany i)
      simp only [commonNeighborAugmentedPosition, Fin.lastCases_castSucc,
        commonNeighborAugmentedSpine_length]
      omega

lemma commonNeighborAugmentedPosition_injective {j : ℕ}
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base))
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card) :
    Function.Injective
      (commonNeighborAugmentedPosition P base hbaseLast hmany) := by
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast b =>
          have hb := (mem_firstExteriorNeighborPositions_iff P _).mp
            (commonNeighborExteriorPosition_mem P hmany b)
          simp only [commonNeighborAugmentedPosition,
            Fin.lastCases_last, Fin.lastCases_castSucc,
            commonNeighborAugmentedSpine_length] at hab
          omega
  | cast a =>
      induction b using Fin.lastCases with
      | last =>
          have ha := (mem_firstExteriorNeighborPositions_iff P _).mp
            (commonNeighborExteriorPosition_mem P hmany a)
          simp only [commonNeighborAugmentedPosition,
            Fin.lastCases_last, Fin.lastCases_castSucc,
            commonNeighborAugmentedSpine_length] at hab
          omega
      | cast b =>
          have heq : a = b :=
            commonNeighborExteriorPosition_injective P hmany (by
            simpa [commonNeighborAugmentedPosition] using hab)
          exact congrArg Fin.castSucc heq

/-- The common-singleton endpoint geometry supplies a genuine endpoint fan:
`2*j` neighbours lie on the exterior path and the common cycle neighbour is
the final, additional spoke. -/
noncomputable def commonNeighborAugmentedFan {j : ℕ}
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseFirst : G.Adj (P.first : V) (C.walk.getVert base))
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base))
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card) :
    EndpointFanData G (P.first : V) (C.walk.getVert base) j where
  path := commonNeighborAugmentedSpine P base hbaseLast
  isPath := commonNeighborAugmentedSpine_isPath P base hbaseLast
  position := commonNeighborAugmentedPosition P base hbaseLast hmany
  position_pos := commonNeighborAugmentedPosition_pos P base hbaseLast hmany
  position_le := commonNeighborAugmentedPosition_le P base hbaseLast hmany
  position_injective :=
    commonNeighborAugmentedPosition_injective P base hbaseLast hmany
  spoke := by
    intro i
    induction i using Fin.lastCases with
    | last =>
        simp only [commonNeighborAugmentedPosition,
          Fin.lastCases_last]
        change G.Adj (P.first : V)
          ((commonNeighborAugmentedSpine P base hbaseLast).getVert
            (commonNeighborAugmentedSpine P base hbaseLast).length)
        simpa only [SimpleGraph.Walk.getVert_length] using hbaseFirst
    | cast i =>
        have hi := (mem_firstExteriorNeighborPositions_iff P _).mp
          (commonNeighborExteriorPosition_mem P hmany i)
        have hile : commonNeighborExteriorPosition P hmany i ≤
            P.exactAmbientPath.length := hi.2.1
        simp only [commonNeighborAugmentedPosition,
          Fin.lastCases_castSucc]
        change G.Adj (P.first : V)
          ((commonNeighborAugmentedSpine P base hbaseLast).getVert
            (commonNeighborExteriorPosition P hmany i))
        rw [commonNeighborAugmentedSpine,
          SimpleGraph.Walk.concat_eq_append,
          SimpleGraph.Walk.getVert_append', if_pos hile]
        exact hi.2.2

@[simp] lemma commonNeighborAugmentedFan_position_last {j : ℕ}
    (P : LongestExteriorPath C) (base : Fin C.walk.length)
    (hbaseFirst : G.Adj (P.first : V) (C.walk.getVert base))
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base))
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card) :
    (commonNeighborAugmentedFan P base hbaseFirst hbaseLast hmany).position
        (Fin.last (2 * j)) =
      (commonNeighborAugmentedFan P base hbaseFirst hbaseLast hmany).path.length := by
  change commonNeighborAugmentedPosition P base hbaseLast hmany
      (Fin.last (2 * j)) =
    (commonNeighborAugmentedSpine P base hbaseLast).length
  simp [commonNeighborAugmentedPosition]

@[simp] lemma commonNeighborAugmentedFan_position_zero {j : ℕ}
    (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length) (base : Fin C.walk.length)
    (hbaseFirst : G.Adj (P.first : V) (C.walk.getVert base))
    (hbaseLast : G.Adj (P.last : V) (C.walk.getVert base))
    (hmany : 2 * j ≤ (firstExteriorNeighborPositions P).card) :
    (commonNeighborAugmentedFan P base hbaseFirst hbaseLast hmany).position
        (0 : Fin (2 * j + 1)) = 1 := by
  classical
  let S := firstExteriorNeighborPositions P
  have honeMem : 1 ∈ S := by
    apply (mem_firstExteriorNeighborPositions_iff P 1).mpr
    have hambientPos : 0 < P.exactAmbientPath.length := by simpa using hpos
    have hadj := P.exactAmbientPath.adj_getVert_succ
      (i := 0) hambientPos
    exact ⟨by omega, by omega, by simpa using hadj⟩
  have hcardPos : 0 < S.card := by
    change 0 < (firstExteriorNeighborPositions P).card
    omega
  let i0 : Fin (2 * j) := ⟨0, by omega⟩
  have hzeroValue :
      commonNeighborExteriorPosition P hmany i0 =
        S.min' ⟨1, honeMem⟩ := by
    simpa [commonNeighborExteriorPosition, S, i0] using
      Finset.orderEmbOfFin_zero (s := S) rfl hcardPos
  have hminPos := (mem_firstExteriorNeighborPositions_iff P
    (S.min' ⟨1, honeMem⟩)).mp (Finset.min'_mem S _)
  have hminLe := Finset.min'_le S 1 honeMem
  change commonNeighborAugmentedPosition P base hbaseLast hmany
      (0 : Fin (2 * j + 1)) = 1
  rw [show (0 : Fin (2 * j + 1)) =
      i0.castSucc by rfl]
  simp only [commonNeighborAugmentedPosition, Fin.lastCases_castSucc,
    hzeroValue]
  omega

/-- If the first endpoint has a unique cycle neighbour, its minimum-degree
bound supplies the `2*j` exterior positions needed by the augmented fan. -/
lemma two_mul_le_firstExteriorPositions_of_singleton {j : ℕ}
    (P : LongestExteriorPath C)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hsingleton : P.firstCycleNeighbors.card = 1) :
    2 * j ≤ (firstExteriorNeighborPositions P).card := by
  have hsplit := P.card_firstCycleNeighbors_add_card_firstExteriorNeighbors
  rw [card_firstExteriorNeighborPositions]
  omega

/-- The compulsory first edge and all later neighbour positions (including
the terminal endpoint when it is adjacent to the first endpoint) partition
all exterior neighbours of the first endpoint. -/
lemma firstExteriorNeighborPositions_eq_insert_interior
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length) :
    firstExteriorNeighborPositions P =
      insert 1 (EndpointApplication.interiorChordPositions P.exactAmbientPath) := by
  classical
  ext n
  constructor
  · intro hn
    have hn' := (mem_firstExteriorNeighborPositions_iff P n).mp hn
    by_cases hn1 : n = 1
    · simp [hn1]
    · simp only [Finset.mem_insert]
      right
      exact EndpointApplication.mem_interiorChordPositions_iff.mpr
        ⟨by omega, hn'.2.1, hn'.2.2⟩
  · intro hn
    simp only [Finset.mem_insert] at hn
    apply mem_firstExteriorNeighborPositions_iff P n |>.mpr
    rcases hn with rfl | hn
    · have hadj := P.exactAmbientPath.adj_getVert_succ (i := 0)
        (by simpa using hpos)
      have hlen : 1 ≤ P.exactAmbientPath.length := by
        rw [P.exactAmbientPath_length]
        omega
      exact ⟨by omega, hlen, by simpa using hadj⟩
    · have hn' := EndpointApplication.mem_interiorChordPositions_iff.mp hn
      exact ⟨by omega, hn'.2.1, hn'.2.2⟩

/-- The endpoint lemma's path-chord parameter is exactly the exterior degree
minus the compulsory first edge, whether or not the path endpoints are
adjacent. -/
lemma chordCount_eq_firstExterior_card_sub_one
    (P : LongestExteriorPath C) (D : CyclicOrientation P)
    (hpos : 0 < P.path.length) :
    D.chordCount = P.firstExteriorNeighbors.card - 1 := by
  classical
  let s := firstExteriorNeighborPositions P
  have hinj : Set.InjOn (fun n : ℕ ↦ P.exactAmbientPath.getVert n) s := by
    intro i hi j hj hij
    have hi' := (mem_firstExteriorNeighborPositions_iff P i).mp hi
    have hj' := (mem_firstExteriorNeighborPositions_iff P j).mp hj
    exact P.exactAmbientPath_isPath.getVert_injOn hi'.2.1 hj'.2.1 hij
  have himageCard := Finset.card_image_of_injOn hinj
  have hsCard : s.card = P.firstExteriorNeighbors.card := by
    rw [← image_firstExteriorNeighborPositions P]
    exact himageCard.symm
  have hpartition :=
    firstExteriorNeighborPositions_eq_insert_interior P hpos
  have hone : 1 ∉ EndpointApplication.interiorChordPositions P.exactAmbientPath := by
    exact fun h ↦ (EndpointApplication.mem_interiorChordPositions_iff.mp h).1.ne rfl
  change (EndpointApplication.interiorChordPositions P.exactAmbientPath).card =
    P.firstExteriorNeighbors.card - 1
  have hcardPartition := congrArg Finset.card hpartition
  rw [Finset.card_insert_of_notMem hone] at hcardPartition
  dsimp [s] at hsCard
  omega

lemma RotatedCyclicOrientation.chordCount_eq_firstExterior_card_sub_one
    {P : LongestExteriorPath C} (D : RotatedCyclicOrientation P)
    (hpos : 0 < P.path.length) :
    D.chordCount = P.firstExteriorNeighbors.card - 1 := by
  classical
  let s := firstExteriorNeighborPositions P
  have hinj : Set.InjOn (fun n : ℕ ↦ P.exactAmbientPath.getVert n) s := by
    intro i hi j hj hij
    have hi' := (mem_firstExteriorNeighborPositions_iff P i).mp hi
    have hj' := (mem_firstExteriorNeighborPositions_iff P j).mp hj
    exact P.exactAmbientPath_isPath.getVert_injOn hi'.2.1 hj'.2.1 hij
  have himageCard := Finset.card_image_of_injOn hinj
  have hsCard : s.card = P.firstExteriorNeighbors.card := by
    rw [← image_firstExteriorNeighborPositions P]
    exact himageCard.symm
  have hpartition := firstExteriorNeighborPositions_eq_insert_interior P hpos
  have hone : 1 ∉ EndpointApplication.interiorChordPositions P.exactAmbientPath := by
    exact fun h ↦
      (EndpointApplication.mem_interiorChordPositions_iff.mp h).1.ne rfl
  change (EndpointApplication.interiorChordPositions P.exactAmbientPath).card =
    P.firstExteriorNeighbors.card - 1
  have hcardPartition := congrArg Finset.card hpartition
  rw [Finset.card_insert_of_notMem hone] at hcardPartition
  dsimp [s] at hsCard
  omega

/-- The endpoint module's natural-number chord positions are exactly the
left-chord positions used by the boundary module. -/
lemma image_leftChordPositions_val
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length) :
    (leftChordPositions (P.toBoundaryExteriorPath hpos)).image
        (fun i : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) ↦
          (i : ℕ)) =
      EndpointApplication.interiorChordPositions P.exactAmbientPath := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have hi' : 1 < (i : ℕ) ∧
        G.Adj (P.first : V) (P.exactAmbientPath.getVert i) := by
      simpa [LongestExteriorPath.toBoundaryExteriorPath] using
        (mem_leftChordPositions (P.toBoundaryExteriorPath hpos) i).mp hi
    apply EndpointApplication.mem_interiorChordPositions_iff.mpr
    refine ⟨hi'.1, ?_, hi'.2⟩
    have hil := i.isLt
    have hile : (i : ℕ) ≤ (P.toBoundaryExteriorPath hpos).walk.length := by
      omega
    simpa [LongestExteriorPath.toBoundaryExteriorPath] using hile
  · intro hn
    have hn' := EndpointApplication.mem_interiorChordPositions_iff.mp hn
    let i : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) :=
      ⟨n, by
        simp only [LongestExteriorPath.toBoundaryExteriorPath]
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    apply (mem_leftChordPositions (P.toBoundaryExteriorPath hpos) i).mpr
    simpa [LongestExteriorPath.toBoundaryExteriorPath, i] using
      And.intro hn'.1 hn'.2.2

/-- Consequently the one-sided endpoint parameter `q` is exactly the
number of left chords in the boundary representation. -/
lemma leftChordPositions_card_eq_chordCount
    (P : LongestExteriorPath C) (D : CyclicOrientation P)
    (hpos : 0 < P.path.length) :
    (leftChordPositions (P.toBoundaryExteriorPath hpos)).card = D.chordCount := by
  classical
  have hinj : Set.InjOn
      (fun i : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) ↦ (i : ℕ))
      (leftChordPositions (P.toBoundaryExteriorPath hpos)) := by
    intro i _hi j _hj hij
    exact Fin.ext hij
  have hcard := Finset.card_image_of_injOn hinj
  rw [image_leftChordPositions_val P hpos] at hcard
  exact hcard.symm

lemma leftChordPositions_eq_empty_of_chordCount_eq_zero
    (P : LongestExteriorPath C) (D : CyclicOrientation P)
    (hpos : 0 < P.path.length) (hq : D.chordCount = 0) :
    leftChordPositions (P.toBoundaryExteriorPath hpos) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [leftChordPositions_card_eq_chordCount P D hpos, hq]

lemma RotatedCyclicOrientation.leftChordPositions_card_eq_chordCount
    {P : LongestExteriorPath C} (D : RotatedCyclicOrientation P)
    (hpos : 0 < P.path.length) :
    (leftChordPositions (P.toBoundaryExteriorPath hpos)).card = D.chordCount := by
  classical
  have hinj : Set.InjOn
      (fun i : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) ↦ (i : ℕ))
      (leftChordPositions (P.toBoundaryExteriorPath hpos)) := by
    intro i _hi j _hj hij
    exact Fin.ext hij
  have hcard := Finset.card_image_of_injOn hinj
  rw [image_leftChordPositions_val P hpos] at hcard
  exact hcard.symm

lemma RotatedCyclicOrientation.leftChordPositions_eq_empty_of_chordCount_eq_zero
    {P : LongestExteriorPath C} (D : RotatedCyclicOrientation P)
    (hpos : 0 < P.path.length) (hq : D.chordCount = 0) :
    leftChordPositions (P.toBoundaryExteriorPath hpos) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [D.leftChordPositions_card_eq_chordCount hpos, hq]

/-- The first edge of a positive exterior path is an exterior neighbour of
its first endpoint. -/
lemma firstExteriorNeighbors_card_pos (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length) : 0 < P.firstExteriorNeighbors.card := by
  classical
  let w : V := P.exactAmbientPath.getVert 1
  have hadj : G.Adj (P.first : V) w := by
    have hambient : 0 < P.exactAmbientPath.length := by simpa using hpos
    simpa [w] using P.exactAmbientPath.adj_getVert_succ (i := 0) hambient
  have hwSupport : w ∈ P.exactAmbientPath.support :=
    P.exactAmbientPath.getVert_mem_support 1
  have hwOutside : w ∈ C.carrierᶜ := P.exactAmbientPath_avoids_cycle hwSupport
  apply Finset.card_pos.mpr
  exact ⟨w, (P.mem_firstExteriorNeighbors w).mpr ⟨hadj, hwOutside⟩⟩

/-- The last edge of a positive exterior path is an exterior neighbour of
its last endpoint. -/
lemma lastExteriorNeighbors_card_pos (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length) : 0 < P.lastExteriorNeighbors.card := by
  classical
  let q := P.exactAmbientPath.reverse
  let w : V := q.getVert 1
  have hqpos : 0 < q.length := by
    simpa [q] using hpos
  have hadj : G.Adj (P.last : V) w := by
    simpa [q, w] using q.adj_getVert_succ (i := 0) hqpos
  have hwReverse : w ∈ q.support := q.getVert_mem_support 1
  have hwSupport : w ∈ P.exactAmbientPath.support := by
    simpa [q, SimpleGraph.Walk.support_reverse] using hwReverse
  have hwOutside : w ∈ C.carrierᶜ := P.exactAmbientPath_avoids_cycle hwSupport
  apply Finset.card_pos.mpr
  exact ⟨w, (P.mem_lastExteriorNeighbors w).mpr ⟨hadj, hwOutside⟩⟩

/-- Positions strictly before the terminal occurrence at which the last
endpoint has an exterior neighbour. -/
def lastExteriorNeighborPositions (P : LongestExteriorPath C) : Finset ℕ := by
  classical
  exact Finset.range P.exactAmbientPath.length |>.filter fun n ↦
    G.Adj (P.last : V) (P.exactAmbientPath.getVert n)

lemma mem_lastExteriorNeighborPositions_iff
    (P : LongestExteriorPath C) (n : ℕ) :
    n ∈ lastExteriorNeighborPositions P ↔
      n < P.exactAmbientPath.length ∧
        G.Adj (P.last : V) (P.exactAmbientPath.getVert n) := by
  classical
  simp [lastExteriorNeighborPositions]

/-- The position-valued last-endpoint neighbours map exactly to the
vertex-valued finset supplied by longest-path maximality. -/
lemma image_lastExteriorNeighborPositions (P : LongestExteriorPath C) :
    (lastExteriorNeighborPositions P).image
        (fun n ↦ P.exactAmbientPath.getVert n) =
      P.lastExteriorNeighbors := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    have hn' := (mem_lastExteriorNeighborPositions_iff P n).mp hn
    rw [P.mem_lastExteriorNeighbors]
    exact ⟨hn'.2, P.exactAmbientPath_avoids_cycle
      (P.exactAmbientPath.getVert_mem_support n)⟩
  · intro hv
    rw [P.mem_lastExteriorNeighbors] at hv
    let w : ↑(C.carrierᶜ) := ⟨v, hv.2⟩
    have hwAdj : (exteriorGraph C).Adj P.last w :=
      SimpleGraph.induce_adj.mpr hv.1
    have hwMem : w ∈ P.path.support := P.last_neighbor_mem_support hwAdj
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwMem
    have hget : P.exactAmbientPath.getVert n = v := by
      rw [P.exactAmbientPath_getVert]
      exact congrArg Subtype.val hn
    have hnlt : n < P.exactAmbientPath.length := by
      rw [P.exactAmbientPath_length]
      by_contra h
      have hne : n = P.path.length := by omega
      subst n
      have heq : (P.last : V) = v := by
        rw [← P.exactAmbientPath_length] at hget
        simpa only [SimpleGraph.Walk.getVert_length] using hget
      exact G.irrefl (heq ▸ hv.1)
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, hget⟩
    exact (mem_lastExteriorNeighborPositions_iff P n).mpr
      ⟨hnlt, by simpa [hget] using hv.1⟩

/-- Apart from the compulsory final path edge, the remaining last-endpoint
neighbours are exactly the boundary module's right chords. -/
lemma lastExteriorNeighborPositions_eq_insert_rightChords
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length) :
    lastExteriorNeighborPositions P =
      insert (P.exactAmbientPath.length - 1)
        ((rightChordPositions (P.toBoundaryExteriorPath hpos)).image
          (fun i : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) ↦
            (i : ℕ))) := by
  classical
  ext n
  constructor
  · intro hn
    have hn' := (mem_lastExteriorNeighborPositions_iff P n).mp hn
    by_cases hlast : n = P.exactAmbientPath.length - 1
    · simp [hlast]
    · simp only [Finset.mem_insert]
      right
      let i : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) :=
        ⟨n, by
          simp only [LongestExteriorPath.toBoundaryExteriorPath]
          omega⟩
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      apply (mem_rightChordPositions (P.toBoundaryExteriorPath hpos) i).mpr
      simpa [LongestExteriorPath.toBoundaryExteriorPath, i] using
        (show n + 1 < P.exactAmbientPath.length ∧
            G.Adj (P.last : V) (P.exactAmbientPath.getVert n) by
          constructor
          · have hlen : 0 < P.exactAmbientPath.length := by simpa using hpos
            omega
          · exact hn'.2)
  · intro hn
    simp only [Finset.mem_insert] at hn
    apply (mem_lastExteriorNeighborPositions_iff P n).mpr
    rcases hn with rfl | hn
    · have hlen : 0 < P.exactAmbientPath.length := by simpa using hpos
      have hadj := P.exactAmbientPath.adj_getVert_succ
        (i := P.exactAmbientPath.length - 1) (by omega)
      have hindex : P.exactAmbientPath.length - 1 + 1 =
          P.exactAmbientPath.length := by omega
      rw [hindex, SimpleGraph.Walk.getVert_length] at hadj
      exact ⟨by omega, hadj.symm⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      have hi' :=
        (mem_rightChordPositions (P.toBoundaryExteriorPath hpos) i).mp hi
      have hilen : (i : ℕ) + 1 < P.exactAmbientPath.length := by
        simpa only [LongestExteriorPath.toBoundaryExteriorPath] using hi'.1
      exact ⟨by omega,
        by simpa [LongestExteriorPath.toBoundaryExteriorPath] using hi'.2⟩

/-- Right chords count every exterior neighbour of the last endpoint except
the compulsory final path edge. -/
lemma rightChordPositions_card_eq_lastExterior_card_sub_one
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length) :
    (rightChordPositions (P.toBoundaryExteriorPath hpos)).card =
      P.lastExteriorNeighbors.card - 1 := by
  classical
  let s := lastExteriorNeighborPositions P
  have hinjVert : Set.InjOn
      (fun n : ℕ ↦ P.exactAmbientPath.getVert n) s := by
    intro i hi j hj hij
    have hi' := (mem_lastExteriorNeighborPositions_iff P i).mp hi
    have hj' := (mem_lastExteriorNeighborPositions_iff P j).mp hj
    exact P.exactAmbientPath_isPath.getVert_injOn hi'.1.le hj'.1.le hij
  have hsCard : s.card = P.lastExteriorNeighbors.card := by
    rw [← image_lastExteriorNeighborPositions P]
    exact (Finset.card_image_of_injOn hinjVert).symm
  let R := rightChordPositions (P.toBoundaryExteriorPath hpos)
  let f : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) → ℕ :=
    fun i ↦ (i : ℕ)
  have hinjVal : Set.InjOn f R := by
    intro i _hi j _hj hij
    exact Fin.ext hij
  have hRCard : (R.image f).card = R.card :=
    Finset.card_image_of_injOn hinjVal
  have hnot : P.exactAmbientPath.length - 1 ∉ R.image f := by
    intro h
    obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp h
    have hi' := (mem_rightChordPositions (P.toBoundaryExteriorPath hpos) i).mp hi
    dsimp [f] at hieq
    have hineq : (i : ℕ) + 1 < P.exactAmbientPath.length := by
      simpa only [LongestExteriorPath.toBoundaryExteriorPath] using hi'.1
    omega
  have hpartition :=
    lastExteriorNeighborPositions_eq_insert_rightChords P hpos
  change s = insert (P.exactAmbientPath.length - 1) (R.image f) at hpartition
  have hcards := congrArg Finset.card hpartition
  rw [Finset.card_insert_of_notMem hnot, hRCard] at hcards
  dsimp [s, R] at hsCard hcards ⊢
  omega

/-- The minimum-degree hypothesis, split at the first endpoint.  The
quantity `firstExteriorNeighbors.card - 1` removes the mandatory first path
edge and counts every remaining exterior neighbour, independently of any
later choice of chord convention. -/
theorem first_endpoint_degree_parameters {j : ℕ}
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V)) :
    2 * j ≤ P.firstCycleNeighbors.card +
      (P.firstExteriorNeighbors.card - 1) := by
  have hsplit := P.card_firstCycleNeighbors_add_card_firstExteriorNeighbors
  have hext := firstExteriorNeighbors_card_pos P hpos
  omega

/-- The same exact degree parameter bound at the last endpoint. -/
theorem last_endpoint_degree_parameters {j : ℕ}
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.last : V)) :
    2 * j ≤ P.lastCycleNeighbors.card +
      (P.lastExteriorNeighbors.card - 1) := by
  have hsplit := P.card_lastCycleNeighbors_add_card_lastExteriorNeighbors
  have hext := lastExteriorNeighbors_card_pos P hpos
  omega

/-- The last-endpoint degree split in the exact boundary-module
representation.  Unlike the endpoint count, this is a statement about the
right endpoint and is logically independent of its left-chord parameter. -/
theorem last_endpoint_boundary_degree_parameters {j : ℕ}
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.last : V)) :
    2 * j ≤
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.last : V)).card +
      (rightChordPositions (P.toBoundaryExteriorPath hpos)).card := by
  rw [card_boundaryCycleNeighborPositions_last,
    rightChordPositions_card_eq_lastExterior_card_sub_one]
  exact last_endpoint_degree_parameters P hpos hdegree

/-- In the one-left-chord exceptional case, the last-endpoint degree bound
and the common `2*j-1` cycle-neighbour count force at least one right chord.
No claim is made that this right chord is unique. -/
theorem rightChordPositions_nonempty_of_degree_and_cycle_card
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.last : V))
    (hcycle :
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.last : V)).card = 2 * j - 1) :
    (rightChordPositions (P.toBoundaryExteriorPath hpos)).Nonempty := by
  have hbound := last_endpoint_boundary_degree_parameters P hpos hdegree
  rw [hcycle] at hbound
  apply Finset.card_pos.mp
  omega

/-! ## The final endpoint arithmetic split -/

/-- This orientation places every cycle neighbour of the first endpoint
among the selected positions before `bPos`. -/
def CyclicOrientation.CoversAllFirstCycleNeighbors
    {P : LongestExteriorPath C} (D : CyclicOrientation P) : Prop :=
  selectedCycleNeighborPositions P D.bPos =
    EndpointApplication.cycleNeighborPositions C.walk (P.first : V)

lemma CyclicOrientation.attachmentCount_eq_firstCycle_card
    {P : LongestExteriorPath C} (D : CyclicOrientation P)
    (hcover : D.CoversAllFirstCycleNeighbors) :
    D.attachmentCount = P.firstCycleNeighbors.card := by
  change (selectedCycleNeighborPositions P D.bPos).card =
    P.firstCycleNeighbors.card
  rw [hcover, card_cycleNeighborPositions_first P]

/-- In the equal-neighbour application, `bPos` is the reserved common
attachment and all other first-endpoint cycle neighbours are selected.  The
cardinality equation is the exact part of that orientation used by the
arithmetic endgame. -/
def CyclicOrientation.ReservesOneFirstCycleNeighbor
    {P : LongestExteriorPath C} (D : CyclicOrientation P) : Prop :=
  D.attachmentCount + 1 = P.firstCycleNeighbors.card

/-- Unequal-neighbour arithmetic endgame from the actual longest path.

The conclusion is the unique numerical boundary case.  Notice that the
degree inequality and the endpoint lower bound are proved internally; the
only geometric side condition is coverage of the first endpoint's cycle
neighbours. -/
theorem unequal_endpoint_boundary_of_longestExteriorPath [Finite V]
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (D : CyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hcover : D.CoversAllFirstCycleNeighbors) :
    D.chordCount = 0 ∧ D.attachmentCount = 2 * j := by
  have hp := D.attachmentCount_eq_firstCycle_card hcover
  have hq := chordCount_eq_firstExterior_card_sub_one P D hpos
  have hparameters := first_endpoint_degree_parameters P hpos hdegree
  have hdegree' : 2 * j ≤ D.attachmentCount + D.chordCount := by
    simpa [hp, hq] using hparameters
  have hcount := D.endpoint_count_of_longestExteriorPath hpos hattach
  exact AlternativeSharp.unequal_endpoint_exception hj hattach hdegree'
    (hcount.trans hodd)

/-- Equal-neighbour arithmetic endgame from the actual longest path after
reserving one common cycle attachment for the last endpoint.  These are
exactly Gyárfás's three remaining numerical boundary configurations. -/
theorem equal_endpoint_boundaries_of_longestExteriorPath [Finite V]
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (D : CyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hreserve : D.ReservesOneFirstCycleNeighbor) :
    (D.chordCount = 1 ∧ P.firstCycleNeighbors.card = 2 * j - 1) ∨
      (D.chordCount = 0 ∧
        (P.firstCycleNeighbors.card = 2 * j ∨
          P.firstCycleNeighbors.card = 2 * j + 1)) := by
  have hq := chordCount_eq_firstExterior_card_sub_one P D hpos
  have hparameters := first_endpoint_degree_parameters P hpos hdegree
  have hdegree' :
      2 * j ≤ P.firstCycleNeighbors.card + D.chordCount := by
    simpa [hq] using hparameters
  have hcount := D.endpoint_count_of_longestExteriorPath hpos hattach
  have hsub : P.firstCycleNeighbors.card - 1 = D.attachmentCount := by
    unfold CyclicOrientation.ReservesOneFirstCycleNeighbor at hreserve
    omega
  have hcount' :
      Arithmetic.ceilHalf (P.firstCycleNeighbors.card - 1) + D.chordCount ≤ j := by
    simpa [EndpointCount.ceilHalf, Arithmetic.ceilHalf, hsub] using
      hcount.trans hodd
  have hp : 0 < P.firstCycleNeighbors.card := by
    unfold CyclicOrientation.ReservesOneFirstCycleNeighbor at hreserve
    omega
  exact AlternativeSharp.equal_endpoint_exception hj hp hdegree' hcount'

/-- Unequal-neighbour arithmetic using the cycle rotated at the actual
extra last-endpoint attachment. -/
theorem rotated_unequal_endpoint_boundary_of_longestExteriorPath [Finite V]
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (D : RotatedCyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hp : D.attachmentCount = P.firstCycleNeighbors.card) :
    D.chordCount = 0 ∧ D.attachmentCount = 2 * j := by
  have hq := D.chordCount_eq_firstExterior_card_sub_one hpos
  have hparameters := first_endpoint_degree_parameters P hpos hdegree
  have hdegree' : 2 * j ≤ D.attachmentCount + D.chordCount := by
    simpa [hp, hq] using hparameters
  have hcount := D.endpoint_count hpos hattach
  exact AlternativeSharp.unequal_endpoint_exception hj hattach hdegree'
    (hcount.trans hodd)

/-- Equal-neighbour arithmetic using the cycle rotated at the reserved
common attachment. -/
theorem rotated_equal_endpoint_boundaries_of_longestExteriorPath [Finite V]
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (D : RotatedCyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hreserve : D.attachmentCount + 1 = P.firstCycleNeighbors.card) :
    (D.chordCount = 1 ∧ P.firstCycleNeighbors.card = 2 * j - 1) ∨
      (D.chordCount = 0 ∧
        (P.firstCycleNeighbors.card = 2 * j ∨
          P.firstCycleNeighbors.card = 2 * j + 1)) := by
  have hq := D.chordCount_eq_firstExterior_card_sub_one hpos
  have hparameters := first_endpoint_degree_parameters P hpos hdegree
  have hdegree' :
      2 * j ≤ P.firstCycleNeighbors.card + D.chordCount := by
    simpa [hq] using hparameters
  have hcount := D.endpoint_count hpos hattach
  have hsub : P.firstCycleNeighbors.card - 1 = D.attachmentCount := by omega
  have hcount' :
      Arithmetic.ceilHalf (P.firstCycleNeighbors.card - 1) +
          D.chordCount ≤ j := by
    simpa [EndpointCount.ceilHalf, Arithmetic.ceilHalf, hsub] using
      hcount.trans hodd
  have hp : 0 < P.firstCycleNeighbors.card := by omega
  exact AlternativeSharp.equal_endpoint_exception hj hp hdegree' hcount'

/-! ## Faithful boundary-configuration assembly -/

/-- Assemble the one-left-chord boundary object.  The required right chord
is derived from the *last* endpoint degree split; it is not inferred from
the left endpoint's parameter `q`. -/
noncomputable def oneChordEachConfiguration_of_longestExteriorPath
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegreeLast : 2 * j + 1 ≤ G.degree (P.last : V))
    (D : CyclicOrientation P) (hq : D.chordCount = 1)
    (hsame :
      Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V) =
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V))
    (hcycle :
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).card = 2 * j - 1) :
    OneChordEachConfiguration (toEndpointLongestOddCycle C) j := by
  have hcycleLast :
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.last : V)).card = 2 * j - 1 := by
    rw [← hsame]
    exact hcycle
  exact
    { exterior := P.toBoundaryExteriorPath hpos
      same_neighbors := hsame
      cycle_neighbor_card := hcycle
      left_chord_card := by
        rw [leftChordPositions_card_eq_chordCount P D hpos, hq]
      right_chord_nonempty :=
        rightChordPositions_nonempty_of_degree_and_cycle_card
          hj P hpos hdegreeLast hcycleLast }

/-- Assemble the equal-neighbour no-left-chord boundary object.  Right
chords are deliberately unrestricted. -/
noncomputable def sameNeighborhoodNoChordConfiguration_of_longestExteriorPath
    {j : ℕ} (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (D : CyclicOrientation P) (hq : D.chordCount = 0)
    (hsame :
      Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V) =
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V))
    (hmany : 2 * j ≤
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).card) :
    SameNeighborhoodNoChordConfiguration (toEndpointLongestOddCycle C) j :=
  { exterior := P.toBoundaryExteriorPath hpos
    no_left_chord :=
      leftChordPositions_eq_empty_of_chordCount_eq_zero P D hpos hq
    same_neighbors := hsame
    many_neighbors := hmany }

/-- Assemble the different-neighbour no-left-chord boundary object from the
actual source orientation.  Again no condition is imposed on right chords. -/
noncomputable def differentNeighborhoodNoChordConfiguration_of_longestExteriorPath
    {j : ℕ} (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (D : CyclicOrientation P) (hq : D.chordCount = 0)
    (hmany : 2 * j ≤
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).card)
    (hcard :
      (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).card ≤
        (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V)).card)
    (hextra :
      (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V) \
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).Nonempty) :
    DifferentNeighborhoodNoChordConfiguration
      (toEndpointLongestOddCycle C) j :=
  { exterior := P.toBoundaryExteriorPath hpos
    no_left_chord :=
      leftChordPositions_eq_empty_of_chordCount_eq_zero P D hpos hq
    many_left_neighbors := hmany
    left_card_le_right_card := hcard
    extra_right_neighbor := hextra }

/-- The equal-neighbour numerical alternatives assemble directly into the
two faithful boundary configurations. -/
theorem equal_boundary_configuration_of_longestExteriorPath [Finite V]
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegreeFirst : 2 * j + 1 ≤ G.degree (P.first : V))
    (hdegreeLast : 2 * j + 1 ≤ G.degree (P.last : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (D : CyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hreserve : D.ReservesOneFirstCycleNeighbor)
    (hsame :
      Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V) =
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V)) :
    Nonempty (OneChordEachConfiguration (toEndpointLongestOddCycle C) j) ∨
      Nonempty (SameNeighborhoodNoChordConfiguration
        (toEndpointLongestOddCycle C) j) := by
  have hsplit := equal_endpoint_boundaries_of_longestExteriorPath
    hj P hpos hdegreeFirst hodd D hattach hreserve
  have hcard := card_boundaryCycleNeighborPositions_first P
  rcases hsplit with ⟨hq, hp⟩ | ⟨hq, hp⟩
  · left
    exact ⟨oneChordEachConfiguration_of_longestExteriorPath
      hj P hpos hdegreeLast D hq hsame (by omega)⟩
  · right
    exact ⟨sameNeighborhoodNoChordConfiguration_of_longestExteriorPath
      P hpos D hq hsame (by omega)⟩

/-- The different-neighbour numerical alternative assembles into its
faithful no-left-chord boundary object. -/
noncomputable def different_boundary_configuration_of_longestExteriorPath [Finite V]
    {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (D : CyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hcover : D.CoversAllFirstCycleNeighbors)
    (hcard :
      (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).card ≤
        (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V)).card)
    (hextra :
      (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V) \
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).Nonempty) :
    DifferentNeighborhoodNoChordConfiguration
      (toEndpointLongestOddCycle C) j := by
  have hsplit := unequal_endpoint_boundary_of_longestExteriorPath
    hj P hpos hdegree hodd D hattach hcover
  have hp := D.attachmentCount_eq_firstCycle_card hcover
  have hcycle := card_boundaryCycleNeighborPositions_first P
  apply differentNeighborhoodNoChordConfiguration_of_longestExteriorPath
    P hpos D hsplit.1
  · omega
  · exact hcard
  · exact hextra

/-- Direct different-neighbour dispatch with the cycle rotation constructed
from the actual extra last-endpoint attachment.  No orientation object is an
input. -/
noncomputable def rotated_different_boundary_configuration_of_longestExteriorPath
    [Finite V] {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegree : 2 * j + 1 ≤ G.degree (P.first : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (hfirst : 0 < P.firstCycleNeighbors.card)
    (hcard :
      (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).card ≤
        (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V)).card)
    (hextra :
      (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V) \
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).Nonempty) :
    DifferentNeighborhoodNoChordConfiguration
      (toEndpointLongestOddCycle C) j := by
  let E := rotatedOrientation_of_extraRightNeighbor (P := P) hextra
  let D := E.1
  have hp : D.attachmentCount = P.firstCycleNeighbors.card := E.2
  have hattach : 0 < D.attachmentCount := by omega
  have hsplit := rotated_unequal_endpoint_boundary_of_longestExteriorPath
    hj P hpos hdegree hodd D hattach hp
  have hcycle := card_boundaryCycleNeighborPositions_first P
  exact
    { exterior := P.toBoundaryExteriorPath hpos
      no_left_chord :=
        D.leftChordPositions_eq_empty_of_chordCount_eq_zero hpos hsplit.1
      many_left_neighbors := by
        change 2 * j ≤ (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).card
        rw [card_boundaryCycleNeighborPositions_first]
        omega
      left_card_le_right_card := hcard
      extra_right_neighbor := hextra }

/-- Direct equal-neighbour dispatch with the cycle rotation constructed at
an actual common attachment.  The lower bound two guarantees that, after
reserving the base occurrence, the endpoint count still has a positive
attachment family. -/
theorem rotated_equal_boundary_configuration_of_longestExteriorPath
    [Finite V] {j : ℕ} (hj : 0 < j) (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length)
    (hdegreeFirst : 2 * j + 1 ≤ G.degree (P.first : V))
    (hdegreeLast : 2 * j + 1 ≤ G.degree (P.last : V))
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (hsame :
      Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V) =
        Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V))
    (htwo : 2 ≤
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).card) :
    Nonempty (OneChordEachConfiguration (toEndpointLongestOddCycle C) j) ∨
      Nonempty (SameNeighborhoodNoChordConfiguration
        (toEndpointLongestOddCycle C) j) := by
  have hnonempty :
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).Nonempty :=
    Finset.card_pos.mp (by omega)
  let E := rotatedOrientation_of_commonNeighbor (P := P) hsame hnonempty
  let D := E.1
  have hreserve : D.attachmentCount + 1 = P.firstCycleNeighbors.card := E.2
  have hcardFirst := card_boundaryCycleNeighborPositions_first P
  have hattach : 0 < D.attachmentCount := by omega
  have hsplit := rotated_equal_endpoint_boundaries_of_longestExteriorPath
    hj P hpos hdegreeFirst hodd D hattach hreserve
  rcases hsplit with ⟨hq, hp⟩ | ⟨hq, hp⟩
  · left
    have hcycle :
        (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).card = 2 * j - 1 := by
      omega
    have hcycleLast :
        (Structural.cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.last : V)).card = 2 * j - 1 := by
      rw [← hsame]
      exact hcycle
    exact ⟨
      { exterior := P.toBoundaryExteriorPath hpos
        same_neighbors := hsame
        cycle_neighbor_card := hcycle
        left_chord_card := by
          rw [D.leftChordPositions_card_eq_chordCount hpos, hq]
        right_chord_nonempty :=
          rightChordPositions_nonempty_of_degree_and_cycle_card
            hj P hpos hdegreeLast hcycleLast }⟩
  · right
    exact ⟨
      { exterior := P.toBoundaryExteriorPath hpos
        no_left_chord :=
          D.leftChordPositions_eq_empty_of_chordCount_eq_zero hpos hq
        same_neighbors := hsame
        many_neighbors := by
          change 2 * j ≤ (Structural.cycleNeighborPositions
            (toEndpointLongestOddCycle C) (P.first : V)).card
          rw [card_boundaryCycleNeighborPositions_first]
          omega }⟩

/-! ## Checked boundary case already available from the actual geometry -/

/-- Transport the concrete `j = 1` equal-neighbour boundary theorem from
`ExteriorPath` to the selected longest exterior path. -/
theorem sameNeighborhoodBoundary_one_of_longestExteriorPath [Finite V]
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hsame :
      Structural.cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V) =
        Structural.cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V))
    (htwo :
      (Structural.cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).card = 2) :
    2 ≤ (oddCycleLengths G).ncard := by
  let S := P.toBoundaryExteriorPath hpos
  let D : SameNeighborhoodTwoConfiguration (toEndpointLongestOddCycle C) := {
    exterior := S
    same_neighbors := hsame
    two_neighbors := htwo
  }
  exact sameNeighborhoodBoundary_one_of_exteriorPath
    (toEndpointLongestOddCycle C) D

end CaseAssembly

end

end Erdos58.Structural
