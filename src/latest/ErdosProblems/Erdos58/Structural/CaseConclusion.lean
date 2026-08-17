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
import ErdosProblems.Erdos58.Structural.CaseAssembly
import ErdosProblems.Erdos58.Structural.FanLinkage
import ErdosProblems.Erdos58.Structural.K1Boundary
import ErdosProblems.Erdos58.Structural.SingletonFan

/-!
# Closing the checked endpoint boundary cases

These are the short final contradictions after `CaseAssembly` has converted
the endpoint-count arithmetic into actual boundary configurations.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural.CaseConclusion

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Erdos58.LongestOddCycle G}

open CaseAssembly

lemma rotated_chordCount_eq_firstExterior_card_sub_one
    (P : LongestExteriorPath C) (D : RotatedCyclicOrientation P)
    (hpos : 0 < P.path.length) :
    D.chordCount = P.firstExteriorNeighbors.card - 1 := by
  classical
  let s := firstExteriorNeighborPositions P
  have hinj : Set.InjOn (fun n : ℕ ↦ P.exactAmbientPath.getVert n) s := by
    intro i hi k hk hik
    have hi' := (mem_firstExteriorNeighborPositions_iff P i).mp hi
    have hk' := (mem_firstExteriorNeighborPositions_iff P k).mp hk
    exact P.exactAmbientPath_isPath.getVert_injOn hi'.2.1 hk'.2.1 hik
  have hsCard : s.card = P.firstExteriorNeighbors.card := by
    rw [← image_firstExteriorNeighborPositions P]
    exact (Finset.card_image_of_injOn hinj).symm
  have hpartition := firstExteriorNeighborPositions_eq_insert_interior P hpos
  have hone : 1 ∉ EndpointApplication.interiorChordPositions P.exactAmbientPath := by
    exact fun h ↦ (EndpointApplication.mem_interiorChordPositions_iff.mp h).1.ne rfl
  change (EndpointApplication.interiorChordPositions P.exactAmbientPath).card =
    P.firstExteriorNeighbors.card - 1
  have hcards := congrArg Finset.card hpartition
  rw [Finset.card_insert_of_notMem hone] at hcards
  dsimp [s] at hsCard
  omega

lemma leftChordPositions_card_eq_rotated_chordCount
    (P : LongestExteriorPath C) (D : RotatedCyclicOrientation P)
    (hpos : 0 < P.path.length) :
    (leftChordPositions (P.toBoundaryExteriorPath hpos)).card = D.chordCount := by
  classical
  have hinj : Set.InjOn
      (fun i : Fin ((P.toBoundaryExteriorPath hpos).walk.length + 1) ↦ (i : ℕ))
      (leftChordPositions (P.toBoundaryExteriorPath hpos)) := by
    intro i _hi k _hk hik
    exact Fin.ext hik
  have hcard := Finset.card_image_of_injOn hinj
  rw [image_leftChordPositions_val P hpos] at hcard
  exact hcard.symm

/-- The different-neighborhood orientation is impossible under the exact
`j`-length hypothesis. -/
theorem different_orientation_impossible
    (hG : TwoConnected G) {j : ℕ} (hj : 0 < j)
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j)
    (D : CyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hcover : D.CoversAllFirstCycleNeighbors)
    (hcard :
      (cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V)).card ≤
        (cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V)).card)
    (hextra :
      (cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V) \
        cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V)).Nonempty) :
    False := by
  let K := different_boundary_configuration_of_longestExteriorPath
    hj P hpos (hdegree (P.first : V)) hodd.le D hattach hcover hcard hextra
  have hmany := differentNeighborhoodNoChordBoundary
    (toEndpointLongestOddCycle C) hj K
  omega

/-- Rotated, duplicated-terminal form of the different-neighborhood
contradiction. -/
theorem rotated_different_orientation_impossible
    {j : ℕ} (hj : 0 < j)
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j)
    (D : RotatedCyclicOrientation P)
    (hp : D.attachmentCount = P.firstCycleNeighbors.card)
    (hattach : 0 < D.attachmentCount)
    (hcard :
      (cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V)).card ≤
        (cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V)).card)
    (hextra :
      (cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V) \
        cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V)).Nonempty) :
    False := by
  have hq := rotated_chordCount_eq_firstExterior_card_sub_one P D hpos
  have hparameters := first_endpoint_degree_parameters P hpos
    (hdegree (P.first : V))
  have hdegree' : 2 * j ≤ D.attachmentCount + D.chordCount := by
    simpa [hp, hq] using hparameters
  have hcount := D.endpoint_count hpos hattach
  have hsplit := AlternativeSharp.unequal_endpoint_exception
    hj hattach hdegree' (hcount.trans hodd.le)
  let K : DifferentNeighborhoodNoChordConfiguration
      (toEndpointLongestOddCycle C) j :=
    { exterior := P.toBoundaryExteriorPath hpos
      no_left_chord := by
        apply Finset.card_eq_zero.mp
        rw [leftChordPositions_card_eq_rotated_chordCount P D hpos, hsplit.1]
      many_left_neighbors := by
        change 2 * j ≤
          (cycleNeighborPositions
            (toEndpointLongestOddCycle C) (P.first : V)).card
        rw [card_boundaryCycleNeighborPositions_first P]
        omega
      left_card_le_right_card := hcard
      extra_right_neighbor := hextra }
  have hmany := differentNeighborhoodNoChordBoundary
    (toEndpointLongestOddCycle C) hj K
  omega

/-- In the equal-neighborhood orientation, the no-chord alternative is
already impossible.  Consequently the only remaining output of the checked
endpoint arithmetic is the actual one-chord-at-each-end configuration. -/
theorem equal_orientation_forces_oneChord
    {j : ℕ} (hj : 0 < j)
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j)
    (D : CyclicOrientation P) (hattach : 0 < D.attachmentCount)
    (hreserve : D.ReservesOneFirstCycleNeighbor)
    (hsame :
      cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V) =
        cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V)) :
    Nonempty (OneChordEachConfiguration (toEndpointLongestOddCycle C) j) := by
  rcases equal_boundary_configuration_of_longestExteriorPath
      hj P hpos (hdegree (P.first : V)) (hdegree (P.last : V))
      hodd.le D hattach hreserve hsame with hone | hno
  · exact hone
  · obtain ⟨K⟩ := hno
    have hmany := sameNeighborhoodNoChordBoundary
      (toEndpointLongestOddCycle C) hj K
    omega

/-- Rotated, duplicated-terminal form of the equal-neighborhood endgame.
The no-chord cases contradict the checked common-neighborhood boundary
lemma, leaving the genuine one-chord-at-each-end configuration. -/
theorem rotated_equal_orientation_forces_oneChord
    {j : ℕ} (hj : 0 < j)
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j)
    (D : RotatedCyclicOrientation P)
    (hreserve : D.attachmentCount + 1 = P.firstCycleNeighbors.card)
    (hattach : 0 < D.attachmentCount)
    (hsame :
      cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V) =
        cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V)) :
    Nonempty (OneChordEachConfiguration (toEndpointLongestOddCycle C) j) := by
  have hq := rotated_chordCount_eq_firstExterior_card_sub_one P D hpos
  have hparameters := first_endpoint_degree_parameters P hpos
    (hdegree (P.first : V))
  have hdegree' :
      2 * j ≤ P.firstCycleNeighbors.card + D.chordCount := by
    simpa [hq] using hparameters
  have hcount := D.endpoint_count hpos hattach
  have hsub : P.firstCycleNeighbors.card - 1 = D.attachmentCount := by omega
  have hcount' :
      Arithmetic.ceilHalf (P.firstCycleNeighbors.card - 1) + D.chordCount ≤ j := by
    simpa [EndpointCount.ceilHalf, Arithmetic.ceilHalf, hsub] using
      hcount.trans hodd.le
  have hpPos : 0 < P.firstCycleNeighbors.card := by omega
  have hsplit := AlternativeSharp.equal_endpoint_exception
    hj hpPos hdegree' hcount'
  rcases hsplit with ⟨hqone, hp⟩ | ⟨hqzero, hp⟩
  · let K : OneChordEachConfiguration (toEndpointLongestOddCycle C) j :=
      { exterior := P.toBoundaryExteriorPath hpos
        same_neighbors := hsame
        cycle_neighbor_card := by
          change (cycleNeighborPositions
            (toEndpointLongestOddCycle C) (P.first : V)).card = 2 * j - 1
          rw [card_boundaryCycleNeighborPositions_first P]
          exact hp
        left_chord_card := by
          rw [leftChordPositions_card_eq_rotated_chordCount P D hpos, hqone]
        right_chord_nonempty := by
          apply rightChordPositions_nonempty_of_degree_and_cycle_card
            hj P hpos (hdegree (P.last : V))
          rw [← hsame, card_boundaryCycleNeighborPositions_first P]
          exact hp }
    exact ⟨K⟩
  · have hmany : 2 * j ≤
        (cycleNeighborPositions
          (toEndpointLongestOddCycle C) (P.first : V)).card := by
      rw [card_boundaryCycleNeighborPositions_first P]
      omega
    let K : SameNeighborhoodNoChordConfiguration
        (toEndpointLongestOddCycle C) j :=
      { exterior := P.toBoundaryExteriorPath hpos
        no_left_chord := by
          apply Finset.card_eq_zero.mp
          rw [leftChordPositions_card_eq_rotated_chordCount P D hpos, hqzero]
        same_neighbors := hsame
        many_neighbors := hmany }
    have hcontr := sameNeighborhoodNoChordBoundary
      (toEndpointLongestOddCycle C) hj K
    omega

private lemma sdiff_nonempty_of_ne_of_card_le {α : Type*} [DecidableEq α]
    {A B : Finset α} (hne : A ≠ B) (hcard : A.card ≤ B.card) :
    (B \ A).Nonempty := by
  rw [Finset.sdiff_nonempty]
  intro hsub
  have hBA : B = A := Finset.eq_of_subset_of_card_le hsub hcard
  exact hne hBA.symm

/-- In the common-singleton case at `j = 1`, the degree-three bound leaves
at least one genuine chord at the first endpoint of the exterior path. -/
lemma leftChordPositions_nonempty_of_singleton_degree
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : 3 ≤ G.degree (P.first : V))
    (hsingleton :
      (cycleNeighborPositions (toEndpointLongestOddCycle C)
        (P.first : V)).card = 1) :
    (leftChordPositions (P.toBoundaryExteriorPath hpos)).Nonempty := by
  classical
  have hcycle : P.firstCycleNeighbors.card = 1 := by
    rw [← card_boundaryCycleNeighborPositions_first P]
    exact hsingleton
  have hmany : 2 ≤ (firstExteriorNeighborPositions P).card := by
    simpa using two_mul_le_firstExteriorPositions_of_singleton
      (j := 1) P hdegree hcycle
  have hpartition := firstExteriorNeighborPositions_eq_insert_interior P hpos
  have hone : 1 ∉
      EndpointApplication.interiorChordPositions P.exactAmbientPath := by
    intro h
    exact (EndpointApplication.mem_interiorChordPositions_iff.mp h).1.ne rfl
  have hcard := congrArg Finset.card hpartition
  rw [Finset.card_insert_of_notMem hone] at hcard
  have hinterior :
      (EndpointApplication.interiorChordPositions P.exactAmbientPath).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨n, hn⟩ := hinterior
  rw [← image_leftChordPositions_val P hpos] at hn
  obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hn
  exact ⟨i, hi⟩

/-- Complete longest-path endpoint split, apart from the two genuinely
geometric residuals: the common singleton attachment and the checked
one-chord-at-each-end configuration.  Unequal neighborhoods and all
equal-neighborhood no-chord alternatives have already been contradicted. -/
theorem nonIndependent_reduces_to_singleton_or_oneChord
    (hG : TwoConnected G) {j : ℕ} (hj : 0 < j)
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    ((cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V) =
        cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V)) ∧
      (cycleNeighborPositions
        (toEndpointLongestOddCycle C) (P.first : V)).card = 1) ∨
      Nonempty (OneChordEachConfiguration (toEndpointLongestOddCycle C) j) := by
  let A := cycleNeighborPositions (toEndpointLongestOddCycle C) (P.first : V)
  let B := cycleNeighborPositions (toEndpointLongestOddCycle C) (P.last : V)
  have hend := endpointCycleNeighbors_nonempty hG hj P hpos hdegree hodd
  have hApos : 0 < A.card := by
    have hcard := card_boundaryCycleNeighborPositions_first P
    dsimp [A]
    rw [hcard]
    exact Finset.card_pos.mpr hend.1
  have hBpos : 0 < B.card := by
    have hcard := card_boundaryCycleNeighborPositions_last P
    dsimp [B]
    rw [hcard]
    exact Finset.card_pos.mpr hend.2
  by_cases heq : A = B
  · have hAne : A.Nonempty := Finset.card_pos.mp hApos
    let RD := rotatedOrientation_of_commonNeighbor (P := P) heq hAne
    by_cases hone : A.card = 1
    · exact Or.inl ⟨heq, hone⟩
    · right
      apply rotated_equal_orientation_forces_oneChord
        hj P hpos hdegree hodd RD.1 RD.2
      · have hfirstCard := card_boundaryCycleNeighborPositions_first P
        have htwo : 2 ≤ A.card := by omega
        dsimp [A] at htwo
        rw [hfirstCard] at htwo
        omega
      · exact heq
  · by_cases hcard : A.card ≤ B.card
    · have hextra : (B \ A).Nonempty :=
        sdiff_nonempty_of_ne_of_card_le heq hcard
      let RD := rotatedOrientation_of_extraRightNeighbor (P := P) hextra
      have hattach : 0 < RD.1.attachmentCount := by
        rw [RD.2]
        exact Finset.card_pos.mpr hend.1
      exact (rotated_different_orientation_impossible
        hj P hpos hdegree hodd RD.1 RD.2 hattach hcard hextra).elim
    · have hcard' : B.card ≤ A.card := by omega
      have hne' : B ≠ A := fun h ↦ heq h.symm
      have hextra : (A \ B).Nonempty :=
        sdiff_nonempty_of_ne_of_card_le hne' hcard'
      let Q := P.reverse
      have hextraQ :
          (cycleNeighborPositions (toEndpointLongestOddCycle C) (Q.last : V) \
            cycleNeighborPositions
              (toEndpointLongestOddCycle C) (Q.first : V)).Nonempty := by
        simpa [Q, LongestExteriorPath.reverse, A, B] using hextra
      let RD := rotatedOrientation_of_extraRightNeighbor (P := Q) hextraQ
      have hattach : 0 < RD.1.attachmentCount := by
        rw [RD.2]
        have : Q.firstCycleNeighbors.card = P.lastCycleNeighbors.card := rfl
        rw [this]
        exact Finset.card_pos.mpr hend.2
      have hcardQ :
          (cycleNeighborPositions (toEndpointLongestOddCycle C) (Q.first : V)).card ≤
            (cycleNeighborPositions
              (toEndpointLongestOddCycle C) (Q.last : V)).card := by
        simpa [Q, LongestExteriorPath.reverse, A, B] using hcard'
      exact (rotated_different_orientation_impossible
        hj Q (by simpa [Q] using hpos) hdegree hodd RD.1 RD.2
          hattach hcardQ hextraQ).elim

/-- Every positive longest exterior path contradicts the exact `j`-length
hypothesis.  The endpoint count has already reduced the proof to two cases:
the common-singleton augmented fan, and the one-chord boundary. -/
theorem nonIndependent_impossible
    (hG : TwoConnected G) {j : ℕ} (hj : 0 < j)
    (P : LongestExteriorPath C) (hpos : 0 < P.path.length)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) : False := by
  rcases nonIndependent_reduces_to_singleton_or_oneChord
      hG hj P hpos hdegree hodd with hsingleton | hboundary
  · obtain ⟨hsame, hone⟩ := hsingleton
    by_cases hjone : j = 1
    · rcases hjone with rfl
      let S := P.toBoundaryExteriorPath hpos
      have hleft : (leftChordPositions S).Nonempty := by
        exact leftChordPositions_nonempty_of_singleton_degree P hpos
          (hdegree (P.first : V)) hone
      have honeLast :
          (cycleNeighborPositions (toEndpointLongestOddCycle C)
            (P.last : V)).card = 1 := by
        rw [← hsame]
        exact hone
      have hright : (rightChordPositions S).Nonempty := by
        exact rightChordPositions_nonempty_of_degree_and_cycle_card
          (j := 1) (by omega) P hpos (hdegree (P.last : V)) honeLast
      have htwo := K1Boundary.singletonChordBoundary_one_of_twoConnected
        hG (toEndpointLongestOddCycle C) S hsame hone hleft hright
      omega
    · have hjtwo : 2 ≤ j := by omega
      exact SingletonFan.equalSingletonEndpoint_impossible
        hG hjtwo P hpos hdegree hodd hsame hone
  · obtain ⟨D⟩ := hboundary
    by_cases hjone : j = 1
    · rcases hjone with rfl
      have htwo := K1Boundary.oneChordEachBoundary_one_of_twoConnected
        hG (toEndpointLongestOddCycle C) D
      omega
    · have hjtwo : 2 ≤ j := by omega
      have hmany := oneChordEachBoundary_of_two_le
        (toEndpointLongestOddCycle C) hjtwo D
      omega

end

end Erdos58.Structural.CaseConclusion
