/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.TripleCover
import ErdosProblems.Erdos518.HighMu
import ErdosProblems.Erdos518.BasicBounds
import ErdosProblems.Erdos518.MuBound

/-!
# No blue-triple edge contains all high vertices

This file proves Claim 3 in the high-degree branch of the Chen--Chen proof.  If an edge of
the ordered-blue-triple hypergraph contained every high vertex, then it would contain a
maximum-blue-degree vertex `s`.  Outside that edge every vertex has blue degree at most half
of `r`.  The key equality and the parity consequence of the blue-triple cover leave at least
`r - blueDegreeToX s` outside vertices.  Sharp endpoint and consecutive-common-neighbour
counts in `extensionReservoir s` then build the alternating lists forbidden by Lemma 3.4.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance noEdgeAllHighDecidableEq : DecidableEq V := Classical.decEq V
noncomputable local instance noEdgeAllHighDecidableAdj : DecidableRel C.G.Adj := Classical.decRel _
noncomputable local instance noEdgeAllHighDecidableComplAdj : DecidableRel C.Gᶜ.Adj :=
  Classical.decRel _

/-- The size of the extension reservoir, in the form used in Claim 3. -/
lemma extensionReservoir_card_identity {s : V} (hs : s ∈ C.Y) :
    (C.extensionReservoir s).card + C.blueDegreeToX s + 1 + C.w =
      C.c ^ 2 + C.r := by
  classical
  have hSsub : C.extensionPredecessorSet s ⊆ C.X :=
    C.extensionPredecessorSet_subset_X s
  have hScard : (C.extensionPredecessorSet s).card = C.blueDegreeToX s + 1 :=
    C.extensionPredecessorSet_card hs
  have hsplit :
      (C.extensionReservoir s).card + (C.extensionPredecessorSet s).card = C.X.card := by
    rw [extensionReservoir, Finset.card_sdiff_of_subset hSsub]
    exact Nat.sub_add_cancel (Finset.card_le_card hSsub)
  have hXsum : C.X.card + C.w = C.c ^ 2 + C.r := by
    rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
  omega

/-- Inside an extension reservoir, at most the total blue degree of an outside vertex is
missing from its red-neighbour set. -/
lemma extensionReservoir_card_le_redNeighbors_add_blueDegree_claimThree
    {s y : V} (hy : y ∈ C.Y) :
    (C.extensionReservoir s).card ≤
      (C.extensionRedNeighbors s y).card + C.blueDegreeToX y := by
  classical
  let B := (C.extensionReservoir s).filter fun x ↦ C.Gᶜ.Adj y x
  have hyX : y ∉ C.X := C.mem_Y.mp hy
  have hUnion : C.extensionRedNeighbors s y ∪ B = C.extensionReservoir s := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (C.mem_extensionRedNeighbors.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      by_cases hred : C.G.Adj y x
      · exact Finset.mem_union_left _ (C.mem_extensionRedNeighbors.mpr ⟨hx, hred⟩)
      · apply Finset.mem_union_right
        refine Finset.mem_filter.mpr ⟨hx, (SimpleGraph.compl_adj C.G y x).2 ⟨?_, hred⟩⟩
        intro hyx
        subst x
        exact hyX (C.extensionReservoir_subset_X s hx)
  have hDisjoint : Disjoint (C.extensionRedNeighbors s y) B := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    have hred := (C.mem_extensionRedNeighbors.mp hxR).2
    have hblue := (Finset.mem_filter.mp hxB).2
    exact ((SimpleGraph.compl_adj C.G y x).mp hblue).2 hred
  have hBsub : B ⊆ C.X.filter fun x ↦ C.Gᶜ.Adj y x := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨C.extensionReservoir_subset_X s (Finset.mem_filter.mp hx).1,
        (Finset.mem_filter.mp hx).2⟩
  have hcard := Finset.card_union_of_disjoint hDisjoint
  rw [hUnion] at hcard
  have hBle : B.card ≤ C.blueDegreeToX y := by
    simpa [blueDegreeToX] using Finset.card_le_card hBsub
  omega

/-- Two red-neighbour sets in one extension reservoir miss at most the sum of the two total
blue degrees. -/
lemma extensionReservoir_card_le_commonRed_add_blueDegrees_claimThree
    {s y z : V} (hy : y ∈ C.Y) (hz : z ∈ C.Y) :
    (C.extensionReservoir s).card ≤
      (C.extensionRedNeighbors s y ∩ C.extensionRedNeighbors s z).card +
        C.blueDegreeToX y + C.blueDegreeToX z := by
  classical
  have hyBound :=
    C.extensionReservoir_card_le_redNeighbors_add_blueDegree_claimThree (s := s) hy
  have hzBound :=
    C.extensionReservoir_card_le_redNeighbors_add_blueDegree_claimThree (s := s) hz
  have hUnionSub :
      C.extensionRedNeighbors s y ∪ C.extensionRedNeighbors s z ⊆
        C.extensionReservoir s := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (C.mem_extensionRedNeighbors.mp hx).1
    · exact (C.mem_extensionRedNeighbors.mp hx).1
  have hUnionCard := Finset.card_le_card hUnionSub
  have hIE := Finset.card_inter_add_card_union
    (C.extensionRedNeighbors s y) (C.extensionRedNeighbors s z)
  omega

/-- **Chen--Chen Claim 3.**  Under the key equality in the high-degree branch, no edge of
the concrete ordered-blue-triple hypergraph contains every high vertex.  Its conclusion is
exactly the last input of `highMu_structural_reduction`. -/
theorem no_blueTripleHyperedge_contains_all_high
    (hc : 4 ≤ C.c)
    (hkey : C.a0 + ceilHalf C.a1 = C.c)
    (hHighMu : C.r + 1 ≤ 2 * C.mu) :
    ∀ T ∈ C.blueTripleHypergraph,
      ¬ highVertices C.Y1 C.blueDegreeToX C.r ⊆ T := by
  classical
  intro T hT hAllHigh

  have hY0 : C.Y0.Nonempty := C.Y0_nonempty
  have hdegBound : C.mu + 2 ≤ C.r := by
    apply C.mu_add_two_le_r_of_bounds C.Y1_nonempty hY0 (by omega)
    have := C.w_le_r_sub_two
    have := C.w_ge_c
    omega
  obtain ⟨s, hsY1, hsDegree⟩ :=
    C.exists_mem_Y1_blueDegreeToX_eq_mu C.Y1_nonempty
  have hsHigh : s ∈ highVertices C.Y1 C.blueDegreeToX C.r := by
    apply mem_highVertices.mpr
    exact ⟨hsY1, by simpa [hsDegree] using hHighMu⟩
  have hsT : s ∈ T := hAllHigh hsHigh
  have hsY : s ∈ C.Y := C.Y1_subset_Y hsY1
  have hsDegLt : C.blueDegreeToX s < C.r := by omega

  have hTsubY1 : T ⊆ C.Y1 := (C.blueTripleHypergraph_threeUniform hT).1
  have hTcard : T.card = 3 := (C.blueTripleHypergraph_threeUniform hT).2
  have hTsubY : T ⊆ C.Y := hTsubY1.trans C.Y1_subset_Y
  have ha1ge : 3 ≤ C.a1 := by
    rw [C.a1_eq_card_Y1, ← hTcard]
    exact Finset.card_le_card hTsubY1
  have ha1Even : Even C.a1 := by
    rcases Nat.even_or_odd C.a1 with heven | hodd
    · exact heven
    · have hempty := C.blueTripleHypergraph_eq_empty_of_odd hkey hodd
      rw [hempty] at hT
      simp at hT
  have hceil : 2 * ceilHalf C.a1 = C.a1 :=
    two_mul_ceilHalf_of_even ha1Even
  have hwLarge : C.c + 2 ≤ C.w := by
    have hw := C.w_eq_a0_add_a1
    omega

  let outside : Finset V := C.Y \ T
  have houtsideCard : outside.card = C.w - 3 := by
    dsimp only [outside]
    rw [Finset.card_sdiff_of_subset hTsubY, ← C.w_eq_card_Y, hTcard]
  let a : ℕ := C.extensionCount s
  have haDef : a = C.r - C.blueDegreeToX s := rfl
  have haPos : 0 < a := by
    dsimp only [a, extensionCount]
    omega
  have haSum : a + C.blueDegreeToX s = C.r := by
    dsimp only [a, extensionCount]
    omega
  have haLe : a ≤ C.c - 1 := by
    rw [haDef, hsDegree]
    exact highMu_deficit_le_pred C.r_le_two_mul_c hHighMu
  have haOutside : a ≤ outside.card := by
    rw [houtsideCard]
    omega

  have hnotHigh : ∀ y ∈ outside, 2 * C.blueDegreeToX y ≤ C.r := by
    intro y hyOutside
    have hyData : y ∈ C.Y ∧ y ∉ T := Finset.mem_sdiff.mp hyOutside
    by_contra hnot
    have hhigh : C.r + 1 ≤ 2 * C.blueDegreeToX y := by omega
    have hdegreeNe : C.blueDegreeToX y ≠ 0 := by
      have hrPos : 0 < C.r := by
        have := C.w_ge_c
        have := C.w_le_r_sub_two
        omega
      omega
    have hyY1 : y ∈ C.Y1 := C.mem_Y1.mpr ⟨hyData.1, hdegreeNe⟩
    have hyHigh : y ∈ highVertices C.Y1 C.blueDegreeToX C.r :=
      mem_highVertices.mpr ⟨hyY1, hhigh⟩
    exact hyData.2 (hAllHigh hyHigh)

  have hfourSquare : 4 * C.c ≤ C.c ^ 2 := by
    calc
      4 * C.c = C.c * 4 := by omega
      _ ≤ C.c * C.c := Nat.mul_le_mul_left C.c hc
      _ = C.c ^ 2 := by simp [pow_two]
  have hWcard := C.extensionReservoir_card_identity hsY

  have hendpointCard : ∀ y ∈ outside,
      a ≤ (C.extensionRedNeighbors s y).card := by
    intro y hyOutside
    have hyY : y ∈ C.Y := (Finset.mem_sdiff.mp hyOutside).1
    have hyLow := hnotHigh y hyOutside
    have hyDegreeC : C.blueDegreeToX y ≤ C.c := by
      have hr := C.r_le_two_mul_c
      omega
    have hbase :=
      C.extensionReservoir_card_le_redNeighbors_add_blueDegree_claimThree
        (s := s) hyY
    have hw := C.w_le_r_sub_two
    have hr := C.r_le_two_mul_c
    omega

  have hcommonCard : ∀ y ∈ outside, ∀ z ∈ outside,
      a - 1 ≤
        (C.extensionRedNeighbors s y ∩ C.extensionRedNeighbors s z).card := by
    intro y hyOutside z hzOutside
    have hyY : y ∈ C.Y := (Finset.mem_sdiff.mp hyOutside).1
    have hzY : z ∈ C.Y := (Finset.mem_sdiff.mp hzOutside).1
    have hyLow := hnotHigh y hyOutside
    have hzLow := hnotHigh z hzOutside
    have hsumDegree : C.blueDegreeToX y + C.blueDegreeToX z ≤ C.r := by omega
    have hbase :=
      C.extensionReservoir_card_le_commonRed_add_blueDegrees_claimThree
        (s := s) hyY hzY
    have hw := C.w_le_r_sub_two
    have hr := C.r_le_two_mul_c
    omega

  let ys : List V := outside.toList.take a
  have hysLen : ys.length = a := by
    simp only [ys, List.length_take, Finset.length_toList]
    omega
  have hys0 : ys ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hysN : ys.Nodup := (Finset.nodup_toList outside).take
  have hysOutside : ∀ y ∈ ys, y ∈ outside := by
    intro y hy
    exact Finset.mem_toList.mp (List.mem_of_mem_take hy)
  have hysY : ∀ y ∈ ys, y ∈ C.Y := by
    intro y hy
    exact (Finset.mem_sdiff.mp (hysOutside y hy)).1
  have hcommonAux : ∀ ls : List V, (∀ y ∈ ls, y ∈ outside) →
      ∀ D ∈ sequentialCommonCandidates (C.extensionRedNeighbors s) ls,
        a - 1 ≤ D.card := by
    intro ls
    induction ls with
    | nil => simp
    | cons y tail ih =>
        intro hmem
        cases tail with
        | nil => simp
        | cons z tail =>
            intro D hD
            simp only [sequentialCommonCandidates_cons_cons, List.mem_cons] at hD
            rcases hD with rfl | hD
            · exact hcommonCard y (hmem y (by simp)) z (hmem z (by simp))
            · exact ih (fun q hq ↦ hmem q (by simp [hq])) D hD
  have hcommon : ∀ D ∈ sequentialCommonCandidates (C.extensionRedNeighbors s) ys,
      (sequentialCommonCandidates (C.extensionRedNeighbors s) ys).length ≤ D.card := by
    intro D hD
    rw [length_sequentialCommonCandidates, hysLen]
    exact hcommonAux ys hysOutside D hD

  let last := ys.getLast hys0
  have hlastMem : last ∈ ys := List.getLast_mem hys0
  have hlastOutside : last ∈ outside := hysOutside last hlastMem
  have hendpoint :
      (sequentialCommonCandidates (C.extensionRedNeighbors s) ys).length + 1 ≤
        (C.extensionRedNeighbors s last).card := by
    rw [length_sequentialCommonCandidates, hysLen]
    have := hendpointCard last hlastOutside
    omega
  obtain ⟨xs0, z, hxsN, hrep, hz⟩ :=
    exists_nodup_sequential_common_and_endpoint
      (C.extensionRedNeighbors s) ys (C.extensionRedNeighbors s last)
      hcommon hendpoint
  have hlastOption : ys.getLast? = some last :=
    List.getLast?_eq_some_getLast hys0
  have hzOption :
      ys.getLast?.elim False (fun y ↦ z ∈ C.extensionRedNeighbors s y) := by
    simpa only [hlastOption, Option.elim_some] using hz
  let xs := xs0 ++ [z]
  have hrels := representativeList_sequential_relations
    (C.extensionRedNeighbors s)
    (fun y x ↦ x ∈ C.extensionReservoir s ∧ C.G.Adj y x)
    (fun y x ↦ C.mem_extensionRedNeighbors (s := s) (y := y) (x := x)) hrep hzOption
  have hxsLen : xs.length = C.extensionCount s := by
    have hrepLen := hrep.length_eq
    simp only [xs, List.length_append, List.length_singleton,
      length_sequentialCommonCandidates] at hrepLen ⊢
    rw [hysLen] at hrepLen
    dsimp only [a] at hysLen ⊢
    omega
  have hxsW : ∀ x ∈ xs, x ∈ C.extensionReservoir s := by
    intro x hx
    have hright : ∀ {as bs : List V},
        List.Forall₂ (fun _ q ↦ q ∈ C.extensionReservoir s) as bs →
          ∀ q ∈ bs, q ∈ C.extensionReservoir s := by
      intro as bs hab
      induction hab with
      | nil => simp
      | cons hp _ ih =>
          intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact hp
          · exact ih q hq
    exact hright (hrels.1.imp fun _ _ h ↦ h.1) x hx
  have hyx : List.Forall₂ C.G.Adj ys xs :=
    hrels.1.imp fun _ _ h ↦ h.2
  have hxy : List.Forall₂ C.G.Adj xs.dropLast ys.tail := by
    simpa [xs] using (hrels.2.imp fun _ _ h ↦ h.2.symm)
  apply C.clique_extension_obstruction_list hsY1 hsDegLt
      (ys := ys) (xs := xs)
  · simpa [a] using hysLen
  · exact hxsLen
  · exact hysN
  · exact hxsN
  · exact hysY
  · exact hxsW
  · exact hyx
  · exact hxy

end Configuration
end Erdos518
