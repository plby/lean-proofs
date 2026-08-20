/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.HighMu
import ErdosProblems.Erdos518.ExtensionObstruction
import ErdosProblems.Erdos518.BasicBounds
import ErdosProblems.Erdos518.MuBound
import ErdosProblems.Erdos518.CaseArithmetic

/-!
# The final high-degree contradiction

This file closes the last `lambda in {2,3}` case in the Chen--Chen proof.  Starting from
`HighMuReductionData`, it puts `b = r - blueDegreeToX s` and
`W = X \ extensionPredecessorSet s`.  If `b <= a0`, the outside list is chosen in `Y0`.
Otherwise it consists of all of `Y0` and the required one or two vertices of
`Y1 \ edge`, ordered so that every consecutive pair contains a member of `Y0`.
The cardinal estimate proved in `HighMu` then supplies distinct representatives in `W`,
contradicting the clique-extension obstruction.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance highFinalDecidableEq : DecidableEq V := Classical.decEq V
noncomputable local instance highFinalDecidableAdj : DecidableRel C.G.Adj := Classical.decRel _
noncomputable local instance highFinalDecidableComplAdj : DecidableRel C.Gᶜ.Adj := Classical.decRel _

/-- Every element of `extensionRedNeighbors s y` belongs to the extension reservoir. -/
lemma extensionRedNeighbors_subset (s y : V) :
    C.extensionRedNeighbors s y ⊆ C.extensionReservoir s := by
  classical
  intro x hx
  exact (C.mem_extensionRedNeighbors.mp hx).1

/-- A member of `Y0` is red-complete to every extension reservoir. -/
lemma extensionRedNeighbors_eq_reservoir_of_mem_Y0
    {s y : V} (hy : y ∈ C.Y0) :
    C.extensionRedNeighbors s y = C.extensionReservoir s := by
  classical
  apply Finset.Subset.antisymm (C.extensionRedNeighbors_subset s y)
  intro x hx
  exact C.mem_extensionRedNeighbors.mpr
    ⟨hx, C.adj_of_mem_Y0_mem_X hy (C.extensionReservoir_subset_X s hx)⟩

/-- Inside an extension reservoir, the red-neighbour count can miss at most the total blue
degree into `X`. -/
lemma extensionReservoir_card_le_redNeighbors_add_blueDegree
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

/-- If `degree s + b <= |W|`, every outside vertex whose blue degree is at most that of `s`
has at least `b` red neighbours in `W`. -/
lemma extensionCount_le_card_extensionRedNeighbors
    {s y : V} {b : ℕ}
    (hy : y ∈ C.Y) (hdeg : C.blueDegreeToX y ≤ C.blueDegreeToX s)
    (hcap : C.blueDegreeToX s + b ≤ (C.extensionReservoir s).card) :
    b ≤ (C.extensionRedNeighbors s y).card := by
  have hbase := C.extensionReservoir_card_le_redNeighbors_add_blueDegree
    (s := s) hy
  omega

/-- The list-level condition used in the final construction: every adjacent pair contains a
vertex of `Y0`. -/
def EveryAdjacentHasY0 (C : Configuration V) : List V → Prop
  | [] => True
  | [_] => True
  | y :: y' :: ys => (y ∈ C.Y0 ∨ y' ∈ C.Y0) ∧ C.EveryAdjacentHasY0 (y' :: ys)

@[simp] lemma everyAdjacentHasY0_nil : C.EveryAdjacentHasY0 [] := trivial

@[simp] lemma everyAdjacentHasY0_singleton (y : V) :
    C.EveryAdjacentHasY0 [y] := trivial

@[simp] lemma everyAdjacentHasY0_cons_cons (y y' : V) (ys : List V) :
    C.EveryAdjacentHasY0 (y :: y' :: ys) ↔
      (y ∈ C.Y0 ∨ y' ∈ C.Y0) ∧ C.EveryAdjacentHasY0 (y' :: ys) := by
  rfl

/-- A list consisting entirely of `Y0` vertices satisfies the adjacent-pair condition. -/
lemma everyAdjacentHasY0_of_forall_mem
    {ys : List V} (hys : ∀ y ∈ ys, y ∈ C.Y0) :
    C.EveryAdjacentHasY0 ys := by
  induction ys with
  | nil => trivial
  | cons y ys ih =>
      cases ys with
      | nil => trivial
      | cons y' ys =>
          rw [C.everyAdjacentHasY0_cons_cons]
          exact ⟨Or.inl (hys y (by simp)), ih (fun z hz ↦ hys z (by simp [hz]))⟩

/-- A possibly non-`Y0` vertex followed by a list in `Y0` still satisfies the
adjacent-pair condition. -/
lemma everyAdjacentHasY0_cons_of_tail
    (y : V) {ys : List V} (hys : ∀ z ∈ ys, z ∈ C.Y0) :
    C.EveryAdjacentHasY0 (y :: ys) := by
  cases ys with
  | nil => trivial
  | cons z zs =>
      rw [C.everyAdjacentHasY0_cons_cons]
      exact ⟨Or.inr (hys z (by simp)),
        C.everyAdjacentHasY0_of_forall_mem (fun q hq ↦ hys q (by simp [hq]))⟩

/-- If each adjacent pair has a `Y0` member, every sequential common-neighbour candidate
has the same lower bound as a single outside vertex. -/
lemma card_sequentialCommonCandidates_of_everyAdjacentHasY0
    {s : V} {ys : List V} {b : ℕ}
    (hcap : C.blueDegreeToX s + b ≤ (C.extensionReservoir s).card)
    (hysY : ∀ y ∈ ys, y ∈ C.Y)
    (hysDeg : ∀ y ∈ ys, C.blueDegreeToX y ≤ C.blueDegreeToX s)
    (hadj : C.EveryAdjacentHasY0 ys) :
    ∀ D ∈ sequentialCommonCandidates (C.extensionRedNeighbors s) ys,
      b ≤ D.card := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      cases ys with
      | nil => simp
      | cons y' ys =>
          intro D hD
          simp only [sequentialCommonCandidates_cons_cons, List.mem_cons] at hD
          rw [C.everyAdjacentHasY0_cons_cons] at hadj
          rcases hD with rfl | hD
          · rcases hadj.1 with hy0 | hy0
            · rw [C.extensionRedNeighbors_eq_reservoir_of_mem_Y0 hy0,
                Finset.inter_eq_right.mpr (C.extensionRedNeighbors_subset s y')]
              exact C.extensionCount_le_card_extensionRedNeighbors
                (hysY y' (by simp)) (hysDeg y' (by simp)) hcap
            · rw [C.extensionRedNeighbors_eq_reservoir_of_mem_Y0 hy0,
                Finset.inter_eq_left.mpr (C.extensionRedNeighbors_subset s y)]
              exact C.extensionCount_le_card_extensionRedNeighbors
                (hysY y (by simp)) (hysDeg y (by simp)) hcap
          · apply ih
            · intro z hz
              exact hysY z (by simp [hz])
            · intro z hz
              exact hysDeg z (by simp [hz])
            · exact hadj.2
            · exact hD

/-- The exact ordered list needed by Lemma 3.4 exists in the final `lambda in {2,3}`
configuration. -/
theorem exists_highMu_final_outside_list
    {H : Finset (Finset V)}
    (hc : 4 ≤ C.c) (hUniform : IsThreeUniformOn H C.Y1)
    (hred : HighMuReductionData H C.Y1 C.blueDegreeToX C.r C.a0 C.a1 C.c C.w) :
    ∃ s ∈ C.Y1, C.blueDegreeToX s < C.r ∧
      ∃ ys : List V,
        ys.length = C.extensionCount s ∧ ys ≠ [] ∧ ys.Nodup ∧
        (∀ y ∈ ys, y ∈ C.Y) ∧
        C.EveryAdjacentHasY0 ys ∧
        C.blueDegreeToX s + C.extensionCount s ≤
          (C.extensionReservoir s).card ∧
        ∀ y ∈ ys, C.blueDegreeToX y ≤ C.blueDegreeToX s := by
  classical
  rcases hred with ⟨lam, hlam, ha1, ha0, hw, T, hTH, s, hsComp, hhigh, _hfree, hmax⟩
  have hsY1 : s ∈ C.Y1 := (Finset.mem_sdiff.mp hsComp).1
  have hY0 : C.Y0.Nonempty := by
    apply Finset.card_pos.mp
    rw [← C.a0_eq_card_Y0]
    exact C.one_le_a0
  have hdegAdd : C.blueDegreeToX s + 2 ≤ C.r := by
    apply C.blueDegreeToX_add_two_le_r_of_bounds hY0 (by omega) _ hsY1
    have := C.w_le_r_sub_two
    omega
  have hdegLt : C.blueDegreeToX s < C.r := by omega
  let b := C.extensionCount s
  have hbDef : b = C.r - C.blueDegreeToX s := rfl
  have hbPos : 0 < b := by simp only [b, extensionCount]; omega
  have hbSum : b + C.blueDegreeToX s = C.r := by omega
  have hlamThree : lam ≤ 3 := by rcases hlam with rfl | rfl <;> omega
  have hdegC : C.blueDegreeToX s ≤ 2 * C.c - 2 := by
    have := C.r_le_two_mul_c
    omega
  have hSsub := C.extensionPredecessorSet_subset_X s
  have hScard := C.extensionPredecessorSet_card (C.Y1_subset_Y hsY1)
  have hWsplit : (C.extensionReservoir s).card +
      (C.extensionPredecessorSet s).card = C.X.card := by
    rw [extensionReservoir, Finset.card_sdiff_of_subset hSsub]
    exact Nat.sub_add_cancel (Finset.card_le_card hSsub)
  have hXsum : C.X.card + C.w = C.c ^ 2 + C.r := by
    rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
  have hWcard : (C.extensionReservoir s).card + C.blueDegreeToX s + 1 +
      C.c + lam = C.c ^ 2 + C.r := by
    omega
  have hcap : C.blueDegreeToX s + b ≤ (C.extensionReservoir s).card := by
    exact highMu_final_capacity hc hlamThree hdegC hbSum hWcard
  have hTsub : T ⊆ C.Y1 := (hUniform T hTH).1
  have hTcard : T.card = 3 := (hUniform T hTH).2
  have hCompCard : (C.Y1 \ T).card = 2 * lam - 3 := by
    rw [Finset.card_sdiff_of_subset hTsub, ← C.a1_eq_card_Y1, ha1, hTcard]
  have hshort : b - C.a0 ≤ lam - 1 := by
    exact highMu_shortfall C.r_le_two_mul_c hhigh ha0 hbDef
  have hshortTwo : b - C.a0 ≤ 2 := hshort.trans (lambda_pred_le_two hlam)
  refine ⟨s, hsY1, hdegLt, ?_⟩
  by_cases hb0 : b ≤ C.a0
  · let ys := C.Y0.toList.take b
    have hlen : ys.length = b := by
      have hbCard : b ≤ C.Y0.card := by
        rw [← C.a0_eq_card_Y0]
        exact hb0
      simp [ys, List.length_take, hbCard]
    have hnonempty : ys ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hnodup : ys.Nodup := (Finset.nodup_toList C.Y0).take
    have hmem0 : ∀ y ∈ ys, y ∈ C.Y0 := by
      intro y hy
      exact Finset.mem_toList.mp (List.mem_of_mem_take hy)
    refine ⟨ys, hlen, hnonempty, hnodup,
      (fun y hy ↦ C.Y0_subset_Y (hmem0 y hy)),
      C.everyAdjacentHasY0_of_forall_mem hmem0, hcap, ?_⟩
    intro y hy
    rw [(C.mem_Y0.mp (hmem0 y hy)).2]
    exact Nat.zero_le _
  · have ha0b : C.a0 < b := by omega
    have hkPos : 0 < b - C.a0 := by omega
    have hkCases : b - C.a0 = 1 ∨ b - C.a0 = 2 := by omega
    rcases hkCases with hk | hk
    · have hCompNonempty : (C.Y1 \ T).Nonempty := by
        apply Finset.card_pos.mp
        rw [hCompCard]
        rcases hlam with rfl | rfl <;> omega
      obtain ⟨u, huComp⟩ := hCompNonempty
      have huY1 : u ∈ C.Y1 := (Finset.mem_sdiff.mp huComp).1
      have hu0 : u ∉ C.Y0 := by
        intro hu
        exact Finset.disjoint_left.mp C.Y0_disjoint_Y1 hu huY1
      let ys := u :: C.Y0.toList
      have hlen : ys.length = b := by
        simp [ys]
        rw [← C.a0_eq_card_Y0]
        omega
      have hnodup : ys.Nodup := by
        simp only [ys, List.nodup_cons, Finset.nodup_toList, and_true]
        simpa using hu0
      have hmem0 : ∀ y ∈ C.Y0.toList, y ∈ C.Y0 := by
        intro y hy
        exact Finset.mem_toList.mp hy
      have hallY : ∀ y ∈ ys, y ∈ C.Y := by
        intro y hy
        simp only [ys, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact C.Y1_subset_Y huY1
        · exact C.Y0_subset_Y (hmem0 y hy)
      have hallDeg : ∀ y ∈ ys, C.blueDegreeToX y ≤ C.blueDegreeToX s := by
        intro y hy
        simp only [ys, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hmax _ huComp
        · rw [(C.mem_Y0.mp (hmem0 y hy)).2]
          exact Nat.zero_le _
      exact ⟨ys, hlen, by simp [ys], hnodup, hallY,
        C.everyAdjacentHasY0_cons_of_tail u hmem0, hcap, hallDeg⟩
    · have hCompTwo : 2 ≤ (C.Y1 \ T).card := by
        rw [hCompCard]
        rcases hlam with rfl | rfl <;> omega
      have hCompNonempty : (C.Y1 \ T).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u, huComp⟩ := hCompNonempty
      have hEraseNonempty : ((C.Y1 \ T).erase u).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem huComp]
        omega
      obtain ⟨v, hvErase⟩ := hEraseNonempty
      have hvComp : v ∈ C.Y1 \ T := Finset.mem_of_mem_erase hvErase
      have hvu : v ≠ u := Finset.ne_of_mem_erase hvErase
      obtain ⟨y0, hy0⟩ := hY0
      let L := (C.Y0.erase y0).toList
      let ys := u :: y0 :: v :: L
      have huY1 : u ∈ C.Y1 := (Finset.mem_sdiff.mp huComp).1
      have hvY1 : v ∈ C.Y1 := (Finset.mem_sdiff.mp hvComp).1
      have hu0 : u ∉ C.Y0 := by
        intro hu
        exact Finset.disjoint_left.mp C.Y0_disjoint_Y1 hu huY1
      have hv0 : v ∉ C.Y0 := by
        intro hv
        exact Finset.disjoint_left.mp C.Y0_disjoint_Y1 hv hvY1
      have hLmem : ∀ y ∈ L, y ∈ C.Y0 := by
        intro y hy
        exact Finset.mem_of_mem_erase (Finset.mem_toList.mp hy)
      have hy0L : y0 ∉ L := by simp [L]
      have huL : u ∉ L := fun hu ↦ hu0 (hLmem u hu)
      have hvL : v ∉ L := fun hv ↦ hv0 (hLmem v hv)
      have hLN : L.Nodup := Finset.nodup_toList _
      have huy0 : u ≠ y0 := by
        intro h
        subst u
        exact hu0 hy0
      have hy0v : y0 ≠ v := by
        intro h
        subst v
        exact hv0 hy0
      have hlen : ys.length = b := by
        simp [ys, L]
        rw [Finset.card_erase_of_mem hy0, ← C.a0_eq_card_Y0]
        omega
      have hnodup : ys.Nodup := by
        simp only [ys, List.nodup_cons, List.mem_cons, List.not_mem_nil,
          List.mem_nil_iff, or_false, not_or]
        exact ⟨⟨huy0, ⟨hvu.symm, huL⟩⟩,
          ⟨⟨hy0v, hy0L⟩, ⟨hvL, hLN⟩⟩⟩
      have hallY : ∀ y ∈ ys, y ∈ C.Y := by
        intro y hy
        simp only [ys, List.mem_cons] at hy
        rcases hy with rfl | rfl | rfl | hy
        · exact C.Y1_subset_Y huY1
        · exact C.Y0_subset_Y hy0
        · exact C.Y1_subset_Y hvY1
        · exact C.Y0_subset_Y (hLmem y hy)
      have hallDeg : ∀ y ∈ ys, C.blueDegreeToX y ≤ C.blueDegreeToX s := by
        intro y hy
        simp only [ys, List.mem_cons] at hy
        rcases hy with rfl | rfl | rfl | hy
        · exact hmax _ huComp
        · rw [(C.mem_Y0.mp hy0).2]
          exact Nat.zero_le _
        · exact hmax _ hvComp
        · rw [(C.mem_Y0.mp (hLmem y hy)).2]
          exact Nat.zero_le _
      have hadj : C.EveryAdjacentHasY0 ys := by
        rw [show ys = u :: y0 :: v :: L from rfl,
          C.everyAdjacentHasY0_cons_cons, C.everyAdjacentHasY0_cons_cons]
        exact ⟨Or.inr hy0, Or.inl hy0, C.everyAdjacentHasY0_cons_of_tail v hLmem⟩
      exact ⟨ys, hlen, by simp [ys], hnodup, hallY, hadj, hcap, hallDeg⟩

/-- The final high-`mu` branch is impossible.  This is the concrete discharge of the abstract
selection hypothesis in `highMu_final_extension_contradiction_of_data`. -/
theorem highMu_final_contradiction
    {H : Finset (Finset V)}
    (hc : 4 ≤ C.c) (hUniform : IsThreeUniformOn H C.Y1)
    (hred : HighMuReductionData H C.Y1 C.blueDegreeToX C.r C.a0 C.a1 C.c C.w) :
    False := by
  classical
  obtain ⟨s, hs, hdeg, ys, hlen, hnonempty, hnodup, hysY, hadj, hcap, hysDeg⟩ :=
    C.exists_highMu_final_outside_list hc hUniform hred
  apply C.highMu_greedy_extension_contradiction hs hdeg ys hlen hnonempty hnodup hysY
  · exact C.card_sequentialCommonCandidates_of_everyAdjacentHasY0
      hcap hysY hysDeg hadj
  · intro y hyLast
    have hyMem : y ∈ ys := by
      rcases List.getLast?_eq_some_iff.mp hyLast with ⟨zs, hzs⟩
      rw [hzs]
      simp
    exact C.extensionCount_le_card_extensionRedNeighbors
      (hysY y hyMem) (hysDeg y hyMem) hcap

end Configuration
end Erdos518
