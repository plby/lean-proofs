/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.BasicBounds
import ErdosProblems.Erdos518.MuBound
import ErdosProblems.Erdos518.HighMu

open scoped SimpleGraph List

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance tripleFreeConcreteDecidableEq : DecidableEq V := Classical.decEq V
noncomputable local instance tripleFreeConcreteDecidableAdj : DecidableRel C.G.Adj :=
  Classical.decRel _
noncomputable local instance tripleFreeConcreteDecidableComplAdj : DecidableRel C.Gᶜ.Adj :=
  Classical.decRel _

/-- An outside vertex cannot have complement-colour edges to two consecutive vertices of a
globally longest complement-colour path. -/
lemma not_compl_adj_consecutive_of_globally_longest
    {G : SimpleGraph V} {P A R : List V} {a b y : V}
    (hP : IsPath Gᶜ P) (hlong : IsGloballyLongestMonoPath G P)
    (hy : y ∉ P) (hdecomp : P = A ++ a :: b :: R) :
    ¬ (Gᶜ.Adj y a ∧ Gᶜ.Adj y b) := by
  rintro ⟨hya, hyb⟩
  subst P
  have hperm : A ++ a :: y :: b :: R ~ y :: (A ++ a :: b :: R) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using
      (List.perm_middle (a := y) (l₁ := A ++ [a]) (l₂ := b :: R))
  have hq : IsPath Gᶜ (A ++ a :: y :: b :: R) := by
    refine ⟨by simp, hperm.nodup_iff.mpr (hP.2.1.cons hy), ?_⟩
    have hchain := hP.2.2
    have hay : Gᶜ.Adj a y := hya.symm
    simp_all [List.isChain_append]
  have hlen := hlong.2 (A ++ a :: y :: b :: R) (Or.inr hq)
  simp only [List.length_append, List.length_cons] at hlen
  omega

/-- The complement neighbours of an outside vertex are disjoint from its predecessor clique.
This is the set-level form of the endpoint and no-consecutive-neighbours observations. -/
lemma blueNeighbours_disjoint_predCliqueSet {s : V} (hs : s ∈ C.Y) :
    Disjoint (C.X.filter fun x ↦ C.Gᶜ.Adj s x) (C.predCliqueSet s) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxB hxS
  have hxX : x ∈ C.X := (Finset.mem_filter.mp hxB).1
  have hsx : C.Gᶜ.Adj s x := (Finset.mem_filter.mp hxB).2
  simp only [predCliqueSet, predecessorClique, Finset.mem_insert,
    List.mem_toFinset] at hxS
  rcases hxS with hxLast | hxPred
  · have hred : C.G.Adj s x := by
      rw [hxLast]
      exact (C.predCliqueEnd_adj_outside hs).symm
    exact ((SimpleGraph.compl_adj C.G s x).mp hsx).2 hred
  · obtain ⟨b, A, R, hQ, hsb⟩ := (mem_bluePredecessors_iff C.G).mp hxPred
    have hsQ : s ∉ C.Q := by simpa [C.mem_X] using C.mem_Y.mp hs
    exact not_compl_adj_consecutive_of_globally_longest C.q_isPath
      C.q_isGloballyLongest hsQ hQ ⟨hsx, hsb⟩

/-- The sorted one-based complement-neighbour positions, padded by the two sentinels used in
Claim 2. -/
noncomputable def blueBoundaryList (s : V) : List ℕ :=
  0 :: ((C.blueIndices s).sort (· ≤ ·) ++ [C.Q.length + 1])

/-- Total indexing into `blueBoundaryList`; all uses below are in range, while the default is
the right sentinel. -/
noncomputable def blueBoundaryAt (s : V) (i : ℕ) : ℕ :=
  (C.blueBoundaryList s).getD i (C.Q.length + 1)

lemma blueBoundaryList_length (s : V) :
    (C.blueBoundaryList s).length = C.blueDegreeToX s + 2 := by
  simp [blueBoundaryList, C.blueIndices_card]

lemma blueBoundaryList_sortedLT (s : V) :
    (C.blueBoundaryList s).SortedLT := by
  classical
  unfold blueBoundaryList
  rw [List.sortedLT_iff_pairwise, List.pairwise_cons, List.pairwise_append]
  refine ⟨?_, Finset.sortedLT_sort (C.blueIndices s) |>.pairwise, by simp,
    ?_⟩
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · have hi' : i ∈ C.blueIndices s := (Finset.mem_sort (· ≤ ·)).mp hi
      obtain ⟨x, -, -, rfl⟩ := C.mem_blueIndices.mp hi'
      omega
    · omega
  · intro i hi j hj
    simp only [List.mem_singleton] at hj
    subst j
    have hi' : i ∈ C.blueIndices s := (Finset.mem_sort (· ≤ ·)).mp hi
    have hile := C.blueIndex_le_length hi'
    omega

lemma blueBoundaryList_strictMono (s : V) {i j : ℕ}
    (hi : i < (C.blueBoundaryList s).length)
    (hj : j < (C.blueBoundaryList s).length) (hij : i < j) :
    (C.blueBoundaryList s)[i] < (C.blueBoundaryList s)[j] := by
  exact (List.pairwise_iff_getElem.mp
    (List.sortedLT_iff_pairwise.mp (C.blueBoundaryList_sortedLT s))) i j hi hj hij

lemma blueBoundaryAt_eq_getElem (s : V) {i : ℕ}
    (hi : i < (C.blueBoundaryList s).length) :
    C.blueBoundaryAt s i = (C.blueBoundaryList s)[i] := by
  exact List.getD_eq_getElem (C.blueBoundaryList s) (C.Q.length + 1) hi

@[simp] lemma blueBoundaryAt_zero (s : V) : C.blueBoundaryAt s 0 = 0 := by
  rw [C.blueBoundaryAt_eq_getElem s (by simp [C.blueBoundaryList_length])]
  simp [blueBoundaryList]

lemma blueBoundaryAt_internal_mem (s : V) {i : ℕ}
    (hi : i < C.blueDegreeToX s) : C.blueBoundaryAt s (i + 1) ∈ C.blueIndices s := by
  classical
  have hiList : i < ((C.blueIndices s).sort (· ≤ ·)).length := by
    simpa [Finset.length_sort, C.blueIndices_card] using hi
  unfold blueBoundaryAt blueBoundaryList
  rw [List.getD_cons_succ,
    List.getD_append _ _ _ _ hiList,
    List.getD_eq_getElem _ _ hiList]
  exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hiList)

@[simp] lemma blueBoundaryAt_last (s : V) :
    C.blueBoundaryAt s (C.blueDegreeToX s + 1) = C.Q.length + 1 := by
  classical
  have hiBound : C.blueDegreeToX s + 1 < (C.blueBoundaryList s).length := by
    rw [C.blueBoundaryList_length]
    omega
  rw [C.blueBoundaryAt_eq_getElem s hiBound]
  simp [blueBoundaryList, Finset.length_sort, C.blueIndices_card]

lemma blueBoundaryAt_strictMono (s : V) {i j : ℕ}
    (hi : i < C.blueDegreeToX s + 2) (hj : j < C.blueDegreeToX s + 2)
    (hij : i < j) : C.blueBoundaryAt s i < C.blueBoundaryAt s j := by
  rw [C.blueBoundaryAt_eq_getElem s (by simpa [C.blueBoundaryList_length] using hi),
    C.blueBoundaryAt_eq_getElem s (by simpa [C.blueBoundaryList_length] using hj)]
  exact C.blueBoundaryList_strictMono s
    (by simpa [C.blueBoundaryList_length] using hi)
    (by simpa [C.blueBoundaryList_length] using hj) hij

/-- A blue position strictly between boundary positions two apart is the unique intervening
blue position. -/
lemma blueIndex_between_two_boundaries_eq_middle (s : V) {e k : ℕ}
    (he : e < C.blueDegreeToX s) (hk : k ∈ C.blueIndices s)
    (hlo : C.blueBoundaryAt s e < k)
    (hhi : k < C.blueBoundaryAt s (e + 2)) :
    k = C.blueBoundaryAt s (e + 1) := by
  classical
  have hkSort : k ∈ (C.blueIndices s).sort (· ≤ ·) :=
    (Finset.mem_sort (· ≤ ·)).mpr hk
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hkSort
  have hjdeg : j < C.blueDegreeToX s := by
    simpa [Finset.length_sort, C.blueIndices_card] using hj
  have hpos : C.blueBoundaryAt s (j + 1) = k := by
    have hjList : j < ((C.blueIndices s).sort (· ≤ ·)).length := hj
    unfold blueBoundaryAt blueBoundaryList
    rw [List.getD_cons_succ,
      List.getD_append _ _ _ _ hjList,
      List.getD_eq_getElem _ _ hjList]
    exact hjk
  have hej : e < j + 1 := by
    by_contra hnot
    have hle : j + 1 ≤ e := Nat.le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · rw [← heq, hpos] at hlo
      omega
    · have hmono := C.blueBoundaryAt_strictMono s
          (by omega) (by omega) hlt
      rw [hpos] at hmono
      omega
  have hje : j + 1 < e + 2 := by
    by_contra hnot
    have hle : e + 2 ≤ j + 1 := Nat.le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · rw [heq, hpos] at hhi
      omega
    · have hmono := C.blueBoundaryAt_strictMono s
          (by omega) (by omega) hlt
      rw [hpos] at hmono
      omega
  have : j + 1 = e + 1 := by omega
  rw [← this, hpos]

lemma lowerBlueSet_zero (Y' : Finset V) (s : V) :
    C.lowerBlueSet Y' s 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨-, -, i, hi, hiz⟩ := C.mem_lowerBlueSet.mp hy
  obtain ⟨x, -, -, hidx⟩ := C.mem_blueIndices.mp hi
  omega

/-- The maximal lower boundary with at most one earlier outside vertex.  The following boundary
is either the right sentinel, or maximality supplies the two-lower-vertices witness required by
`tripleFree_estimate`. -/
lemma exists_tripleFree_boundaries {Y' : Finset V} {s : V}
    (hY' : Y' ⊆ C.Y1) (hs : s ∈ Y') :
    ∃ e < C.blueDegreeToX s,
      (C.lowerBlueSet Y' s (C.blueBoundaryAt s e)).card ≤ 1 ∧
      C.HasUpperBoundaryWitness Y' s (C.blueBoundaryAt s (e + 2)) := by
  classical
  have hsY1 : s ∈ C.Y1 := hY' hs
  have hdeg : 1 ≤ C.blueDegreeToX s := C.blueDegreeToX_pos_of_mem_Y1 hsY1
  let E := (Finset.range (C.blueDegreeToX s)).filter fun i ↦
    (C.lowerBlueSet Y' s (C.blueBoundaryAt s i)).card ≤ 1
  have hE : E.Nonempty := by
    refine ⟨0, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp [C.lowerBlueSet_zero Y' s]
  let e := E.max' hE
  have heE : e ∈ E := Finset.max'_mem E hE
  have he : e < C.blueDegreeToX s := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp heE).1
  have heM : (C.lowerBlueSet Y' s (C.blueBoundaryAt s e)).card ≤ 1 :=
    (Finset.mem_filter.mp heE).2
  refine ⟨e, he, heM, ?_⟩
  by_cases helast : e + 1 = C.blueDegreeToX s
  · left
    rw [show e + 2 = C.blueDegreeToX s + 1 by omega]
    exact C.blueBoundaryAt_last s
  · right
    have henext : e + 1 < C.blueDegreeToX s := by omega
    let mid := C.blueBoundaryAt s (e + 1)
    refine ⟨mid, C.blueBoundaryAt_internal_mem s he,
      C.blueBoundaryAt_internal_mem s (i := e + 1) (by omega), ?_, ?_⟩
    · exact C.blueBoundaryAt_strictMono s (by omega) (by omega) (by omega)
    · have hnot : ¬ (C.lowerBlueSet Y' s mid).card ≤ 1 := by
        intro hsmall
        have hnextE : e + 1 ∈ E := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr henext, hsmall⟩
        have hle : e + 1 ≤ e := Finset.le_max' E (e + 1) hnextE
        omega
      omega

/-- In the nonempty-middle case, all but the unique middle blue neighbour of `s` lie in the
reservoir.  The no-consecutive-neighbours observation keeps those vertices out of the
predecessor clique. -/
lemma blueDegree_sub_one_le_tripleFreeF_of_nonempty
    {Y' : Finset V} {s : V} {e : ℕ}
    (hsY : s ∈ C.Y) (he : e < C.blueDegreeToX s)
    (hJ : (C.middleOutsideSet Y' s (C.blueBoundaryAt s e)).Nonempty) :
    C.blueDegreeToX s - 1 ≤
      (C.tripleFreeF Y' (C.predCliqueSet s) s
        (C.blueBoundaryAt s e) (C.blueBoundaryAt s (e + 2))).card := by
  classical
  let B := C.X.filter fun x ↦ C.Gᶜ.Adj s x
  have hmid : C.blueBoundaryAt s (e + 1) ∈ C.blueIndices s :=
    C.blueBoundaryAt_internal_mem s he
  obtain ⟨xm, hxmX, hsxm, hxmIdx⟩ := C.mem_blueIndices.mp hmid
  have hxmB : xm ∈ B := Finset.mem_filter.mpr ⟨hxmX, hsxm⟩
  have hsub : B.erase xm ⊆
      C.tripleFreeF Y' (C.predCliqueSet s) s
        (C.blueBoundaryAt s e) (C.blueBoundaryAt s (e + 2)) := by
    intro x hx
    have hxB : x ∈ B := (Finset.mem_erase.mp hx).2
    have hxne : x ≠ xm := (Finset.mem_erase.mp hx).1
    have hxX : x ∈ C.X := (Finset.mem_filter.mp hxB).1
    have hsx : C.Gᶜ.Adj s x := (Finset.mem_filter.mp hxB).2
    apply C.mem_tripleFreeF.mpr
    refine ⟨hxX, ?_, ?_⟩
    · exact Finset.disjoint_left.mp (C.blueNeighbours_disjoint_predCliqueSet hsY)
        hxB
    · rw [C.tripleFreeF0_eq_between_of_nonempty hJ]
      intro hxBetween
      have hxBetween' := C.mem_betweenVertices.mp hxBetween
      have hxIndex : C.Q.idxOf x + 1 ∈ C.blueIndices s :=
        C.mem_blueIndices.mpr ⟨x, hxX, hsx, rfl⟩
      have heq := C.blueIndex_between_two_boundaries_eq_middle s he hxIndex
        hxBetween'.2.1 hxBetween'.2.2
      have hidxEq : C.Q.idxOf x = C.Q.idxOf xm := by omega
      have hxQ : x ∈ C.Q := C.mem_X.mp hxX
      have hxmQ : xm ∈ C.Q := C.mem_X.mp hxmX
      exact hxne ((List.idxOf_inj hxQ).mp hidxEq)
  have hcardB : B.card = C.blueDegreeToX s := by
    simp [B, blueDegreeToX]
  have hcardErase : (B.erase xm).card = C.blueDegreeToX s - 1 := by
    rw [Finset.card_erase_of_mem hxmB, hcardB]
  rw [← hcardErase]
  exact Finset.card_le_card hsub

/-- In the empty-middle case the reservoir is simply `X \ S_s`; the basic counterexample
bounds make it large enough for the extension obstruction. -/
lemma r_sub_blueDegree_le_tripleFreeF_of_empty
    {Y' : Finset V} {s : V} {lo hi : ℕ} (hsY : s ∈ C.Y)
    (hdegR : C.blueDegreeToX s + 2 ≤ C.r)
    (hJ : ¬ (C.middleOutsideSet Y' s lo).Nonempty) :
    C.r - C.blueDegreeToX s ≤
      (C.tripleFreeF Y' (C.predCliqueSet s) s lo hi).card := by
  classical
  have hSX : C.predCliqueSet s ⊆ C.X := C.predCliqueSet_subset_X s
  have hScard : (C.predCliqueSet s).card = C.blueDegreeToX s + 1 :=
    C.predCliqueSet_card_eq_blueDegree_add_one hsY
  have hc : 1 ≤ C.c := C.one_le_c
  have hr : C.r ≤ 2 * C.c := C.r_le_two_mul_c
  have hw : C.w + 2 ≤ C.r := by
    have := C.w_le_r_sub_two
    omega
  have hEq : C.X.card + C.w = C.c ^ 2 + C.r := by
    rw [← C.n_eq_card_X_add_w, ← C.n_eq_c_sq_add_r]
  have hsquare : 2 * C.c + 1 ≤ C.c ^ 2 + 2 := by
    nlinarith [sq_nonneg (C.c - 1)]
  have hX : C.r + 1 ≤ C.X.card := by omega
  simp only [tripleFreeF]
  rw [C.tripleFreeF0_eq_empty_of_not_nonempty hJ]
  simp only [Finset.sdiff_empty]
  rw [Finset.card_sdiff_of_subset hSX, hScard]
  omega

/-- **Concrete Claim 2.**  Every hypothesis of the abstract triple-free estimate is discharged
from the normalized counterexample configuration: the predecessor clique supplies `S_s`, the
maximal lower boundary supplies `k_e,k_{e+2}`, and the two reservoir bounds follow from the
basic counterexample estimates and the blue-neighbour injection above. -/
theorem tripleFree_estimate_concrete {Y' : Finset V} {s : V}
    (hY' : Y' ⊆ C.Y1) (hs : s ∈ Y') (hfree : C.TripleFreeOn Y')
    (hhigh : C.IsHigh s) :
    C.a0 + max (Y'.card - 2) 0 < C.r - C.blueDegreeToX s := by
  classical
  have hsY1 : s ∈ C.Y1 := hY' hs
  have hsY : s ∈ C.Y := C.Y1_subset_Y hsY1
  obtain ⟨e, he, hM, hwit⟩ := C.exists_tripleFree_boundaries hY' hs
  have hwTwo : C.w + 2 ≤ C.r := by
    have := C.w_le_r_sub_two
    have hc := C.one_le_c
    have hcw := C.w_ge_c
    omega
  have hcTwo : 2 ≤ C.c := by
    have hcw := C.w_ge_c
    have hr := C.r_le_two_mul_c
    omega
  have hdegree : C.blueDegreeToX s + 2 ≤ C.r :=
    C.blueDegreeToX_add_two_le_r_of_bounds C.Y0_nonempty hcTwo hwTwo hsY1
  apply C.tripleFree_estimate_highMu_form
    (S := C.predCliqueSet s) (e := C.predCliqueEnd)
    (lo := C.blueBoundaryAt s e) (hi := C.blueBoundaryAt s (e + 2))
    hY' hs hfree hwit hM
  · exact C.predCliqueSet_isClique hsY
  · exact C.predCliqueEnd_mem_predCliqueSet s
  · exact C.predCliqueSet_subset_X s
  · exact C.predCliqueSet_card_eq_blueDegree_add_one hsY
  · intro y hy
    exact C.predCliqueEnd_adj_outside hy
  · exact hhigh
  · exact hdegree
  · intro hJ
    exact C.r_sub_blueDegree_le_tripleFreeF_of_empty hsY hdegree hJ
  · intro hJ
    exact C.blueDegree_sub_one_le_tripleFreeF_of_nonempty hsY he hJ

end Configuration
end Erdos518
