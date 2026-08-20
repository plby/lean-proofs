/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Selection
import ErdosProblems.Erdos518.ExtensionObstruction
import ErdosProblems.Erdos518.CoverDevice
import ErdosProblems.Erdos518.BasicBounds
import ErdosProblems.Erdos518.Configuration
import ErdosProblems.Erdos518.CaseArithmetic
import ErdosProblems.Erdos518.Intersection

/-!
# Excluding the low maximum-degree case

This file formalizes the branch `2 * mu <= r` in the Chen--Chen proof.  The predecessor
clique and the two as-yet-unavailable exceptional cases of the covering device are exposed as
explicit hypotheses.  Everything between those inputs is proved here: the two sharp greedy
selections, the clique-extension contradiction, construction of the spanning alternating path,
the cardinal arithmetic, and assembly of the final `c`-path cover.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance lowMuDecidableEq : DecidableEq V := Classical.decEq V
noncomputable local instance lowMuDecidableAdj : DecidableRel C.G.Adj := Classical.decRel _
noncomputable local instance lowMuDecidableComplAdj : DecidableRel C.Gᶜ.Adj := Classical.decRel _

/-- Representatives of the sequential common-neighbour sets are adjacent to the two
corresponding entries of the ordered outside list. -/
lemma representative_sequential_edges {N : V → Finset V} {ys xs : List V}
    (hrep : IsRepresentativeList (sequentialCommonCandidates N ys) xs) :
    List.Forall₂ (fun y x ↦ x ∈ N y) ys.dropLast xs ∧
      List.Forall₂ (fun x y ↦ x ∈ N y) xs ys.tail := by
  induction ys generalizing xs with
  | nil =>
      have hxs : xs = [] := by simpa using hrep.length_eq.symm
      subst xs
      simp
  | cons y ys ih =>
      cases ys with
      | nil =>
          have hxs : xs = [] := by simpa using hrep.length_eq.symm
          subst xs
          simp
      | cons y' ys =>
          cases xs with
          | nil => cases hrep
          | cons x xs =>
              cases hrep with
              | cons hx htail =>
                  obtain ⟨hleft, hright⟩ := ih htail
                  have hx' := Finset.mem_inter.mp hx
                  constructor
                  · simpa using List.Forall₂.cons (R := fun y x ↦ x ∈ N y) hx'.1 hleft
                  · simpa using List.Forall₂.cons (R := fun x y ↦ x ∈ N y) hx'.2 hright

lemma IsRepresentativeList.exists_left_of_mem_right
    {Cs : List (Finset V)} {xs : List V}
    (hrep : IsRepresentativeList Cs xs) {x : V} (hx : x ∈ xs) :
    ∃ D ∈ Cs, x ∈ D := by
  induction hrep with
  | nil => simp at hx
  | cons hD htail ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨_, by simp, hD⟩
      · obtain ⟨D, hDCs, hxD⟩ := ih hx
        exact ⟨D, by simp [hDCs], hxD⟩

lemma exists_pair_of_mem_sequentialCommonCandidates {N : V → Finset V}
    {ys : List V} {D : Finset V} (hD : D ∈ sequentialCommonCandidates N ys) :
    ∃ y ∈ ys, ∃ y' ∈ ys, D = N y ∩ N y' := by
  induction ys with
  | nil => simp at hD
  | cons y ys ih =>
      cases ys with
      | nil => simp at hD
      | cons y' ys =>
          simp only [sequentialCommonCandidates_cons_cons, List.mem_cons] at hD
          rcases hD with rfl | hD
          · exact ⟨y, by simp, y', by simp, rfl⟩
          · obtain ⟨u, hu, v, hv, rfl⟩ := ih hD
            exact ⟨u, by simp [hu], v, by simp [hv], rfl⟩

/-- Exact-edge version of the alternating-path constructor when the first side has one
extra vertex. -/
lemma isPath_alternate_of_aligned_edges_add_one {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length + 1)
    (hxy : List.Forall₂ G.Adj xs.dropLast ys)
    (hyx : List.Forall₂ G.Adj ys xs.tail)
    (hxs : xs.Nodup) (hys : ys.Nodup) (hdisj : List.Disjoint xs ys) :
    IsPath G (alternate xs ys) := by
  have hnonempty : xs ≠ [] := by
    intro h
    subst xs
    simp at hlen
  refine ⟨alternate_ne_nil_of_left_ne_nil hnonempty,
    nodup_alternate hxs hys hdisj, ?_⟩
  induction xs generalizing ys with
  | nil => contradiction
  | cons x xs ih =>
      cases ys with
      | nil =>
          have hxsLen : xs.length = 0 := by simpa using hlen
          have hxsNil : xs = [] := List.eq_nil_of_length_eq_zero hxsLen
          subst xs
          simp [alternate]
      | cons y ys =>
          have hxs0 : xs ≠ [] := by
            apply List.ne_nil_of_length_pos
            simp only [List.length_cons] at hlen
            omega
          cases xs with
          | nil => contradiction
          | cons x' xs =>
              have hlen' : (x' :: xs).length = ys.length + 1 := by
                simp only [List.length_cons] at hlen ⊢
                omega
              have hdrop : (x :: x' :: xs).dropLast = x :: (x' :: xs).dropLast := by
                simp
              rw [hdrop] at hxy
              simp only [List.tail_cons] at hyx
              cases hxy with
              | cons hfirst hxyTail =>
                  cases hyx with
                  | cons hsecond hyxTail =>
                      have htail : (alternate (x' :: xs) ys).IsChain G.Adj := by
                        apply ih hlen'
                        · exact hxyTail
                        · exact hyxTail
                        · exact hxs.tail
                        · exact hys.tail
                        · intro a ha hb
                          exact hdisj (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem y hb)
                        · simp
                      have hconnect :
                          ∀ z ∈ (alternate (x' :: xs) ys).head?, G.Adj y z := by
                        intro z hz
                        rw [head?_alternate_of_left_ne_nil (by simp : x' :: xs ≠ [])] at hz
                        simp only [List.head?_cons, Option.mem_some_iff] at hz
                        subst z
                        exact hsecond
                      rw [alternate_cons_cons, List.isChain_cons_cons]
                      exact ⟨hfirst, htail.cons hconnect⟩

/-- Red neighbours of `y` in a specified finite set. -/
noncomputable def redNeighborsIn (A : Finset V) (y : V) : Finset V :=
  A.filter fun x ↦ C.G.Adj y x

@[simp] lemma mem_redNeighborsIn {A : Finset V} {y x : V} :
    x ∈ C.redNeighborsIn A y ↔ x ∈ A ∧ C.G.Adj y x := by
  classical
  simp [redNeighborsIn]

lemma redNeighborsIn_subset (A : Finset V) (y : V) : C.redNeighborsIn A y ⊆ A := by
  classical
  exact Finset.filter_subset _ _

/-- On a subset of `X`, the red-neighbour count plus the total blue degree into `X`
dominates the size of the subset. -/
lemma card_le_redNeighborsIn_add_blueDegree {A : Finset V} {y : V}
    (hAX : A ⊆ C.X) (hy : y ∈ C.Y) :
    A.card ≤ (C.redNeighborsIn A y).card + C.blueDegreeToX y := by
  classical
  let B := A.filter fun x ↦ C.Gᶜ.Adj y x
  have hyX : y ∉ C.X := C.mem_Y.mp hy
  have hUnion : C.redNeighborsIn A y ∪ B = A := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (C.mem_redNeighborsIn.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      by_cases hred : C.G.Adj y x
      · exact Finset.mem_union_left _ (C.mem_redNeighborsIn.mpr ⟨hx, hred⟩)
      · apply Finset.mem_union_right
        refine Finset.mem_filter.mpr ⟨hx, (SimpleGraph.compl_adj C.G y x).2 ⟨?_, hred⟩⟩
        intro hyx
        exact hyX (hyx ▸ hAX hx)
  have hDisjoint : Disjoint (C.redNeighborsIn A y) B := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    have hred := (C.mem_redNeighborsIn.mp hxR).2
    have hblue := (Finset.mem_filter.mp hxB).2
    exact ((SimpleGraph.compl_adj C.G y x).mp hblue).2 hred
  have hBsub : B ⊆ C.X.filter fun x ↦ C.Gᶜ.Adj y x := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hAX (Finset.mem_filter.mp hx).1,
      (Finset.mem_filter.mp hx).2⟩
  have hcard := Finset.card_union_of_disjoint hDisjoint
  rw [hUnion] at hcard
  have hBle : B.card ≤ C.blueDegreeToX y := by
    simpa [blueDegreeToX] using Finset.card_le_card hBsub
  omega

/-- Two red-neighbour sets have a large intersection: at most the two blue-degree
budgets can be missing from the ambient set. -/
lemma card_le_commonRed_add_blueDegrees {A : Finset V} {y y' : V}
    (hAX : A ⊆ C.X) (hy : y ∈ C.Y) (hy' : y' ∈ C.Y) :
    A.card ≤
      ((C.redNeighborsIn A y) ∩ (C.redNeighborsIn A y')).card +
        C.blueDegreeToX y + C.blueDegreeToX y' := by
  classical
  have hyBound := C.card_le_redNeighborsIn_add_blueDegree hAX hy
  have hy'Bound := C.card_le_redNeighborsIn_add_blueDegree hAX hy'
  have hUnionSub : C.redNeighborsIn A y ∪ C.redNeighborsIn A y' ⊆ A :=
    Finset.union_subset (C.redNeighborsIn_subset A y) (C.redNeighborsIn_subset A y')
  have hUnionCard := Finset.card_le_card hUnionSub
  have hIE := Finset.card_inter_add_card_union
    (C.redNeighborsIn A y) (C.redNeighborsIn A y')
  omega

/-- Vertices of `Y₀` are red-complete to `X`. -/
lemma red_complete_Y0_X {y x : V} (hy : y ∈ C.Y0) (hx : x ∈ C.X) :
    C.G.Adj y x := by
  classical
  by_contra hred
  have hyY : y ∈ C.Y := C.Y0_subset_Y hy
  have hyx : y ≠ x := by
    intro h
    subst x
    exact Finset.disjoint_left.mp C.X_disjoint_Y hx hyY
  have hblue : C.Gᶜ.Adj y x := (SimpleGraph.compl_adj C.G y x).2 ⟨hyx, hred⟩
  have hxB : x ∈ C.X.filter fun z ↦ C.Gᶜ.Adj y z := Finset.mem_filter.mpr ⟨hx, hblue⟩
  have hpos : 0 < C.blueDegreeToX y := by
    simpa [blueDegreeToX] using Finset.card_pos.mpr ⟨x, hxB⟩
  have hzero : C.blueDegreeToX y = 0 := (C.mem_Y0.mp hy).2
  omega

/-- A set of `mu + 1` vertices in `X` contains a red neighbour of every outside vertex. -/
lemma exists_red_neighbor_in_large_set {S : Finset V} {y : V}
    (hSX : S ⊆ C.X) (hScard : S.card = C.mu + 1) (hy : y ∈ C.Y) :
    ∃ e ∈ S, C.G.Adj e y := by
  classical
  by_contra h
  push_neg at h
  have hSub : S ⊆ C.X.filter fun x ↦ C.Gᶜ.Adj y x := by
    intro x hx
    have hyx : y ≠ x := by
      intro heq
      subst x
      exact Finset.disjoint_left.mp C.X_disjoint_Y (hSX hx) hy
    have hblue : C.Gᶜ.Adj y x :=
      (SimpleGraph.compl_adj C.G y x).2 ⟨hyx, fun hadj ↦ h x hx hadj.symm⟩
    exact Finset.mem_filter.mpr ⟨hSX hx, hblue⟩
  have hcard := Finset.card_le_card hSub
  have hdeg := C.blueDegreeToX_le_mu_of_mem_Y hy
  have hdeg' : (C.X.filter fun x ↦ C.Gᶜ.Adj y x).card ≤ C.mu := by
    simpa [Configuration.blueDegreeToX] using hdeg
  omega

/-- The endpoint and consecutive-common-neighbour estimates used twice in the low-`mu`
branch.  They are stated for `W = X \ S`, where `S` is the predecessor clique. -/
lemma lowMu_candidate_bounds {S : Finset V}
    (hc : 4 ≤ C.c) (hw : C.w ≤ C.r - 2) (hY1 : C.Y1.Nonempty)
    (hlow : 2 * C.mu ≤ C.r)
    (hSX : S ⊆ C.X) (hScard : S.card = C.mu + 1) :
    let W := C.X \ S
    let a := C.r - C.mu
    (∀ y ∈ C.Y, a ≤ (C.redNeighborsIn W y).card) ∧
      (∀ y ∈ C.Y, ∀ y' ∈ C.Y,
        a - 1 ≤ ((C.redNeighborsIn W y) ∩ (C.redNeighborsIn W y')).card) := by
  classical
  dsimp only
  have hcZ : (4 : ℤ) ≤ C.c := by exact_mod_cast hc
  have hrZ : (C.r : ℤ) ≤ 2 * C.c := by exact_mod_cast C.r_le_two_mul_c
  have honeMu := C.one_le_mu hY1
  have hwAdd : C.w + 2 ≤ C.r := by omega
  have hwAddZ : (C.w : ℤ) + 2 ≤ C.r := by exact_mod_cast hwAdd
  have hwZ : (C.w : ℤ) ≤ C.r - 2 := by omega
  have hlowZ : 2 * (C.mu : ℤ) ≤ C.r := by exact_mod_cast hlow
  have hEndpointZ := lowMu_endpoint_positive hcZ hrZ hwZ hlowZ
  have hEndpointZ' : (C.w : ℤ) + C.mu + 1 < C.c ^ 2 := by
    nlinarith
  have hEndpoint : C.w + C.mu + 1 < C.c ^ 2 := by
    exact_mod_cast hEndpointZ'
  have hCommonZ := lowMu_common_nonneg hcZ hrZ hwZ hlowZ
  have hCommonZ' : (C.w : ℤ) + 2 * C.mu ≤ C.c ^ 2 := by
    nlinarith
  have hCommon : C.w + 2 * C.mu ≤ C.c ^ 2 := by
    exact_mod_cast hCommonZ'
  have hXsum : C.X.card + C.w = C.c ^ 2 + C.r := by
    rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
  have hSle : S.card ≤ C.X.card := Finset.card_le_card hSX
  have hWsum : (C.X \ S).card + S.card = C.X.card := by
    rw [Finset.card_sdiff_of_subset hSX]
    omega
  constructor
  · intro y hy
    have hbase := C.card_le_redNeighborsIn_add_blueDegree
      (A := C.X \ S) (Finset.sdiff_subset.trans (by rfl)) hy
    have hdeg := C.blueDegreeToX_le_mu_of_mem_Y hy
    omega
  · intro y hy y' hy'
    have hbase := C.card_le_commonRed_add_blueDegrees
      (A := C.X \ S) (Finset.sdiff_subset.trans (by rfl)) hy hy'
    have hdeg := C.blueDegreeToX_le_mu_of_mem_Y hy
    have hdeg' := C.blueDegreeToX_le_mu_of_mem_Y hy'
    omega

/-- If the predecessor clique has its expected size, the extension obstruction forces
`r - mu` to be strictly larger than the number of outside vertices. -/
theorem lowMu_deficit_gt_w
    (hc : 4 ≤ C.c) (hw : C.w ≤ C.r - 2) (hY1 : C.Y1.Nonempty)
    (hlow : 2 * C.mu ≤ C.r) :
    C.w < C.r - C.mu := by
  classical
  obtain ⟨z, hzY1, hzDegree⟩ := C.exists_mem_Y1_blueDegreeToX_eq_mu hY1
  let S := C.extensionPredecessorSet z
  have hSX : S ⊆ C.X := C.extensionPredecessorSet_subset_X z
  have hScard : S.card = C.mu + 1 := by
    rw [C.extensionPredecessorSet_card (C.Y1_subset_Y hzY1), hzDegree]
  let W := C.X \ S
  let a := C.r - C.mu
  have honeMu := C.one_le_mu hY1
  have hmuLeR : C.mu ≤ C.r := by omega
  have haPos : 1 ≤ a := by simp only [a]; omega
  by_contra hnot
  have haW : a ≤ C.w := by omega
  have haY : a ≤ C.Y.card := by simpa only [C.w_eq_card_Y] using haW
  let ys := C.Y.toList.take a
  have hysLen : ys.length = a := by
    simp [ys, List.length_take, haY]
  have hys0 : ys ≠ [] := by
    apply List.ne_nil_of_length_pos
    omega
  have hysN : ys.Nodup := (Finset.nodup_toList C.Y).take
  have hysY : ∀ y ∈ ys, y ∈ C.Y := by
    intro y hy
    exact Finset.mem_toList.mp (List.mem_of_mem_take hy)
  let N : V → Finset V := fun y ↦ C.redNeighborsIn W y
  have hBounds := C.lowMu_candidate_bounds hc hw hY1 hlow hSX hScard
  have hCommon : ∀ D ∈ sequentialCommonCandidates N ys,
      (sequentialCommonCandidates N ys).length ≤ D.card := by
    intro D hD
    obtain ⟨y, hy, y', hy', rfl⟩ :=
      exists_pair_of_mem_sequentialCommonCandidates hD
    rw [length_sequentialCommonCandidates, hysLen]
    exact hBounds.2 y (hysY y hy) y' (hysY y' hy')
  let yLast := ys.getLast hys0
  have hyLastY : yLast ∈ C.Y := hysY yLast (List.getLast_mem hys0)
  have hEndpoint : (sequentialCommonCandidates N ys).length + 1 ≤ (N yLast).card := by
    rw [length_sequentialCommonCandidates, hysLen]
    have hlastBound := hBounds.1 yLast hyLastY
    change a ≤ (N yLast).card at hlastBound
    omega
  obtain ⟨xs, zLast, hxsN, hrep, hzLast⟩ :=
    exists_nodup_sequential_common_and_endpoint N ys (N yLast) hCommon hEndpoint
  let xall := xs ++ [zLast]
  have hxallN : xall.Nodup := by simpa [xall] using hxsN
  have hrepEdges := representative_sequential_edges hrep
  have hleftMem : List.Forall₂ (fun y x ↦ x ∈ N y) ys.dropLast xs := hrepEdges.1
  have hrightMem : List.Forall₂ (fun x y ↦ x ∈ N y) xs ys.tail := hrepEdges.2
  have hallLeftMem : List.Forall₂ (fun y x ↦ x ∈ N y) ys xall := by
    rw [← List.dropLast_append_getLast hys0]
    exact List.rel_append hleftMem
      (List.Forall₂.cons (R := fun y x ↦ x ∈ N y) hzLast List.Forall₂.nil)
  have hNsubW : ∀ y, N y ⊆ W := fun y ↦ C.redNeighborsIn_subset W y
  have hxsW : ∀ x ∈ xs, x ∈ W := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ :=
      IsRepresentativeList.exists_left_of_mem_right hrep hx
    obtain ⟨y, -, y', -, rfl⟩ := exists_pair_of_mem_sequentialCommonCandidates hD
    exact hNsubW y (Finset.inter_subset_left hxD)
  have hxallW : ∀ x ∈ xall, x ∈ W := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxsW x hx
    · simp only [List.mem_singleton] at hx
      subst x
      exact hNsubW yLast hzLast
  have hxallX : ∀ x ∈ xall, x ∈ C.X := by
    intro x hx
    exact Finset.sdiff_subset (hxallW x hx)
  have hyxDisj : List.Disjoint ys xall := by
    intro v hvY hvX
    exact Finset.disjoint_left.mp C.X_disjoint_Y (hxallX v hvX) (hysY v hvY)
  have hysOutS : ∀ y ∈ ys, y ∉ S := by
    intro y hy hS
    exact Finset.disjoint_left.mp C.X_disjoint_Y (hSX hS) (hysY y hy)
  have hxsOutS : ∀ x ∈ xall, x ∉ S := by
    intro x hx hS
    exact (Finset.mem_sdiff.mp (hxallW x hx)).2 hS
  have hyxAdj : List.Forall₂ C.G.Adj ys xall :=
    hallLeftMem.imp fun y x hx ↦ (C.mem_redNeighborsIn.mp hx).2
  have hxyAdj : List.Forall₂ C.G.Adj xall.dropLast ys.tail := by
    have hxsDrop : xall.dropLast = xs := by simp [xall]
    rw [hxsDrop]
    exact hrightMem.imp fun x y hx ↦ (C.mem_redNeighborsIn.mp hx).2.symm
  have hxallLen : xall.length = a := by
    have hrepLen := hrep.length_eq
    simp only [xall, List.length_append, List.length_singleton,
      length_sequentialCommonCandidates, hysLen] at hrepLen ⊢
    omega
  have hdeg : C.blueDegreeToX z < C.r := by omega
  apply C.clique_extension_obstruction_list hzY1 hdeg
      (ys := ys) (xs := xall)
  · change ys.length = C.r - C.blueDegreeToX z
    rw [hzDegree]
    simpa only [a] using hysLen
  · change xall.length = C.r - C.blueDegreeToX z
    rw [hzDegree]
    simpa only [a] using hxallLen
  · exact hysN
  · exact hxallN
  · exact hysY
  · intro x hx
    simpa [extensionReservoir, W, S] using hxallW x hx
  · exact hyxAdj
  · exact hxyAdj

/-- In the low-`mu` branch, all outside vertices lie on one red alternating path together
with exactly `w + 1` vertices of `X`. -/
theorem exists_lowMu_spanning_path
    (hc : 4 ≤ C.c) (hcw : C.c ≤ C.w) (hw : C.w ≤ C.r - 2)
    (hY1 : C.Y1.Nonempty) (hlow : 2 * C.mu ≤ C.r) :
    ∃ p : List V, IsPath C.G p ∧
      (∀ y ∈ C.Y, y ∈ pathSupport p) ∧
      (pathSupport p ∩ C.X).card = C.w + 1 := by
  classical
  obtain ⟨z, hzY1, hzDegree⟩ := C.exists_mem_Y1_blueDegreeToX_eq_mu hY1
  let S := C.extensionPredecessorSet z
  have hSX : S ⊆ C.X := C.extensionPredecessorSet_subset_X z
  have hScard : S.card = C.mu + 1 := by
    rw [C.extensionPredecessorSet_card (C.Y1_subset_Y hzY1), hzDegree]
  let W := C.X \ S
  let a := C.r - C.mu
  have hwa : C.w < a := C.lowMu_deficit_gt_w hc hw hY1 hlow
  have hBounds := C.lowMu_candidate_bounds hc hw hY1 hlow hSX hScard
  let ys := C.Y.toList
  have hysLen : ys.length = C.w := by simp [ys, C.w_eq_card_Y]
  have hys0 : ys ≠ [] := by
    apply List.ne_nil_of_length_pos
    omega
  have hysN : ys.Nodup := Finset.nodup_toList C.Y
  have hysY : ∀ y ∈ ys, y ∈ C.Y := by
    intro y hy
    exact Finset.mem_toList.mp hy
  let N : V → Finset V := fun y ↦ C.redNeighborsIn W y
  have hCommon : ∀ D ∈ sequentialCommonCandidates N ys,
      (sequentialCommonCandidates N ys).length ≤ D.card := by
    intro D hD
    obtain ⟨y, hy, y', hy', rfl⟩ :=
      exists_pair_of_mem_sequentialCommonCandidates hD
    rw [length_sequentialCommonCandidates, hysLen]
    have hbound := hBounds.2 y (hysY y hy) y' (hysY y' hy')
    change a - 1 ≤ (N y ∩ N y').card at hbound
    omega
  let yFirst := ys.head hys0
  let yLast := ys.getLast hys0
  have hyFirstY : yFirst ∈ C.Y := hysY yFirst (List.head_mem hys0)
  have hyLastY : yLast ∈ C.Y := hysY yLast (List.getLast_mem hys0)
  have hLeft : (sequentialCommonCandidates N ys).length + 2 ≤ (N yFirst).card := by
    rw [length_sequentialCommonCandidates, hysLen]
    have hbound := hBounds.1 yFirst hyFirstY
    change a ≤ (N yFirst).card at hbound
    omega
  have hRight : (sequentialCommonCandidates N ys).length + 2 ≤ (N yLast).card := by
    rw [length_sequentialCommonCandidates, hysLen]
    have hbound := hBounds.1 yLast hyLastY
    change a ≤ (N yLast).card at hbound
    omega
  obtain ⟨xFirst, xs, xLast, hxallN, hxFirst, hrep, hxLast⟩ :=
    exists_nodup_sequential_endpoints_and_common N ys (N yFirst) (N yLast)
      hCommon hLeft hRight
  let xall := xFirst :: xs ++ [xLast]
  have hxallN' : xall.Nodup := by simpa [xall] using hxallN
  have hrepEdges := representative_sequential_edges hrep
  have hleftMem : List.Forall₂ (fun y x ↦ x ∈ N y) ys.dropLast xs := hrepEdges.1
  have hrightMem : List.Forall₂ (fun x y ↦ x ∈ N y) xs ys.tail := hrepEdges.2
  have hNsubW : ∀ y, N y ⊆ W := fun y ↦ C.redNeighborsIn_subset W y
  have hxsW : ∀ x ∈ xs, x ∈ W := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ :=
      IsRepresentativeList.exists_left_of_mem_right hrep hx
    obtain ⟨y, -, y', -, rfl⟩ := exists_pair_of_mem_sequentialCommonCandidates hD
    exact hNsubW y (Finset.inter_subset_left hxD)
  have hxallW : ∀ x ∈ xall, x ∈ W := by
    intro x hx
    change x ∈ xFirst :: (xs ++ [xLast]) at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hNsubW yFirst hxFirst
    · rcases List.mem_append.mp hx with hx | hx
      · exact hxsW x hx
      · have hxEq : x = xLast := by simpa using hx
        subst x
        exact hNsubW yLast hxLast
  have hxallX : ∀ x ∈ xall, x ∈ C.X := by
    intro x hx
    exact Finset.sdiff_subset (hxallW x hx)
  have hdisj : List.Disjoint xall ys := by
    intro v hvX hvY
    exact Finset.disjoint_left.mp C.X_disjoint_Y (hxallX v hvX) (hysY v hvY)
  have hxyMem : List.Forall₂ (fun x y ↦ x ∈ N y) xall.dropLast ys := by
    have hxDrop : xall.dropLast = xFirst :: xs := by
      change ((xFirst :: xs) ++ [xLast]).dropLast = xFirst :: xs
      exact List.dropLast_concat
    rw [hxDrop]
    have hheadMem : ys.head hys0 ∈ ys.head? := by
      rw [List.head?_eq_some_head hys0]
      simp
    rw [← List.cons_head?_tail hheadMem]
    exact List.Forall₂.cons (R := fun x y ↦ x ∈ N y) hxFirst hrightMem
  have hyxMem : List.Forall₂ (fun y x ↦ x ∈ N y) ys xall.tail := by
    have hxTail : xall.tail = xs ++ [xLast] := by simp [xall]
    rw [hxTail, ← List.dropLast_append_getLast hys0]
    exact List.rel_append hleftMem
      (List.Forall₂.cons (R := fun y x ↦ x ∈ N y) hxLast List.Forall₂.nil)
  have hxyAdj : List.Forall₂ C.G.Adj xall.dropLast ys :=
    hxyMem.imp fun x y hx ↦ (C.mem_redNeighborsIn.mp hx).2.symm
  have hyxAdj : List.Forall₂ C.G.Adj ys xall.tail :=
    hyxMem.imp fun y x hx ↦ (C.mem_redNeighborsIn.mp hx).2
  have hxallLen : xall.length = C.w + 1 := by
    have hrepLen := hrep.length_eq
    simp only [xall, List.length_cons, List.length_append, List.length_singleton,
      List.length_nil, length_sequentialCommonCandidates, hysLen] at hrepLen ⊢
    omega
  let p := alternate xall ys
  have hp : IsPath C.G p := by
    apply isPath_alternate_of_aligned_edges_add_one
    · omega
    · exact hxyAdj
    · exact hyxAdj
    · exact hxallN'
    · exact hysN
    · exact hdisj
  refine ⟨p, hp, ?_, ?_⟩
  · intro y hy
    apply mem_pathSupport.mpr
    exact mem_alternate_right (Finset.mem_toList.mpr hy)
  · have hInter : pathSupport p ∩ C.X = xall.toFinset := by
      ext v
      simp only [pathSupport, p, Finset.mem_inter, List.mem_toFinset]
      constructor
      · rintro ⟨hv, hvX⟩
        rcases mem_alternate.mp hv with hv | hv
        · exact hv
        · exact (Finset.disjoint_left.mp C.X_disjoint_Y hvX (hysY v hv)).elim
      · intro hv
        exact ⟨mem_alternate_left hv, hxallX v hv⟩
    rw [hInter, List.toFinset_card_of_nodup hxallN', hxallLen]

/-- The low-maximum-blue-degree branch after the key equality
`c = a₀ + ceil(a₁ / 2)` is impossible.  The proof dispatches to the three exact cases
of the red covering device and appends its `c - 1` paths to the spanning path above. -/
theorem lowMu_impossible_of_key
    (hc : 4 ≤ C.c) (hkey : C.c = C.a0 + ceilHalf C.a1)
    (hlow : 2 * C.mu ≤ C.r) : False := by
  classical
  have hcw := C.w_ge_c
  have hw := C.w_le_r_sub_two
  have hY1 := C.Y1_nonempty
  have hdeficit := C.lowMu_deficit_gt_w hc hw hY1 hlow
  have honeMu := C.one_le_mu hY1
  have hmuLeR : C.mu ≤ C.r := by omega
  have hmuLeC : C.mu ≤ C.c := by
    have hr := C.r_le_two_mul_c
    omega
  have ha0Mu : C.mu ≤ C.a0 := by
    have ha0 := C.a0_lower_bound
    have hr := C.r_le_two_mul_c
    omega
  have ha0LeC : C.a0 ≤ C.c := by
    rw [hkey]
    omega
  have hmuA0C : C.mu ≤ C.a0 ∧ C.a0 ≤ C.c := ⟨ha0Mu, ha0LeC⟩
  obtain ⟨p, hp, hpY, hpX⟩ := C.exists_lowMu_spanning_path hc hcw hw hY1 hlow
  let D := C.X \ pathSupport p
  let h := C.c - 1
  let P := coverDeviceP D C.Y0 h
  let q := coverDeviceQ D C.Y0 h
  have hDX : D ⊆ C.X := Finset.sdiff_subset
  have hInterSub : pathSupport p ∩ C.X ⊆ C.X := Finset.inter_subset_right
  have hDEq : D = C.X \ (pathSupport p ∩ C.X) := by
    ext v
    simp [D]
  have hDcardSub : D.card = C.X.card - (pathSupport p ∩ C.X).card := by
    rw [hDEq, Finset.card_sdiff_of_subset hInterSub]
  have hXsum : C.X.card + C.w = C.c ^ 2 + C.r := by
    rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
  have hDcard : D.card = C.c ^ 2 + C.r - 2 * C.w - 1 := by
    omega
  have hhPos : 1 ≤ h := by simp only [h]; omega
  have hmuTwoH : C.mu ≤ 2 * h := by simp only [h]; omega
  have hXY0 : Disjoint C.X C.Y0 := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact Finset.disjoint_left.mp C.X_disjoint_Y hx (C.Y0_subset_Y hy)
  have hXY1 : Disjoint C.X C.Y1 := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact Finset.disjoint_left.mp C.X_disjoint_Y hx (C.Y1_subset_Y hy)
  have hcomplete : ∀ y ∈ C.Y0, ∀ x ∈ C.X, C.G.Adj y x := by
    intro y hy x hx
    exact C.red_complete_Y0_X hy hx
  have hsparse : ∀ y ∈ C.Y1,
      (nonRedNeighboursIn C.G C.X y).card ≤ C.mu := by
    intro y hy
    have hyY : y ∈ C.Y := C.Y1_subset_Y hy
    have hSub : nonRedNeighboursIn C.G C.X y ⊆
        C.X.filter fun x ↦ C.Gᶜ.Adj y x := by
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      have hyx : y ≠ x := by
        intro heq
        subst x
        exact Finset.disjoint_left.mp C.X_disjoint_Y hxData.1 hyY
      exact Finset.mem_filter.mpr ⟨hxData.1,
        (SimpleGraph.compl_adj C.G y x).2 ⟨hyx, hxData.2⟩⟩
    have hcard := Finset.card_le_card hSub
    have hdeg := C.blueDegreeToX_le_mu_of_mem_Y hyY
    have hdeg' : (C.X.filter fun x ↦ C.Gᶜ.Adj y x).card ≤ C.mu := by
      simpa [Configuration.blueDegreeToX] using hdeg
    omega
  have hpDef : P = (D.card : ℤ) - (h : ℤ) * ((C.a0 : ℤ) + 1) := by
    simp [P, coverDeviceP, C.a0_eq_card_Y0]
  have hdZ : (D.card : ℤ) = C.c ^ 2 + C.r - 2 * C.w - 1 := by
    have hInterLe : (pathSupport p ∩ C.X).card ≤ C.X.card :=
      Finset.card_le_card hInterSub
    have hXsumZ : (C.X.card : ℤ) + C.w = C.c ^ 2 + C.r := by
      exact_mod_cast hXsum
    have hpXZ : ((pathSupport p ∩ C.X).card : ℤ) = C.w + 1 := by
      exact_mod_cast hpX
    rw [hDcardSub, Nat.cast_sub hInterLe]
    omega
  have hhZ : (h : ℤ) = C.c - 1 := by
    change ((C.c - 1 : ℕ) : ℤ) = (C.c : ℤ) - 1
    rw [Nat.cast_sub (by omega : 1 ≤ C.c)]
    norm_num
  have hwZ : (C.w : ℤ) = C.a0 + C.a1 := by
    exact_mod_cast C.w_eq_a0_add_a1
  have hrZ : (C.r : ℤ) ≤ 2 * C.c := by exact_mod_cast C.r_le_two_mul_c
  have hcwZ : (C.c : ℤ) ≤ C.w := by exact_mod_cast hcw
  have hhPosZ : (1 : ℤ) ≤ h := by exact_mod_cast hhPos
  have hmu0Z : (0 : ℤ) ≤ C.mu := by positivity
  have ha0MuZ : (C.mu : ℤ) ≤ C.a0 := by exact_mod_cast hmuA0C.1
  have hmuTwoHZ : (C.mu : ℤ) ≤ 2 * h := by exact_mod_cast hmuTwoH
  have hdevice : HasPathCoverOnAtMost C.G (D : Set V) h := by
    by_cases hpNonpos : P ≤ 0
    · apply coverDevice_case_one hDX hXY0 hcomplete
      simpa [P] using hpNonpos
    · have hpPos : 0 < P := lt_of_not_ge hpNonpos
      by_cases hpSmall : P ≤ (h : ℤ)
      · have hsmallLower := lowMu_small_p_endpoint
          (μ := (C.mu : ℤ)) hpDef hpSmall
        have hbase : 0 ≤ (h : ℤ) * C.a0 - C.mu :=
          lowMu_ha0_nonneg hhPosZ hmu0Z ha0MuZ
        have htwop : 2 * P ≤ (D.card : ℤ) - C.mu := by omega
        have hmuD : C.mu ≤ D.card := by exact_mod_cast (show (C.mu : ℤ) ≤ D.card by omega)
        have hPnat : (P.toNat : ℤ) = P := by omega
        have hpHNatZ : (P.toNat : ℤ) ≤ (h : ℤ) := by omega
        have hpHNat : P.toNat ≤ h := by exact_mod_cast hpHNatZ
        have htwopNat : 2 * P.toNat ≤ D.card - C.mu := by
          have htwopNatZ : ((2 * P.toNat : ℕ) : ℤ) ≤
              ((D.card - C.mu : ℕ) : ℤ) := by
            rw [Nat.cast_mul, Nat.cast_ofNat, hPnat, Nat.cast_sub hmuD]
            exact htwop
          exact_mod_cast htwopNatZ
        have hpHalfNat : P.toNat ≤ (D.card - C.mu) / 2 := by omega
        have hpMinNat : P.toNat ≤ min h ((D.card - C.mu) / 2) :=
          le_min hpHNat hpHalfNat
        have hpBound : P ≤ (min h ((D.card - C.mu) / 2) : ℕ) := by
          have hpMinZ : (P.toNat : ℤ) ≤
              (min h ((D.card - C.mu) / 2) : ℕ) := by
            exact_mod_cast hpMinNat
          omega
        apply coverDevice_case_two hDX hY1 hXY0 hXY1 C.Y0_disjoint_Y1
          hcomplete hsparse
        · simpa [P] using hpPos
        · simpa [P] using hpBound
      · have hpLarge : (h : ℤ) < P := lt_of_not_ge hpSmall
        have hqEq : q = h := by
          have hpCast : (P.toNat : ℤ) = P := Int.toNat_of_nonneg hpPos.le
          have hnatZ : (h : ℤ) ≤ (P.toNat : ℤ) := by omega
          have hnat : h ≤ P.toNat := by exact_mod_cast hnatZ
          dsimp only [q, coverDeviceQ]
          apply Nat.min_eq_right
          simpa only [P] using hnat
        have hqZ : (q : ℤ) = h := by exact_mod_cast hqEq
        have hcap := lowMu_large_p_capacity_nonneg hhZ (by positivity) hcwZ hrZ hdZ
        have hcapId := device_large_p_first_identity hpDef hqZ hwZ
        have hpCapacity : P ≤ (q * C.a1 : ℕ) := by
          exact_mod_cast (show P ≤ (q : ℤ) * C.a1 by omega)
        have hcommonId := device_large_p_common_identity
          (μ := (C.mu : ℤ)) hpDef hqZ
        have hcommonNonneg := lowMu_common_nonneg_of_a0
          hhPosZ hmu0Z ha0MuZ hmuTwoHZ
        have hcommon : P - (q : ℕ) ≤ (D.card : ℤ) - 2 * (C.mu : ℤ) := by
          omega
        have hendId := device_large_p_endpoint_identity
          (μ := (C.mu : ℤ)) hpDef hqZ
        have hendNonneg := lowMu_ha0_nonneg hhPosZ hmu0Z ha0MuZ
        have hendpoint : P + (q : ℕ) ≤ (D.card : ℤ) - (C.mu : ℤ) := by
          omega
        apply coverDevice_case_three hDX hY1 hXY0 hXY1 C.Y0_disjoint_Y1
          hcomplete hsparse
        · simpa [P] using hpPos
        · simpa [P, q] using hpCapacity
        · simpa [P, q] using hcommon
        · simpa [P, q] using hendpoint
  have hpCover : HasPathCoverOnAtMost C.G (pathSupport p : Set V) 1 := by
    refine ⟨[p], by simp, ?_⟩
    constructor
    · simpa using hp
    · intro v hv
      exact ⟨p, by simp, mem_pathSupport.mp hv⟩
  have hUnion : (pathSupport p : Set V) ∪ (D : Set V) = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hvP : v ∈ pathSupport p
    · exact Or.inl hvP
    · right
      have hvXY : v ∈ C.X ∨ v ∈ C.Y := by
        have : v ∈ C.X ∪ C.Y := by rw [C.X_union_Y]; simp
        exact Finset.mem_union.mp this
      rcases hvXY with hvX | hvY
      · exact Finset.mem_sdiff.mpr ⟨hvX, hvP⟩
      · exact (hvP (hpY v hvY)).elim
  have hAllOn : HasPathCoverOnAtMost C.G Set.univ (1 + h) := by
    simpa [hUnion] using hpCover.append hdevice
  have hcount : 1 + h = C.c := by
    change 1 + (C.c - 1) = C.c
    omega
  have hcover : HasPathCoverAtMost C.G C.c := by
    rw [hasPathCoverAtMost_iff_on_univ]
    simpa [hcount] using hAllOn
  exact C.cover_failures.1 hcover

end Configuration
end Erdos518
