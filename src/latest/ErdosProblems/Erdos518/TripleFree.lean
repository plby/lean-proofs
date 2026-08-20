/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.CliqueExtension
import ErdosProblems.Erdos518.Intersection

/-!
# The triple-free estimate

This file formalizes Claim 2 in the high-degree part of the Chen--Chen proof.  Positions on
the distinguished path are numbered from `1` to `Q.length`.  The definitions `lowerBlueSet`
and `upperBlueSet` are the sets denoted by `M_i` and `N_i` in the paper.  The sets
`betweenVertices` and `outsideReservoir` are `F₀` and `F`.

The theorem `tripleFree_estimate` separates the order-theoretic/hypergraph argument from the
two elementary cardinal estimates on `F`.  Its hypothesis `hFcard` is precisely the estimate
proved in the paper by considering whether `J` is empty.  All other parts of the claim,
including the red clique-extension contradiction, are proved here.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance tripleFreeDecidableEq : DecidableEq V := Classical.decEq V

/-- One-based positions of the complement-colour neighbours of `y` on `Q`. -/
noncomputable def blueIndices (y : V) : Finset ℕ := by
  classical
  exact (C.X.filter fun x ↦ C.Gᶜ.Adj y x).image fun x ↦ C.Q.idxOf x + 1

@[simp] lemma mem_blueIndices {y : V} {i : ℕ} :
    i ∈ C.blueIndices y ↔
      ∃ x ∈ C.X, C.Gᶜ.Adj y x ∧ C.Q.idxOf x + 1 = i := by
  classical
  simp [blueIndices, and_assoc]

lemma blueIndices_card (y : V) : (C.blueIndices y).card = C.blueDegreeToX y := by
  classical
  rw [blueIndices, Finset.card_image_iff.mpr]
  · rfl
  · intro x hx z hz heq
    have hxQ : x ∈ C.Q := C.mem_X.mp (Finset.mem_filter.mp hx).1
    have hzQ : z ∈ C.Q := C.mem_X.mp (Finset.mem_filter.mp hz).1
    have hidx : C.Q.idxOf x = C.Q.idxOf z := Nat.add_right_cancel heq
    exact (List.idxOf_inj hxQ).mp hidx

lemma blueIndex_le_length {y : V} {i : ℕ} (hi : i ∈ C.blueIndices y) :
    i ≤ C.Q.length := by
  obtain ⟨x, hx, -, rfl⟩ := C.mem_blueIndices.mp hi
  have hxQ : x ∈ C.Q := C.mem_X.mp hx
  exact List.idxOf_lt_length_iff.mpr hxQ

/-- A vertex is high when its blue degree into `X` is at least `(r+1)/2`. -/
def IsHigh (y : V) : Prop := C.r + 1 ≤ 2 * C.blueDegreeToX y

/-- An oriented blue triple.  The middle vertex has two neighbours at positions `beta` and
`gamma`; the other two vertices have neighbours weakly outside that interval. -/
def OrderedBlueTriple (u m v : V) : Prop :=
  ∃ alpha ∈ C.blueIndices u, ∃ beta ∈ C.blueIndices m,
    ∃ gamma ∈ C.blueIndices m, ∃ delta ∈ C.blueIndices v,
      alpha ≤ beta ∧ beta < gamma ∧ gamma ≤ delta

/-- No three distinct members of `Y'`, in any assignment of their three roles, form an
ordered blue triple. -/
def TripleFreeOn (Y' : Finset V) : Prop :=
  ∀ u ∈ Y', ∀ m ∈ Y', ∀ v ∈ Y',
    u ≠ m → u ≠ v → m ≠ v → ¬ C.OrderedBlueTriple u m v

/-- `M_k`: vertices other than `s` having a blue neighbour at a position at most `k`. -/
noncomputable def lowerBlueSet (Y' : Finset V) (s : V) (k : ℕ) : Finset V := by
  classical
  exact (Y'.erase s).filter fun y ↦ ∃ i ∈ C.blueIndices y, i ≤ k

/-- `N_k`: vertices other than `s` having a blue neighbour at a position at least `k`. -/
noncomputable def upperBlueSet (Y' : Finset V) (s : V) (k : ℕ) : Finset V := by
  classical
  exact (Y'.erase s).filter fun y ↦ ∃ i ∈ C.blueIndices y, k ≤ i

/-- `J = Y' \ (M_k ∪ {s})`. -/
noncomputable def middleOutsideSet (Y' : Finset V) (s : V) (k : ℕ) : Finset V := by
  classical
  exact Y' \ (C.lowerBlueSet Y' s k ∪ {s})

/-- `F₀`: vertices of `Q` whose one-based positions lie strictly between the two boundary
positions. -/
noncomputable def betweenVertices (lo hi : ℕ) : Finset V := by
  classical
  exact C.X.filter fun x ↦ lo < C.Q.idxOf x + 1 ∧ C.Q.idxOf x + 1 < hi

/-- `F = (X \ S_s) \ F₀`, the reservoir outside the predecessor clique and middle
interval. -/
noncomputable def outsideReservoir (S : Finset V) (lo hi : ℕ) : Finset V := by
  classical
  exact (C.X \ S) \ C.betweenVertices lo hi

/-- The source-exact `F₀`: it is the middle interval when `J` is nonempty and is empty
when `J` is empty. -/
noncomputable def tripleFreeF0 (Y' : Finset V) (s : V) (lo hi : ℕ) : Finset V := by
  classical
  exact if (C.middleOutsideSet Y' s lo).Nonempty then C.betweenVertices lo hi else ∅

/-- The source-exact reservoir `F = (X \ S_s) \ F₀`. -/
noncomputable def tripleFreeF
    (Y' S : Finset V) (s : V) (lo hi : ℕ) : Finset V := by
  classical
  exact (C.X \ S) \ C.tripleFreeF0 Y' s lo hi

@[simp] lemma mem_lowerBlueSet {Y' : Finset V} {s y : V} {k : ℕ} :
    y ∈ C.lowerBlueSet Y' s k ↔
      y ∈ Y' ∧ y ≠ s ∧ ∃ i ∈ C.blueIndices y, i ≤ k := by
  classical
  simp only [lowerBlueSet, Finset.mem_filter, Finset.mem_erase]
  aesop

@[simp] lemma mem_upperBlueSet {Y' : Finset V} {s y : V} {k : ℕ} :
    y ∈ C.upperBlueSet Y' s k ↔
      y ∈ Y' ∧ y ≠ s ∧ ∃ i ∈ C.blueIndices y, k ≤ i := by
  classical
  simp only [upperBlueSet, Finset.mem_filter, Finset.mem_erase]
  aesop

@[simp] lemma mem_middleOutsideSet {Y' : Finset V} {s y : V} {k : ℕ} :
    y ∈ C.middleOutsideSet Y' s k ↔
      y ∈ Y' ∧ y ∉ C.lowerBlueSet Y' s k ∧ y ≠ s := by
  classical
  simp only [middleOutsideSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
  aesop

@[simp] lemma mem_betweenVertices {x : V} {lo hi : ℕ} :
    x ∈ C.betweenVertices lo hi ↔
      x ∈ C.X ∧ lo < C.Q.idxOf x + 1 ∧ C.Q.idxOf x + 1 < hi := by
  classical
  simp [betweenVertices, and_assoc]

@[simp] lemma mem_outsideReservoir {S : Finset V} {x : V} {lo hi : ℕ} :
    x ∈ C.outsideReservoir S lo hi ↔
      x ∈ C.X ∧ x ∉ S ∧ x ∉ C.betweenVertices lo hi := by
  classical
  simp [outsideReservoir, and_assoc]

lemma tripleFreeF0_eq_between_of_nonempty
    {Y' : Finset V} {s : V} {lo hi : ℕ}
    (hJ : (C.middleOutsideSet Y' s lo).Nonempty) :
    C.tripleFreeF0 Y' s lo hi = C.betweenVertices lo hi := by
  classical
  simp [tripleFreeF0, hJ]

lemma tripleFreeF0_eq_empty_of_not_nonempty
    {Y' : Finset V} {s : V} {lo hi : ℕ}
    (hJ : ¬ (C.middleOutsideSet Y' s lo).Nonempty) :
    C.tripleFreeF0 Y' s lo hi = ∅ := by
  classical
  simp [tripleFreeF0, hJ]

@[simp] lemma mem_tripleFreeF {Y' S : Finset V} {s x : V} {lo hi : ℕ} :
    x ∈ C.tripleFreeF Y' S s lo hi ↔
      x ∈ C.X ∧ x ∉ S ∧ x ∉ C.tripleFreeF0 Y' s lo hi := by
  classical
  simp [tripleFreeF, and_assoc]

/-- Two vertices in a lower set let triple-freeness exclude every vertex in the corresponding
upper set.  This is the `M_{e+1}`/`N_{e+2}` argument in Claim 2. -/
lemma upperBlueSet_eq_empty_of_two_lower
    {Y' : Finset V} {s : V} {mid hi : ℕ}
    (hs : s ∈ Y') (hfree : C.TripleFreeOn Y')
    (hmid : mid ∈ C.blueIndices s) (hhi : hi ∈ C.blueIndices s)
    (hmh : mid < hi) (hM : 2 ≤ (C.lowerBlueSet Y' s mid).card) :
    C.upperBlueSet Y' s hi = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz' := C.mem_upperBlueSet.mp hz
  obtain ⟨delta, hdelta, hhidelta⟩ := hz'.2.2
  have hex : ∃ u ∈ C.lowerBlueSet Y' s mid, u ≠ z := by
    by_contra h
    push_neg at h
    have hsub : C.lowerBlueSet Y' s mid ⊆ {z} := by
      intro u hu
      simpa [h u hu]
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨u, hu, huz⟩ := hex
  have hu' := C.mem_lowerBlueSet.mp hu
  obtain ⟨alpha, halpha, halphamid⟩ := hu'.2.2
  have hus : u ≠ s := hu'.2.1
  have hzs : z ≠ s := hz'.2.1
  have hnot := hfree u hu'.1 s hs z hz'.1 hus huz (Ne.symm hzs)
  apply hnot
  exact ⟨alpha, halpha, mid, hmid, hi, hhi, delta, hdelta,
    halphamid, hmh, hhidelta⟩

/-- No blue index lies beyond the right sentinel `Q.length + 1`. -/
lemma upperBlueSet_eq_empty_of_sentinel {Y' : Finset V} {s : V} :
    C.upperBlueSet Y' s (C.Q.length + 1) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨-, -, i, hi, hlen⟩ := C.mem_upperBlueSet.mp hy
  have := C.blueIndex_le_length hi
  omega

/-- The two alternatives for the boundary `k_{e+2}` in the paper: it is either the right
sentinel, or it and the preceding boundary are consecutive blue positions of `s` and the
preceding lower set has size at least two. -/
def HasUpperBoundaryWitness (Y' : Finset V) (s : V) (hi : ℕ) : Prop :=
  hi = C.Q.length + 1 ∨
    ∃ mid, mid ∈ C.blueIndices s ∧ hi ∈ C.blueIndices s ∧ mid < hi ∧
      2 ≤ (C.lowerBlueSet Y' s mid).card

lemma upperBlueSet_eq_empty_of_boundaryWitness
    {Y' : Finset V} {s : V} {hi : ℕ} (hs : s ∈ Y')
    (hfree : C.TripleFreeOn Y') (hwit : C.HasUpperBoundaryWitness Y' s hi) :
    C.upperBlueSet Y' s hi = ∅ := by
  rcases hwit with rfl | ⟨mid, hmid, hhi, hlt, htwo⟩
  · exact C.upperBlueSet_eq_empty_of_sentinel
  · exact C.upperBlueSet_eq_empty_of_two_lower hs hfree hmid hhi hlt htwo

/-- Removing `M_e` and `s` loses at most two vertices. -/
lemma card_sub_two_le_middleOutsideSet
    {Y' : Finset V} {s : V} {lo : ℕ} (hs : s ∈ Y')
    (hM : (C.lowerBlueSet Y' s lo).card ≤ 1) :
    Y'.card - 2 ≤ (C.middleOutsideSet Y' s lo).card := by
  classical
  let M := C.lowerBlueSet Y' s lo
  have hMsub : M ⊆ Y' := by
    intro y hy
    exact (C.mem_lowerBlueSet.mp hy).1
  have hsM : s ∉ M := by
    intro h
    exact (C.mem_lowerBlueSet.mp h).2.1 rfl
  have hsub : M ∪ {s} ⊆ Y' := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hMsub hy
    · exact Finset.mem_singleton.mp hy ▸ hs
  have hdis : Disjoint M ({s} : Finset V) := by
    rw [Finset.disjoint_singleton_right]
    exact hsM
  have hcardUnion : (M ∪ {s}).card = M.card + 1 := by
    simpa using Finset.card_union_of_disjoint hdis
  have hcardJ : (C.middleOutsideSet Y' s lo).card = Y'.card - (M ∪ {s}).card := by
    simpa [middleOutsideSet, M] using Finset.card_sdiff_of_subset hsub
  rw [hcardJ, hcardUnion]
  have hM' : M.card ≤ 1 := by simpa [M] using hM
  omega

/-- A vertex in `J` has all of its blue neighbours in the middle interval.  Hence every edge
from `J` to `F` is red. -/
lemma adj_middleOutside_outsideReservoir
    {Y' S : Finset V} {s y x : V} {lo hi : ℕ}
    (hY' : Y' ⊆ C.Y1) (hupper : C.upperBlueSet Y' s hi = ∅)
    (hy : y ∈ C.middleOutsideSet Y' s lo)
    (hx : x ∈ C.outsideReservoir S lo hi) :
    C.G.Adj y x := by
  classical
  have hy' := C.mem_middleOutsideSet.mp hy
  have hx' := C.mem_outsideReservoir.mp hx
  have hyY : y ∈ C.Y := C.Y1_subset_Y (hY' hy'.1)
  have hyX : y ∉ C.X := C.mem_Y.mp hyY
  have hne : y ≠ x := fun h ↦ hyX (h.symm ▸ hx'.1)
  by_contra hred
  have hblue : C.Gᶜ.Adj y x := (SimpleGraph.compl_adj C.G y x).2 ⟨hne, hred⟩
  let i := C.Q.idxOf x + 1
  have hiBlue : i ∈ C.blueIndices y :=
    C.mem_blueIndices.mpr ⟨x, hx'.1, hblue, rfl⟩
  have hlo : lo < i := by
    by_contra h
    have hile : i ≤ lo := Nat.le_of_not_gt h
    exact hy'.2.1 (C.mem_lowerBlueSet.mpr ⟨hy'.1, hy'.2.2, i, hiBlue, hile⟩)
  have hhi : i < hi := by
    by_contra h
    have hhii : hi ≤ i := Nat.le_of_not_gt h
    have hymem : y ∈ C.upperBlueSet Y' s hi :=
      C.mem_upperBlueSet.mpr ⟨hy'.1, hy'.2.2, i, hiBlue, hhii⟩
    simpa [hupper] using hymem
  exact hx'.2.2 (C.mem_betweenVertices.mpr ⟨hx'.1, hlo, hhi⟩)

/-- Vertices in `Y₀` have no blue edge to `X`, so in particular all their edges to `F`
are red. -/
lemma adj_Y0_outsideReservoir
    {S : Finset V} {y x : V} {lo hi : ℕ}
    (hy : y ∈ C.Y0) (hx : x ∈ C.outsideReservoir S lo hi) :
    C.G.Adj y x := by
  classical
  have hxX := (C.mem_outsideReservoir.mp hx).1
  have hyY := C.Y0_subset_Y hy
  have hyX : y ∉ C.X := C.mem_Y.mp hyY
  have hne : y ≠ x := fun h ↦ hyX (h.symm ▸ hxX)
  by_contra hred
  have hblue : C.Gᶜ.Adj y x := (SimpleGraph.compl_adj C.G y x).2 ⟨hne, hred⟩
  have hpos : 0 < C.blueDegreeToX y := by
    simpa [blueDegreeToX] using
      (Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxX, hblue⟩⟩)
  rw [(C.mem_Y0.mp hy).2] at hpos
  omega

lemma adj_middleOutside_tripleFreeF
    {Y' S : Finset V} {s y x : V} {lo hi : ℕ}
    (hY' : Y' ⊆ C.Y1) (hupper : C.upperBlueSet Y' s hi = ∅)
    (hy : y ∈ C.middleOutsideSet Y' s lo)
    (hx : x ∈ C.tripleFreeF Y' S s lo hi) :
    C.G.Adj y x := by
  classical
  have hJ : (C.middleOutsideSet Y' s lo).Nonempty := ⟨y, hy⟩
  have hx' := C.mem_tripleFreeF.mp hx
  have hxOld : x ∈ C.outsideReservoir S lo hi := by
    apply C.mem_outsideReservoir.mpr
    refine ⟨hx'.1, hx'.2.1, ?_⟩
    rw [← C.tripleFreeF0_eq_between_of_nonempty hJ]
    exact hx'.2.2
  exact C.adj_middleOutside_outsideReservoir hY' hupper hy hxOld

lemma adj_Y0_X {y x : V} (hy : y ∈ C.Y0) (hx : x ∈ C.X) : C.G.Adj y x := by
  classical
  have hyY := C.Y0_subset_Y hy
  have hyX : y ∉ C.X := C.mem_Y.mp hyY
  have hne : y ≠ x := fun h ↦ hyX (h.symm ▸ hx)
  by_contra hred
  have hblue : C.Gᶜ.Adj y x := (SimpleGraph.compl_adj C.G y x).2 ⟨hne, hred⟩
  have hpos : 0 < C.blueDegreeToX y := by
    simpa [blueDegreeToX] using
      (Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hblue⟩⟩)
  rw [(C.mem_Y0.mp hy).2] at hpos
  omega

private lemma forall₂_of_cross {A B : Type*} {R : A → B → Prop}
    {as : List A} {bs : List B} (hlen : as.length = bs.length)
    (hcross : ∀ a ∈ as, ∀ b ∈ bs, R a b) :
    List.Forall₂ R as bs := by
  induction as generalizing bs with
  | nil =>
      have : bs = [] := by simpa using hlen.symm
      subst bs
      exact .nil
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          apply List.Forall₂.cons
          · exact hcross a (by simp) b (by simp)
          · apply ih (by simpa using hlen)
            intro a' ha' b' hb'
            exact hcross a' (by simp [ha']) b' (by simp [hb'])

/-- Claim 2 (triple-free estimate), in configuration form.

`S` is the predecessor clique `S_s`, `lo = k_e`, and `hi = k_{e+2}`.  The two hypotheses
`hFempty` and `hFnonempty` are exactly the numerical reservoir estimates in the two cases
`J = ∅` and `J ≠ ∅`. -/
theorem tripleFree_estimate
    {Y' S : Finset V} {s e : V} {lo hi : ℕ}
    (hY' : Y' ⊆ C.Y1) (hs : s ∈ Y') (hfree : C.TripleFreeOn Y')
    (hwit : C.HasUpperBoundaryWitness Y' s hi)
    (hM : (C.lowerBlueSet Y' s lo).card ≤ 1)
    (hSclique : C.G.IsClique (S : Set V)) (heS : e ∈ S) (hSX : S ⊆ C.X)
    (hScard : S.card = C.blueDegreeToX s + 1)
    (hbridge : ∀ y ∈ C.Y, C.G.Adj e y)
    (hhigh : C.IsHigh s)
    (hmu : C.blueDegreeToX s + 2 ≤ C.r)
    (hFempty : ¬ (C.middleOutsideSet Y' s lo).Nonempty →
      C.r - C.blueDegreeToX s ≤ (C.tripleFreeF Y' S s lo hi).card)
    (hFnonempty : (C.middleOutsideSet Y' s lo).Nonempty →
      C.blueDegreeToX s - 1 ≤ (C.tripleFreeF Y' S s lo hi).card) :
    C.a0 + (Y'.card - 2) < C.r - C.blueDegreeToX s := by
  classical
  let muS := C.blueDegreeToX s
  let a := C.r - muS
  let J := C.middleOutsideSet Y' s lo
  let F := C.tripleFreeF Y' S s lo hi
  let U := J ∪ C.Y0
  have hupper : C.upperBlueSet Y' s hi = ∅ :=
    C.upperBlueSet_eq_empty_of_boundaryWitness hs hfree hwit
  have hJsubY1 : J ⊆ C.Y1 := by
    intro y hy
    exact hY' (C.mem_middleOutsideSet.mp hy).1
  have hJY0 : Disjoint J C.Y0 := by
    rw [Finset.disjoint_left]
    intro y hyJ hy0
    exact Finset.disjoint_left.mp C.Y0_disjoint_Y1 hy0 (hJsubY1 hyJ)
  have hJcard : Y'.card - 2 ≤ J.card := by
    exact C.card_sub_two_le_middleOutsideSet hs hM
  have hUcard : U.card = J.card + C.a0 := by
    simpa [U, a0] using Finset.card_union_of_disjoint hJY0
  have hmuR : muS ≤ C.r := by omega
  have haPos : 0 < a := by omega
  by_contra hclaim
  have hclaim' : a ≤ C.a0 + (Y'.card - 2) := Nat.le_of_not_gt hclaim
  have haU : a ≤ U.card := by
    calc
      a ≤ C.a0 + (Y'.card - 2) := hclaim'
      _ ≤ C.a0 + J.card := Nat.add_le_add_left hJcard C.a0
      _ = U.card := by omega
  obtain ⟨A, hAU, hAcard⟩ := Finset.exists_subset_card_eq haU
  have haF : a ≤ F.card := by
    by_cases hJne : J.Nonempty
    · have hhigh' : a ≤ muS - 1 := by
        dsimp only [IsHigh] at hhigh
        dsimp only [a, muS]
        omega
      exact hhigh'.trans (by simpa only [J, F, muS] using hFnonempty hJne)
    · simpa only [a, J, F, muS] using hFempty hJne
  obtain ⟨B, hBF, hBcard⟩ : ∃ B : Finset V, B ⊆ F ∧ B.card = a :=
    Finset.exists_subset_card_eq haF
  let ys := A.toList
  let xs := B.toList
  have hysLen : ys.length = a := by simp [ys, hAcard]
  have hxsLen : xs.length = a := by simp [xs, hBcard]
  have hys0 : ys ≠ [] := by
    intro h
    have : ys.length = 0 := by simp [h]
    omega
  have hysN : ys.Nodup := by exact A.nodup_toList
  have hxsN : xs.Nodup := by exact B.nodup_toList
  have hUsubY : U ⊆ C.Y := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyJ | hy0
    · exact C.Y1_subset_Y (hJsubY1 hyJ)
    · exact C.Y0_subset_Y hy0
  have hysY : ∀ y ∈ ys, y ∈ C.Y := by
    intro y hy
    exact hUsubY (hAU (by simpa [ys] using hy))
  have hxsF : ∀ x ∈ xs, x ∈ F := by
    intro x hx
    exact hBF (by simpa [xs] using hx)
  have hxsX : ∀ x ∈ xs, x ∈ C.X := by
    intro x hx
    exact (C.mem_tripleFreeF.mp (hxsF x hx)).1
  have hysX : ∀ y ∈ ys, y ∉ C.X := by
    intro y hy
    exact C.mem_Y.mp (hysY y hy)
  have hysOut : ∀ y ∈ ys, y ∉ S := by
    intro y hy hyS
    exact hysX y hy (hSX hyS)
  have hxsOut : ∀ x ∈ xs, x ∉ S := by
    intro x hx
    exact (C.mem_tripleFreeF.mp (hxsF x hx)).2.1
  have hyxDisj : List.Disjoint ys xs := by
    rw [List.disjoint_left]
    intro v hvy hvx
    exact hysX v hvy (hxsX v hvx)
  have hcross : ∀ y ∈ ys, ∀ x ∈ xs, C.G.Adj y x := by
    intro y hy x hx
    have hyU : y ∈ U := hAU (by simpa [ys] using hy)
    rcases Finset.mem_union.mp hyU with hyJ | hy0
    · exact C.adj_middleOutside_tripleFreeF hY' hupper hyJ (hxsF x hx)
    · exact C.adj_Y0_X hy0 (hxsX x hx)
  have hyx : List.Forall₂ C.G.Adj ys xs := by
    exact forall₂_of_cross (hysLen.trans hxsLen.symm) hcross
  have hxy : List.Forall₂ C.G.Adj xs.dropLast ys.tail := by
    apply forall₂_of_cross
    · simp only [List.length_dropLast, List.length_tail, hxsLen, hysLen]
    · intro x hx y hy
      exact (hcross y (List.mem_of_mem_tail hy) x (List.mem_of_mem_dropLast hx)).symm
  have heFirst : C.G.Adj e (ys.head hys0) := by
    apply hbridge
    · exact hysY _ (List.head_mem hys0)
  have hp : IsPath C.G (cliqueExtension S e ys xs) :=
    isPath_cliqueExtension hSclique heS hys0 hysN hxsN hyxDisj
      hysOut hxsOut hyx hxy heFirst
  have hinter := cliqueExtension_inter_card (S := S) (X := C.X)
    heS hxsN hxsOut hSX hxsX hysX
  have hinter' :
      ((cliqueExtension S e ys xs).toFinset ∩ C.X).card = C.r + 1 := by
    rw [hinter, hScard, hxsLen]
    dsimp only [muS, a]
    omega
  have hQsupport : pathSupport C.Q = C.X := by
    rfl
  have hP_support : pathSupport (cliqueExtension S e ys xs) =
      (cliqueExtension S e ys xs).toFinset := rfl
  apply C.not_r_add_one_le_path_inter_Q hp
  rw [hP_support, hQsupport, hinter']

end Configuration
end Erdos518
