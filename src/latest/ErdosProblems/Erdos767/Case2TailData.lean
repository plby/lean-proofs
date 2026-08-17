import ErdosProblems.Erdos767.Case2Assembly

open Finset
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The neighbor-index and actual tail-segment data used in the unequal-ear
branch of the aligned-fan splice. -/
structure Case2TailData (B : BestLollipop G) {j₁ : ℕ}
    (D : Case2FanData B j₁) where
  j' : ℕ
  j'_mem : j' ∈ E767WalkIndex.endNeighborIndices B.tail
  j'_lt : j' < D.j₂
  greatest : ∀ t ∈ E767WalkIndex.endNeighborIndices B.tail,
    t < D.j₂ → t ≤ j'
  A : G.Walk D.E₁.b (B.tail.getVert j')
  A_isPath : A.IsPath
  A_length : A.length = j' - j₁
  T : G.Walk (B.tail.getVert D.j₂) B.terminal
  T_isPath : T.IsPath
  T_length : T.length = B.tail.length - D.j₂
  chord : G.Adj (B.tail.getVert j') B.terminal
  degree_le : G.degree B.terminal ≤ A.length + 1 + T.length
  A_support_indices : ∀ v, v ∈ A.support →
    ∃ t, j₁ ≤ t ∧ t ≤ j' ∧ B.tail.getVert t = v
  T_support_indices : ∀ v, v ∈ T.support →
    ∃ t, D.j₂ ≤ t ∧ t ≤ B.tail.length ∧
      B.tail.getVert t = v

/-- Choose the greatest terminal-neighbor index below the second ear's first
suffix hit.  The two actual tail intervals contain enough vertices to pay
for every neighbor of the terminal. -/
theorem Case2FanData.exists_tailData
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁)
    (hj₁J : j₁ ∈ E767WalkIndex.endNeighborIndices B.tail)
    (hN : G.neighborFinset B.terminal ⊆ B.tail.support.toFinset) :
    Nonempty (Case2TailData B D) := by
  let J := E767WalkIndex.endNeighborIndices B.tail
  let L := J.filter fun t ↦ t < D.j₂
  have hj₁L : j₁ ∈ L := by
    simp only [L, Finset.mem_filter]
    exact ⟨hj₁J, D.j₁_lt_j₂⟩
  have hL : L.Nonempty := ⟨j₁, hj₁L⟩
  let j' := L.max' hL
  have hj'L : j' ∈ L := Finset.max'_mem L hL
  have hj'J : j' ∈ J := (Finset.mem_filter.mp hj'L).1
  have hj'lt : j' < D.j₂ := (Finset.mem_filter.mp hj'L).2
  have hgreatest : ∀ t ∈ J, t < D.j₂ → t ≤ j' := by
    intro t htJ htlt
    exact Finset.le_max' L t (Finset.mem_filter.mpr ⟨htJ, htlt⟩)
  have hj₁j' : j₁ ≤ j' := hgreatest j₁ hj₁J D.j₁_lt_j₂
  have hj'le : j' ≤ B.tail.length := by
    have := (E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp
      hj'J |>.1
    omega
  let A₀ : G.Walk (B.tail.getVert j₁)
      ((B.tail.drop j₁).getVert (j' - j₁)) :=
    (B.tail.drop j₁).take (j' - j₁)
  have hAend : (B.tail.drop j₁).getVert (j' - j₁) =
      B.tail.getVert j' := by
    simp [Walk.drop_getVert, Nat.add_sub_of_le hj₁j']
  let A : G.Walk D.E₁.b (B.tail.getVert j') :=
    A₀.copy D.b₁_eq.symm hAend
  have hApath : A.IsPath := by
    simpa [A, A₀, Walk.support_copy] using
      (B.tail_isPath.drop j₁ |>.take (j' - j₁))
  have hAlen : A.length = j' - j₁ := by
    simp [A, A₀, Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  let T : G.Walk (B.tail.getVert D.j₂) B.terminal := B.tail.drop D.j₂
  have hTpath : T.IsPath := B.tail_isPath.drop D.j₂
  have hTlen : T.length = B.tail.length - D.j₂ := by simp [T]
  have hchord : G.Adj (B.tail.getVert j') B.terminal := by
    exact ((E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp
      hj'J).2.symm
  have hdegree : G.degree B.terminal ≤ A.length + 1 + T.length := by
    let Low := J.filter fun t ↦ t < D.j₂
    let High := J.filter fun t ↦ D.j₂ ≤ t
    have hJsub : J ⊆ Low ∪ High := by
      intro t ht
      by_cases hlt : t < D.j₂
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, hlt⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨ht, Nat.le_of_not_gt hlt⟩)
    have hLow : Low ⊆ Finset.Icc j₁ j' := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      have hj₁t : j₁ ≤ t := D.j₁_min t ht'.1
      exact Finset.mem_Icc.mpr ⟨hj₁t, hgreatest t ht'.1 ht'.2⟩
    have hHigh : High ⊆ Finset.Ico D.j₂ B.tail.length := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      have htell :=
        (E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp
          ht'.1 |>.1
      exact Finset.mem_Ico.mpr ⟨ht'.2, htell⟩
    have hcard : J.card ≤ (j' - j₁ + 1) +
        (B.tail.length - D.j₂) := by
      calc
        J.card ≤ (Low ∪ High).card := Finset.card_le_card hJsub
        _ ≤ Low.card + High.card := Finset.card_union_le _ _
        _ ≤ (Finset.Icc j₁ j').card +
            (Finset.Ico D.j₂ B.tail.length).card :=
          Nat.add_le_add (Finset.card_le_card hLow) (Finset.card_le_card hHigh)
        _ = (j' - j₁ + 1) + (B.tail.length - D.j₂) := by
          rw [Nat.card_Icc, Nat.card_Ico]
          omega
    have hJcard := E767WalkIndex.card_endNeighborIndices_eq_degree
      B.tail_isPath hN
    rw [← hJcard]
    rw [hAlen, hTlen]
    omega
  have hAsupp : ∀ v, v ∈ A.support →
      ∃ t, j₁ ≤ t ∧ t ≤ j' ∧ B.tail.getVert t = v := by
    intro v hv
    have hv₀ : v ∈ A₀.support := by simpa [A] using hv
    obtain ⟨r, hrv, hrle⟩ := Walk.mem_support_iff_exists_getVert.mp hv₀
    have hrle' : r ≤ j' - j₁ := by
      have hA₀len : A₀.length = (j' - j₁) ⊓ (B.tail.length - j₁) := by
        simp [A₀, Walk.drop_length]
      rw [hA₀len] at hrle
      omega
    refine ⟨j₁ + r, by omega, by omega, ?_⟩
    simpa [A₀, Walk.take_getVert, min_eq_right hrle', Walk.drop_getVert]
      using hrv
  have hTsupp : ∀ v, v ∈ T.support →
      ∃ t, D.j₂ ≤ t ∧ t ≤ B.tail.length ∧
        B.tail.getVert t = v := by
    intro v hv
    obtain ⟨r, hrv, hrle⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    have hbound : D.j₂ + r ≤ B.tail.length := by
      have hTlen' : T.length = B.tail.length - D.j₂ := by simp [T]
      rw [hTlen'] at hrle
      have hj₂le := D.j₂_le
      omega
    refine ⟨D.j₂ + r, by omega, hbound, ?_⟩
    simpa [T, Walk.drop_getVert] using hrv
  exact ⟨{
    j' := j'
    j'_mem := hj'J
    j'_lt := hj'lt
    greatest := hgreatest
    A := A
    A_isPath := hApath
    A_length := hAlen
    T := T
    T_isPath := hTpath
    T_length := hTlen
    chord := hchord
    degree_le := hdegree
    A_support_indices := hAsupp
    T_support_indices := hTsupp }⟩

end

end E767DiracBuild
