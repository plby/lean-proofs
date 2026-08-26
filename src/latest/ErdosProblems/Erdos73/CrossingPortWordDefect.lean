import ErdosProblems.Erdos73.AntipodalPortDefect
import ErdosProblems.Erdos73.PairedBoundaryOrder
import ErdosProblems.Erdos73.HandleBottomMargin
import ErdosProblems.Erdos73.CrossingHandleExtraction
import ErdosProblems.Erdos73.MonochromaticPathParity

/-! Apply a high-defect noncrossing port word to the actual crossing handle families. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {V U : Type*} [Fintype V] [Fintype U] [LinearOrder U]
variable {G : SimpleGraph V} {c rows N : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c rows) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem defect_of_sameSide_port_word (F : ColumnHandleFamily S col (Fin N))
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (side : Bool) (hc : 2 * N + 2 ≤ c) (hr : side = false → Odd rows)
    (hrow : ∀ i, (F.sourceNail i).val.1.val < (F.targetNail i).val.1.val)
    (hs : ∀ i, if side then (F.sourceNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (F.sourceNail i).val.2.val)
    (ht : ∀ i, if side then (F.targetNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (F.targetNail i).val.2.val)
    (hcross : ∀ i j, i < j → (F.sourceNail i).val.1.val < (F.sourceNail j).val.1.val ∧
      (F.sourceNail j).val.1.val < (F.targetNail i).val.1.val ∧
      (F.targetNail i).val.1.val < (F.targetNail j).val.1.val)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (d : ℕ)
    (hF : 2 * (antipodalPortGraph label).indepNum + d ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast d G := by
  let nails := pairedPorts F.sourceNail F.targetNail
  have hmono := sameSide_paired_rows_strictMono F.sourceNail F.targetNail hrow hcross
  have hPs (i : Fin N) : (F.path i).source = S.branchVertex (nails (firstPort i)) := by
    rw [show nails (firstPort i) = F.sourceNail i from pairedPorts_first _ _ _]
    exact F.source_eq i
  have hPt (i : Fin N) : (F.path i).target = S.branchVertex (nails (secondPort i)) := by
    rw [show nails (secondPort i) = F.targetNail i from pairedPorts_second _ _ _]
    exact F.target_eq i
  have hside (i : Fin (2 * N)) :
      if side then (nails i).val.2.val ≤ 1 else 2 * (c - 1) ≤ (nails i).val.2.val := by
    rcases pairedPorts_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simpa only [nails, pairedPorts_first] using hs j
    · simpa only [nails, pairedPorts_second] using ht j
  cases side
  · exact hasIndependenceDefectAtLeast_of_right_antipodal_word S col b hb label hsurj hNC
      nails hmono hside hc (hr rfl) F.path hPs hPt (F.odd_paths_of_monochromaticBranches b hb)
      F.disjoint (fun i => (F.clean i).internal_disjoint) d hF
  · exact hasIndependenceDefectAtLeast_of_left_antipodal_word S col b hb label hsurj hNC
      nails hmono hside hc F.path hPs hPt (F.odd_paths_of_monochromaticBranches b hb)
      F.disjoint (fun i => (F.clean i).internal_disjoint) d hF

theorem defect_of_through_port_word (F : ColumnHandleFamily S col (Fin N))
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (L : ℕ) (hc : 4 * N + 3 ≤ c) (hr : uCombBase L (2 * N) < rows)
    (hrows : ∀ i, (F.sourceNail i).val.1.val ≤ L ∧ (F.targetNail i).val.1.val ≤ L)
    (hs : ∀ i, (F.sourceNail i).val.2.val ≤ 1)
    (ht : ∀ i, 2 * (c - 1) ≤ (F.targetNail i).val.2.val)
    (hcross : ∀ i j, i < j → (F.sourceNail i).val.1.val < (F.sourceNail j).val.1.val ∧
      (F.targetNail j).val.1.val < (F.targetNail i).val.1.val)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (d : ℕ)
    (hF : 2 * (antipodalPortGraph label).indepNum + d ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast d G := by
  let nails := pairedPorts F.sourceNail F.targetNail
  have hmono := through_paired_rank_strictMono F.sourceNail F.targetNail
    (fun _ _ hij => (hcross _ _ hij).1) (fun _ _ hij => (hcross _ _ hij).2)
    (fun i => (hrows i).1) (fun i => (hrows i).2)
  apply hasIndependenceDefectAtLeast_of_boundary_antipodal_word S col b hb label hsurj hNC
    nails throughPortSides L hmono (fun i => ?_) (fun i hi => ?_) (fun i hi => ?_)
    (by omega) hr F.path (fun i => ?_) (fun i => ?_)
    (F.odd_paths_of_monochromaticBranches b hb) F.disjoint
    (fun i => (F.clean i).internal_disjoint) d hF
  · rcases pairedPorts_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simpa only [nails, pairedPorts_first] using (hrows j).1
    · simpa only [nails, pairedPorts_second] using (hrows j).2
  · rcases pairedPorts_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simpa only [nails, pairedPorts_first] using hs j
    · simp only [throughPortSides, pairedPorts_second, Bool.false_eq_true] at hi
  · rcases pairedPorts_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [throughPortSides, pairedPorts_first, Bool.true_eq_false] at hi
    · simpa only [nails, pairedPorts_second] using ht j
  · rw [show nails (firstPort i) = F.sourceNail i from pairedPorts_first _ _ _]
    exact F.source_eq i
  · rw [show nails (secondPort i) = F.targetNail i from pairedPorts_second _ _ _]
    exact F.target_eq i

theorem defect_of_large_through_crossing {K : ℕ}
    (hhandles : HasThroughCrossingHandles (S := S) (col := col) K)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (hN : 0 < N) (hK : N + (4 * N + 3) ≤ K) (hc : 4 * N + 3 ≤ c)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (d : ℕ)
    (hF : 2 * (antipodalPortGraph label).indepNum + d ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast d G := by
  obtain ⟨F, hdis, hs, ht, hcross⟩ := hhandles
  obtain ⟨f, hf, hbound⟩ := F.exists_ordered_avoiding_bottom hdis N (4 * N + 3) hK
  let E := F.reindex f hf.injective
  let L := rows - (4 * N + 3) - 1
  have hrows : ∀ i, (E.sourceNail i).val.1.val ≤ L ∧ (E.targetNail i).val.1.val ≤ L := by
    intro i
    have hi := hbound i
    change (F.sourceNail (f i)).val.1.val ≤ L ∧ (F.targetNail (f i)).val.1.val ≤ L
    dsimp only [L]
    omega
  have hr : uCombBase L (2 * N) < rows := by
    have hh := hbound ⟨0, hN⟩
    dsimp only [uCombBase, L]
    omega
  exact E.defect_of_through_port_word b hb L hc hr hrows
    (fun i => hs (f i)) (fun i => ht (f i)) (fun i j hij => hcross _ _ (hf hij))
    label hsurj hNC d hF

theorem defect_of_large_sameSide_crossing {K : ℕ} (side : Bool)
    (hhandles : HasSameSideCrossingHandles (S := S) (col := col) side K)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (hK : N ≤ K) (hc : 2 * N + 2 ≤ c) (hr : side = false → Odd rows)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (d : ℕ)
    (hF : 2 * (antipodalPortGraph label).indepNum + d ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast d G := by
  obtain ⟨F, _, hrow, hs, ht, hcross⟩ := hhandles
  let f (i : Fin N) : Fin K := ⟨i.val, i.isLt.trans_le hK⟩
  have hf : StrictMono f := fun _ _ hij => hij
  let E := F.reindex f hf.injective
  exact E.defect_of_sameSide_port_word b hb side hc hr
    (fun i => hrow (f i)) (fun i => hs (f i)) (fun i => ht (f i))
    (fun i j hij => hcross _ _ (hf hij)) label hsurj hNC d hF

theorem defect_of_crossing_handles {K : ℕ}
    (hhandles : HasSameSideCrossingHandles (S := S) (col := col) true K ∨
      HasSameSideCrossingHandles (S := S) (col := col) false K ∨
      HasThroughCrossingHandles (S := S) (col := col) K)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (hN : 0 < N) (hK : N + (4 * N + 3) ≤ K) (hc : 4 * N + 3 ≤ c) (hr : Odd rows)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (d : ℕ)
    (hF : 2 * (antipodalPortGraph label).indepNum + d ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast d G := by
  rcases hhandles with h | h | h
  · exact defect_of_large_sameSide_crossing true h b hb (by omega) (by omega)
      (fun _ => hr) label hsurj hNC d hF
  · exact defect_of_large_sameSide_crossing false h b hb (by omega) (by omega)
      (fun _ => hr) label hsurj hNC d hF
  · exact defect_of_large_through_crossing h b hb hN hK hc label hsurj hNC d hF

end
end Erdos73.ColumnHandleFamily
