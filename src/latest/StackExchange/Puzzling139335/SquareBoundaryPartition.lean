import StackExchange.Puzzling139335.SquareBoundaryJunctions
import StackExchange.Puzzling139335.FiniteBoundaryPartition.Arcs

/-!
# Finite boundary arcs with named partners

Adjoining the closed exterior gives five closed regions covering the plane.
Every boundary point has a second owner, and overlaps between two possible
partners occur only at the finite set of triple contacts.  A finite ordered
partition of each Jordan boundary can therefore be labelled by its partners.
-/

open Set

namespace Puzzling139335

/-- Distinct extended pieces meet exactly where their frontiers meet. -/
theorem SquareDissection.extendedPiece_inter_eq_frontier_inter (d : SquareDissection)
    {i j : ExtendedPieceIndex} (hij : i ≠ j) :
    d.extendedPiece i ∩ d.extendedPiece j =
      frontier (d.extendedPiece i) ∩ frontier (d.extendedPiece j) := by
  have hdis {a b : ExtendedPieceIndex} (hab : a ≠ b) :
      Disjoint (interior (d.extendedPiece a)) (d.extendedPiece b) :=
    disjoint_interior_piece_of_regular d.extendedPiece d.extendedPiece_regular
      d.extendedPiece_disjoint_interiors hab
  apply Subset.antisymm
  · rintro x ⟨hi, hj⟩
    constructor
    · exact (mem_frontier_iff_notMem_interior hi).mpr
        (fun hint => Set.disjoint_left.mp (hdis hij) hint hj)
    · exact (mem_frontier_iff_notMem_interior hj).mpr
        (fun hint => Set.disjoint_left.mp (hdis hij.symm) hint hi)
  · rintro x ⟨hi, hj⟩
    exact ⟨(d.extendedPiece_closed i).closure_eq ▸ hi.1,
      (d.extendedPiece_closed j).closure_eq ▸ hj.1⟩

/-- A chosen loop parametrization of any of the five boundaries has a finite
consecutive arc partition.  Every arc has a different named partner, lies on
both frontiers, and meets other partition arcs only at their endpoints. -/
theorem SquareDissection.exists_extendedPiece_boundary_partition (d : SquareDissection)
    (i : ExtendedPieceIndex) {f : ℝ → Plane} (hf : Schoenflies.IsLoop f)
    (himage : f '' Icc 0 1 = frontier (d.extendedPiece i)) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (1 / 2 : ℝ) ∈ range t ∧ ∃ partner : Fin n → ExtendedPieceIndex,
      (∀ k : Fin n, partner k ≠ i) ∧
      (∀ k : Fin n, Schoenflies.IsArcBetween (f '' Icc (t k.castSucc) (t k.succ))
        (f (t k.castSucc)) (f (t k.succ))) ∧
      (∀ k : Fin n, f '' Icc (t k.castSucc) (t k.succ) ⊆
        frontier (d.extendedPiece i) ∩ frontier (d.extendedPiece (partner k))) ∧
      (⋃ k : Fin n, f '' Icc (t k.castSucc) (t k.succ)) =
        frontier (d.extendedPiece i) ∧
      ∀ k l : Fin n, k ≠ l →
        (f '' Icc (t k.castSucc) (t k.succ)) ∩
          (f '' Icc (t l.castSucc) (t l.succ)) ⊆
        ({f (t k.castSucc), f (t k.succ)} : Set Plane) ∩
          {f (t l.castSucc), f (t l.succ)} := by
  classical
  let T : ExtendedPieceIndex → Set Plane :=
    fun j => if j = i then ∅ else d.extendedPiece i ∩ d.extendedPiece j
  have hclosed (j : ExtendedPieceIndex) : IsClosed (T j) := by
    by_cases hji : j = i
    · simpa only [T, if_pos hji] using (isClosed_empty : IsClosed (∅ : Set Plane))
    · simpa only [T, if_neg hji] using
        (d.extendedPiece_closed i).inter (d.extendedPiece_closed j)
  have hcover : f '' Icc 0 1 ⊆ ⋃ j, T j := by
    intro x hx
    have hxfront : x ∈ frontier (d.extendedPiece i) := himage ▸ hx
    obtain ⟨j, hji, hxj⟩ := boundary_mem_another_of_closed_cover d.extendedPiece
      d.extendedPiece_closed d.extendedPiece_covers hxfront
    have hxi : x ∈ d.extendedPiece i := (d.extendedPiece_closed i).closure_eq ▸ hxfront.1
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    simpa only [T, if_neg hji] using (show x ∈ d.extendedPiece i ∩ d.extendedPiece j
      from ⟨hxi, hxj⟩)
  have hoverlap (j k : ExtendedPieceIndex) (hjk : j ≠ k) :
      (f '' Icc 0 1) ∩ T j ∩ T k ⊆ tripleContactSet d.extendedPiece := by
    rintro x ⟨⟨_, hxj⟩, hxk⟩
    by_cases hji : j = i
    · simp only [T, if_pos hji, mem_empty_iff_false] at hxj
    by_cases hki : k = i
    · simp only [T, if_pos hki, mem_empty_iff_false] at hxk
    have hxij : x ∈ d.extendedPiece i ∩ d.extendedPiece j := by
      simpa only [T, if_neg hji] using hxj
    have hxik : x ∈ d.extendedPiece i ∩ d.extendedPiece k := by
      simpa only [T, if_neg hki] using hxk
    exact ⟨i, j, k, Ne.symm hji, Ne.symm hki, hjk, hxij.1, hxij.2, hxik.2⟩
  obtain ⟨n, hn, t, ht, ht0, ht1, hhalf, hlabels⟩ :=
    hf.exists_finite_closed_cover_partition T hclosed hcover
      (tripleContactSet d.extendedPiece) d.extendedTripleContactSet_finite hoverlap
  choose partner hpartner using hlabels
  have hne (k : Fin n) : partner k ≠ i := by
    intro hki
    have hx := hpartner k (show f (t k.castSucc) ∈
        f '' Icc (t k.castSucc) (t k.succ) from
      ⟨t k.castSucc, ⟨le_rfl, (ht k.castSucc_lt_succ).le⟩, rfl⟩)
    simp only [T, if_pos hki, mem_empty_iff_false] at hx
  have hsub (k : Fin n) : f '' Icc (t k.castSucc) (t k.succ) ⊆
      frontier (d.extendedPiece i) ∩ frontier (d.extendedPiece (partner k)) := by
    rw [← d.extendedPiece_inter_eq_frontier_inter (hne k).symm]
    simpa only [T, if_neg (hne k)] using hpartner k
  refine ⟨n, hn, t, ht, ht0, ht1, hhalf, partner, hne, ?_, hsub, ?_, ?_⟩
  · exact fun k => hf.isArcBetween_partition_interval ht ht0 ht1 hhalf k
  · exact (iUnion_partition_interval_images f hn ht ht0 ht1).trans himage
  · exact fun k l hkl => hf.partition_interval_images_inter_subset_endpoints ht ht0 ht1 hkl

/-- Each of the five boundaries is a finite union of partner-labelled simple
arcs, with distinct arcs intersecting only at their endpoints. -/
theorem SquareDissection.exists_extendedPiece_boundary_arc_cover (d : SquareDissection)
    (i : ExtendedPieceIndex) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : Fin n → Set Plane,
      ∃ a b : Fin n → Plane, ∃ partner : Fin n → ExtendedPieceIndex,
      (∀ k, partner k ≠ i ∧ Schoenflies.IsArcBetween (A k) (a k) (b k) ∧
        A k ⊆ frontier (d.extendedPiece i) ∩ frontier (d.extendedPiece (partner k))) ∧
      (⋃ k, A k) = frontier (d.extendedPiece i) ∧
      ∀ k l : Fin n, k ≠ l → A k ∩ A l ⊆
        ({a k, b k} : Set Plane) ∩ {a l, b l} := by
  obtain ⟨f, hf, himage⟩ := d.extendedPiece_frontier_jordan i
  obtain ⟨n, hn, t, _, _, _, _, partner, hne, harc, hsub, hcover, hinter⟩ :=
    d.exists_extendedPiece_boundary_partition i hf himage
  exact ⟨n, hn, (fun k => f '' Icc (t k.castSucc) (t k.succ)),
    (fun k => f (t k.castSucc)), (fun k => f (t k.succ)), partner,
    (fun k => ⟨hne k, harc k, hsub k⟩), hcover, hinter⟩

end Puzzling139335
