import StackExchange.Puzzling139335.SquareBoundaryPartition
import StackExchange.Puzzling139335.JordanArcComponents
import StackExchange.Puzzling139335.BoundaryJunctionMultiplicity
import StackExchange.Puzzling139335.FiniteBoundaryPartition.Exact
import StackExchange.Puzzling139335.FiniteBoundaryPartition.Degree

/-!
# Pairing the two copies of each interface arc

When every boundary is cut at the common set of triple junctions, an arc on
one region agrees with exactly one arc on its partner region.  The hypotheses
below describe actual arc partitions; the matching is a derived conclusion.
-/

open Set

namespace Puzzling139335

/-- Boundary arc partitions with precisely the common junctions as vertices.
No pairing of the arc occurrences is assumed. -/
structure ExactBoundaryArcFamily (d : SquareDissection) where
  n : ExtendedPieceIndex → ℕ
  arc : (i : ExtendedPieceIndex) → Fin (n i) → Set Plane
  left : (i : ExtendedPieceIndex) → Fin (n i) → Plane
  right : (i : ExtendedPieceIndex) → Fin (n i) → Plane
  partner : (i : ExtendedPieceIndex) → Fin (n i) → ExtendedPieceIndex
  arc_between : ∀ i k, Schoenflies.IsArcBetween (arc i k) (left i k) (right i k)
  left_mem : ∀ i k, left i k ∈ tripleContactSet d.extendedPiece
  right_mem : ∀ i k, right i k ∈ tripleContactSet d.extendedPiece
  arcInterior_disjoint : ∀ i k,
    Disjoint (arc i k \ {left i k, right i k}) (tripleContactSet d.extendedPiece)
  partner_ne : ∀ i k, partner i k ≠ i
  subset_frontiers : ∀ i k, arc i k ⊆
    frontier (d.extendedPiece i) ∩ frontier (d.extendedPiece (partner i k))
  covers : ∀ i, (⋃ k, arc i k) = frontier (d.extendedPiece i)
  meet_endpoints : ∀ i k l, k ≠ l → arc i k ∩ arc i l ⊆
    ({left i k, right i k} : Set Plane) ∩ {left i l, right i l}

namespace ExactBoundaryArcFamily

variable {d : SquareDissection} (F : ExactBoundaryArcFamily d)

/-- Each arc has a point outside the junction set. -/
theorem exists_mem_off_junctions (i : ExtendedPieceIndex) (k : Fin (F.n i)) :
    ∃ x ∈ F.arc i k, x ∉ tripleContactSet d.extendedPiece := by
  obtain ⟨x, hx⟩ := (F.arc_between i k).nonempty_diff
  exact ⟨x, hx.1, fun hxE => Set.disjoint_left.mp (F.arcInterior_disjoint i k) hx hxE⟩

/-- A nonjunction point belongs to at most one arc of a given boundary. -/
theorem index_eq_of_mem_off_junctions (i : ExtendedPieceIndex)
    {k l : Fin (F.n i)} {x : Plane}
    (hxk : x ∈ F.arc i k) (hxl : x ∈ F.arc i l)
    (hxnot : x ∉ tripleContactSet d.extendedPiece) : k = l := by
  by_contra hkl
  have hxend := (F.meet_endpoints i k l hkl ⟨hxk, hxl⟩).1
  exact hxnot (pair_subset (F.left_mem i k) (F.right_mem i k) hxend)

/-- Every interface arc has exactly one matching occurrence on its named
partner boundary. -/
theorem exists_unique_partner_arc (i : ExtendedPieceIndex) (k : Fin (F.n i)) :
    ∃! l : Fin (F.n (F.partner i k)),
      F.arc i k = F.arc (F.partner i k) l := by
  obtain ⟨x, hx, hxnot⟩ := F.exists_mem_off_junctions i k
  have hxpartner : x ∈ frontier (d.extendedPiece (F.partner i k)) :=
    (F.subset_frontiers i k hx).2
  rw [← F.covers (F.partner i k)] at hxpartner
  obtain ⟨l, hxl⟩ := mem_iUnion.mp hxpartner
  have heq : F.arc i k = F.arc (F.partner i k) l :=
    (d.extendedPiece_frontier_jordan (F.partner i k)).arc_eq_of_common_point_off_vertices
      (F.arc_between i k) (F.arc_between (F.partner i k) l)
      (fun _ hy => (F.subset_frontiers i k hy).2)
      (fun _ hy => (F.subset_frontiers (F.partner i k) l hy).1)
      (F.left_mem i k) (F.right_mem i k)
      (F.left_mem (F.partner i k) l) (F.right_mem (F.partner i k) l)
      (F.arcInterior_disjoint i k) (F.arcInterior_disjoint (F.partner i k) l)
      hx hxl hxnot
  refine ⟨l, heq, ?_⟩
  intro m hm
  exact F.index_eq_of_mem_off_junctions (F.partner i k) (hm ▸ hx) hxl hxnot

/-- The matching occurrence names the original boundary as its partner. -/
theorem partner_reverse_of_arc_eq (i : ExtendedPieceIndex) (k : Fin (F.n i))
    (l : Fin (F.n (F.partner i k)))
    (heq : F.arc i k = F.arc (F.partner i k) l) :
    F.partner (F.partner i k) l = i := by
  obtain ⟨x, hx, hxnot⟩ := F.exists_mem_off_junctions i k
  have hxl : x ∈ F.arc (F.partner i k) l := heq ▸ hx
  have hxi : x ∈ d.extendedPiece i :=
    (d.extendedPiece_closed i).closure_eq ▸ (F.subset_frontiers i k hx).1.1
  have hxj : x ∈ d.extendedPiece (F.partner i k) :=
    (d.extendedPiece_closed (F.partner i k)).closure_eq ▸ (F.subset_frontiers i k hx).2.1
  have hxk : x ∈ d.extendedPiece (F.partner (F.partner i k) l) :=
    (d.extendedPiece_closed (F.partner (F.partner i k) l)).closure_eq ▸
      (F.subset_frontiers (F.partner i k) l hxl).2.1
  by_contra hne
  exact hxnot ⟨i, F.partner i k, F.partner (F.partner i k) l,
    (F.partner_ne i k).symm, Ne.symm hne, (F.partner_ne (F.partner i k) l).symm,
    hxi, hxj, hxk⟩

/-- Matching carriers and reciprocal partner labels hold simultaneously. -/
theorem exists_unique_reciprocal_partner_arc (i : ExtendedPieceIndex) (k : Fin (F.n i)) :
    ∃! l : Fin (F.n (F.partner i k)),
      F.arc i k = F.arc (F.partner i k) l ∧ F.partner (F.partner i k) l = i := by
  obtain ⟨l, heq, huniq⟩ := F.exists_unique_partner_arc i k
  exact ⟨l, ⟨heq, F.partner_reverse_of_arc_eq i k l heq⟩,
    fun m hm => huniq m hm.1⟩

end ExactBoundaryArcFamily

/-- Every junction has precisely two incident arcs on each boundary which
contains it. -/
def ExactBoundaryArcFamily.HasTwoGerms {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) : Prop :=
  ∀ (i : ExtendedPieceIndex) (v : Plane),
    v ∈ frontier (d.extendedPiece i) ∩ tripleContactSet d.extendedPiece →
      {k : Fin (F.n i) | v = F.left i k ∨ v = F.right i k}.encard = 2

/-- The arc carriers and their named endpoints arise from consecutive
intervals of a concrete ordered Jordan-loop parametrization. -/
def ExactBoundaryArcFamily.HasLoopParameters {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) : Prop :=
  ∀ i : ExtendedPieceIndex, ∃ f : ℝ → Plane,
    Schoenflies.IsLoop f ∧ f '' Icc 0 1 = frontier (d.extendedPiece i) ∧
    0 < F.n i ∧ ∃ t : Fin (F.n i + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last (F.n i)) = 1 ∧
      (1 / 2 : ℝ) ∈ range t ∧
      (∀ k : Fin (F.n i), F.arc i k = f '' Icc (t k.castSucc) (t k.succ)) ∧
      (∀ k : Fin (F.n i), F.left i k = f (t k.castSucc)) ∧
      (∀ k : Fin (F.n i), F.right i k = f (t k.succ))

/-- Each boundary has an actual exact-junction arc partition, retaining its
two incidences at every vertex. -/
theorem SquareDissection.exists_exact_extended_boundary_arc_cover (d : SquareDissection)
    (i : ExtendedPieceIndex) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : Fin n → Set Plane,
      ∃ a b : Fin n → Plane, ∃ partner : Fin n → ExtendedPieceIndex,
      (∀ k, Schoenflies.IsArcBetween (A k) (a k) (b k)) ∧
      (∀ k, a k ∈ tripleContactSet d.extendedPiece) ∧
      (∀ k, b k ∈ tripleContactSet d.extendedPiece) ∧
      (∀ k, Disjoint (A k \ {a k, b k}) (tripleContactSet d.extendedPiece)) ∧
      (∀ k, partner k ≠ i) ∧
      (∀ k, A k ⊆ frontier (d.extendedPiece i) ∩
        frontier (d.extendedPiece (partner k))) ∧
      (⋃ k, A k) = frontier (d.extendedPiece i) ∧
      (∀ k l, k ≠ l → A k ∩ A l ⊆ ({a k, b k} : Set Plane) ∩ {a l, b l}) ∧
      (∀ v ∈ frontier (d.extendedPiece i) ∩ tripleContactSet d.extendedPiece,
        {k : Fin n | v = a k ∨ v = b k}.encard = 2) ∧
      ∃ f : ℝ → Plane, Schoenflies.IsLoop f ∧
        f '' Icc 0 1 = frontier (d.extendedPiece i) ∧
        ∃ t : Fin (n + 1) → ℝ,
          StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
          (1 / 2 : ℝ) ∈ range t ∧
          (∀ k : Fin n, A k = f '' Icc (t k.castSucc) (t k.succ)) ∧
          (∀ k : Fin n, a k = f (t k.castSucc)) ∧
          (∀ k : Fin n, b k = f (t k.succ)) := by
  classical
  let J := {j : ExtendedPieceIndex // j ≠ i}
  let T : J → Set Plane := fun j => d.extendedPiece i ∩ d.extendedPiece j.val
  have hclosed (j : J) : IsClosed (T j) :=
    (d.extendedPiece_closed i).inter (d.extendedPiece_closed j.val)
  have hcover : frontier (d.extendedPiece i) ⊆ ⋃ j : J, T j := by
    intro x hx
    have hxi : x ∈ d.extendedPiece i := (d.extendedPiece_closed i).closure_eq ▸ hx.1
    obtain ⟨j, hji, hxj⟩ := boundary_mem_another_of_closed_cover d.extendedPiece
      d.extendedPiece_closed d.extendedPiece_covers hx
    exact mem_iUnion.mpr ⟨⟨j, hji⟩, ⟨hxi, hxj⟩⟩
  have hoverlap (j k : J) (hjk : j ≠ k) :
      frontier (d.extendedPiece i) ∩ T j ∩ T k ⊆ tripleContactSet d.extendedPiece := by
    rintro x ⟨⟨_, hxj⟩, hxk⟩
    exact ⟨i, j.val, k.val, j.property.symm, k.property.symm,
      (fun h => hjk (Subtype.ext h)), hxj.1, hxj.2, hxk.2⟩
  obtain ⟨f, hf, himage, n, hn, t, ht, ht0, ht1, hhalf, hvertices,
      _, hdiff, hlabels, harcs, hcover_arcs, hmeet⟩ :=
    (d.extendedPiece_frontier_jordan i).exists_exact_finite_closed_cover_partition
      T hclosed hcover (tripleContactSet d.extendedPiece)
      d.extendedTripleContactSet_finite hoverlap (d.extendedBoundaryJunctions_nontrivial i)
  choose partner hpartner using hlabels
  have hsub (k : Fin n) : f '' Icc (t k.castSucc) (t k.succ) ⊆
      frontier (d.extendedPiece i) ∩ frontier (d.extendedPiece (partner k).val) := by
    rw [← d.extendedPiece_inter_eq_frontier_inter (partner k).property.symm]
    exact hpartner k
  refine ⟨n, hn, (fun k => f '' Icc (t k.castSucc) (t k.succ)),
    (fun k => f (t k.castSucc)), (fun k => f (t k.succ)),
    (fun k => (partner k).val), harcs, ?_, ?_, hdiff,
    (fun k => (partner k).property), hsub, hcover_arcs, hmeet, ?_, ?_⟩
  · exact fun k => hvertices k.castSucc
  · exact fun k => hvertices k.succ
  · intro v hv
    have hvcover : v ∈ ⋃ k : Fin n, f '' Icc (t k.castSucc) (t k.succ) := by
      rw [hcover_arcs]
      exact hv.1
    obtain ⟨k, hvk⟩ := mem_iUnion.mp hvcover
    have hvend : v ∈ ({f (t k.castSucc), f (t k.succ)} : Set Plane) := by
      by_contra hvnot
      exact Set.disjoint_left.mp (hdiff k) ⟨hvk, hvnot⟩ hv.2
    have hvvertices : v ∈ f '' range t := by
      rcases hvend with rfl | rfl
      · exact mem_image_of_mem f (mem_range_self k.castSucc)
      · exact mem_image_of_mem f (mem_range_self k.succ)
    exact hf.partition_vertex_incidence_encard hn ht ht0 ht1 hhalf hvvertices
  · exact ⟨f, hf, himage, t, ht, ht0, ht1, hhalf,
      (fun _ => rfl), (fun _ => rfl), (fun _ => rfl)⟩

/-- Every square dissection admits compatible exact-junction arc partitions
on all five boundaries, with two arc germs at each incident junction and
concrete ordered loop parametrizations. -/
theorem SquareDissection.exists_exact_boundary_arc_family (d : SquareDissection) :
    ∃ F : ExactBoundaryArcFamily d, F.HasTwoGerms ∧ F.HasLoopParameters := by
  classical
  choose n hn A a b partner harc hleft hright hdis hne hsub hcover hmeet hdegree hloop using
    (fun i => d.exists_exact_extended_boundary_arc_cover i)
  let F : ExactBoundaryArcFamily d := {
    n := n
    arc := A
    left := a
    right := b
    partner := partner
    arc_between := harc
    left_mem := hleft
    right_mem := hright
    arcInterior_disjoint := hdis
    partner_ne := hne
    subset_frontiers := hsub
    covers := hcover
    meet_endpoints := hmeet }
  refine ⟨F, hdegree, ?_⟩
  intro i
  obtain ⟨f, hf, himage, t, ht, ht0, ht1, hhalf, hA, ha, hb⟩ := hloop i
  exact ⟨f, hf, himage, hn i, t, ht, ht0, ht1, hhalf, hA, ha, hb⟩

end Puzzling139335
