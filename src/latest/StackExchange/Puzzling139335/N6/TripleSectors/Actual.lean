import StackExchange.Puzzling139335.N6.Incidence
import StackExchange.Puzzling139335.SharedCornerStraightCount
import StackExchange.Puzzling139335.Transform
import StackExchange.Puzzling139335.N6.TripleSectors.LocalSector

/-!
# Normalizing three actual copies at a common square corner

This module constructs a local triple from the dissection hypotheses.  Its
isometries are the actual relative placements, conjugated by one symmetry
of the square; they fix the origin because the intrinsic corner is shared.
The local cover excludes every nonincident piece by closedness.
-/

open Set Metric

namespace Puzzling139335.N6.TripleSectors

noncomputable section

/-- Three actual Jordan regions at the origin, before determining their
sector angles or their relative placement matrices. -/
structure NormalizedTriple where
  region : Fin 3 → Set Plane
  jordan : ∀ i, IsJordanRegion (region i)
  square_fit : ∀ i, region i ⊆ unitSquare
  straight : ∀ i, HasStraightBranchCount (frontier (region i)) 0 2
  disjoint : Pairwise (fun i j => Disjoint (interior (region i)) (interior (region j)))
  congruences : ∀ i j, ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, e 0 = 0 ∧ e '' region i = region j
  local_cover : ∃ r > 0, ball (0 : Plane) r ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆
    ⋃ i, region i

theorem NormalizedTriple.quadrant (T : NormalizedTriple) (i : Fin 3)
    (x : Plane) (hx : x ∈ T.region i) : 0 ≤ x 0 ∧ 0 ≤ x 1 :=
  ⟨(T.square_fit i hx).1.1, (T.square_fit i hx).2.1⟩

theorem quadrant_ball_one_subset_unitSquare :
    ball (0 : Plane) 1 ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆ unitSquare := by
  intro x hx
  have hd : dist x 0 < 1 := hx.1
  have hs : dist x 0 ^ 2 < 1 := by nlinarith only [dist_nonneg (x := x) (y := 0), hd]
  have heq := plane_dist_sq x 0
  simp only [PiLp.zero_apply, sub_zero] at heq
  exact ⟨⟨hx.2.1, by nlinarith [sq_nonneg (x 1)]⟩,
    ⟨hx.2.2, by nlinarith [sq_nonneg (x 0)]⟩⟩

/-- A finite list of all pieces containing the origin covers a genuine
quarter-ball. No local angle or local boundary regularity is assumed. -/
theorem local_cover_of_indexed_owners (d : SquareDissection) (f : Fin 3 → Fin 4)
    (howners : ∀ i, (0 : Plane) ∈ d.piece i ↔ ∃ k, f k = i) :
    ∃ r > 0, ball (0 : Plane) r ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆
      ⋃ k, d.piece (f k) := by
  classical
  let U : Set Plane := ⋂ i : Fin 4, if (0 : Plane) ∈ d.piece i then univ else (d.piece i)ᶜ
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact isOpen_univ
    · exact (d.jordan i).isClosed.isOpen_compl
  have hzero : (0 : Plane) ∈ U := by
    apply mem_iInter.mpr
    intro i
    split_ifs with hi
    · trivial
    · exact hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  refine ⟨min r 1, lt_min hr zero_lt_one, ?_⟩
  intro x hx
  have hsmall : x ∈ ball (0 : Plane) 1 := ball_subset_ball (min_le_right r 1) hx.1
  have hxSquare := quadrant_ball_one_subset_unitSquare ⟨hsmall, hx.2⟩
  obtain ⟨i, hi⟩ := d.exists_piece_mem hxSquare
  have hz : (0 : Plane) ∈ d.piece i := by
    by_contra hnot
    have hxU := hball (ball_subset_ball (min_le_left r 1) hx.1)
    have hxnot : x ∉ d.piece i := by
      change x ∈ (d.piece i)ᶜ
      simpa only [if_neg hnot] using mem_iInter.mp hxU i
    exact hxnot hi
  obtain ⟨k, hk⟩ := (howners i).mp hz
  exact mem_iUnion.mpr ⟨k, hk ▸ hi⟩

theorem zero_mem_cornerFlip_image_iff (s : Fin 4) (P : Set Plane) :
    (0 : Plane) ∈ SquareSymmetry.cornerFlip s '' P ↔ corner s ∈ P := by
  constructor
  · rintro ⟨p, hp, heq⟩
    have hpCorner : p = corner s := (SquareSymmetry.cornerFlip s).injective
      (heq.trans (SquareSymmetry.cornerFlip_corner s).symm)
    exact hpCorner ▸ hp
  · intro hp
    exact ⟨corner s, hp, SquareSymmetry.cornerFlip_corner s⟩

/-- The normalized actual relative placement. -/
def cornerRelativePlacement (d : SquareDissection) (s : Fin 4) (i j : Fin 4) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  ((SquareSymmetry.cornerFlip s).symm.trans (d.relativePlacement i j)).trans
    (SquareSymmetry.cornerFlip s)

theorem cornerRelativePlacement_image (d : SquareDissection) (s i j : Fin 4) :
    cornerRelativePlacement d s i j '' (SquareSymmetry.cornerFlip s '' d.piece i) =
      SquareSymmetry.cornerFlip s '' d.piece j := by
  calc
    _ = SquareSymmetry.cornerFlip s '' (d.relativePlacement i j '' d.piece i) := by
      simp only [image_image]
      congr 1
      funext p
      change SquareSymmetry.cornerFlip s (d.relativePlacement i j
        ((SquareSymmetry.cornerFlip s).symm (SquareSymmetry.cornerFlip s p))) = _
      rw [AffineIsometryEquiv.symm_apply_apply]
    _ = _ := by rw [d.relativePlacement_image]

theorem cornerRelativePlacement_zero (d : SquareDissection) (s i j : Fin 4)
    (htype : d.intrinsicCorner i s = d.intrinsicCorner j s) :
    cornerRelativePlacement d s i j 0 = 0 := by
  have hpre : (SquareSymmetry.cornerFlip s).symm 0 = corner s := by
    apply (SquareSymmetry.cornerFlip s).injective
    simp only [AffineIsometryEquiv.apply_symm_apply, SquareSymmetry.cornerFlip_corner]
  change SquareSymmetry.cornerFlip s
    (d.relativePlacement i j ((SquareSymmetry.cornerFlip s).symm 0)) = 0
  rw [hpre, d.relativePlacement_corner htype, SquareSymmetry.cornerFlip_corner]

/-- An actual triple of congruent pieces with one common intrinsic corner
can be put into the generic local triple format. -/
theorem exists_normalized_triple (d : SquareDissection) (s : Fin 4) (a : Plane)
    (hthree : d.cornerTileCount s = 3)
    (htype : ∀ i, corner s ∈ d.piece i → d.intrinsicCorner i s = a) :
    ∃ T : NormalizedTriple, ∃ f : Fin 3 → Fin 4,
      Function.Injective f ∧
      (∀ i, corner s ∈ d.piece i ↔ ∃ k, f k = i) ∧
      (∀ k, T.region k = SquareSymmetry.cornerFlip s '' d.piece (f k)) := by
  classical
  obtain ⟨i, j, k, hij, hik, hjk, howners⟩ := triple_corner_owners d s hthree
  let f : Fin 3 → Fin 4 := ![i, j, k]
  have hf : Function.Injective f := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [f]
  have howners' : ∀ l, corner s ∈ d.piece l ↔ ∃ u, f u = l := by
    intro l
    constructor
    · intro hl
      rcases (howners l).mp hl with h | h | h
      · exact ⟨0, by simpa [f] using h.symm⟩
      · exact ⟨1, by simpa [f] using h.symm⟩
      · exact ⟨2, by simpa [f] using h.symm⟩
    · rintro ⟨u, rfl⟩
      apply (howners (f u)).mpr
      fin_cases u <;> simp [f]
  let D := d.map (SquareSymmetry.cornerFlip s) (SquareSymmetry.cornerFlip_image_unitSquare s)
  have hDpiece (l : Fin 4) : D.piece l = SquareSymmetry.cornerFlip s '' d.piece l := rfl
  have hDowners : ∀ l, (0 : Plane) ∈ D.piece l ↔ ∃ u, f u = l := by
    intro l
    rw [hDpiece, zero_mem_cornerFlip_image_iff, howners']
  have hcount := d.hasStraightBranchCount_two_of_three_equal_intrinsic s a hthree htype
  have hstraight (u : Fin 3) : HasStraightBranchCount (frontier (D.piece (f u))) 0 2 := by
    have hu : corner s ∈ d.piece (f u) := (howners' (f u)).mpr ⟨u, rfl⟩
    have hsource : HasStraightBranchCount (frontier (d.piece 0))
        (d.intrinsicCorner (f u) s) 2 := by rwa [htype (f u) hu]
    have hphysical := d.straightBranchCount_at_corner_of_intrinsic (f u) s hsource
    have hn := hphysical.image_affineIsometry (SquareSymmetry.cornerFlip s)
    rw [SquareSymmetry.cornerFlip_corner] at hn
    have hfront := (SquareSymmetry.cornerFlip s).toHomeomorph.image_frontier (d.piece (f u))
    change SquareSymmetry.cornerFlip s '' frontier (d.piece (f u)) =
      frontier (SquareSymmetry.cornerFlip s '' d.piece (f u)) at hfront
    rwa [hfront] at hn
  refine ⟨{
    region := fun u => D.piece (f u)
    jordan := fun u => D.jordan (f u)
    square_fit := fun u => D.piece_subset (f u)
    straight := hstraight
    disjoint := fun _ _ hne => D.disjoint_interiors (fun heq => hne (hf heq))
    congruences := ?_
    local_cover := local_cover_of_indexed_owners D f hDowners
  }, f, hf, howners', fun _ => rfl⟩
  intro u v
  refine ⟨cornerRelativePlacement d s (f u) (f v), ?_, cornerRelativePlacement_image d s _ _⟩
  apply cornerRelativePlacement_zero
  have hu : corner s ∈ d.piece (f u) := (howners' (f u)).mpr ⟨u, rfl⟩
  have hv : corner s ∈ d.piece (f v) := (howners' (f v)).mpr ⟨v, rfl⟩
  exact (htype _ hu).trans (htype _ hv).symm

end

end Puzzling139335.N6.TripleSectors
