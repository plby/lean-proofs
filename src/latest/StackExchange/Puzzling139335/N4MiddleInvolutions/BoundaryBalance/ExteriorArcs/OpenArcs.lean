import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.Geometry
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.Uniqueness

/-!
# Open outer arcs avoid every junction

Strict contact uniqueness removes all junctions from the open outer arcs.
A generic maximal-arc lemma then identifies a square-boundary arc with an
actual exterior occurrence when its endpoints are known junctions.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

variable {d : SquareDissection}

private theorem plane_eq_mk_coords (p : Plane) :
    p = Schoenflies.Plane.mk (p 0) (p 1) := by
  ext j
  fin_cases j <;> rfl

private theorem horizontal_mk_point (x y : ℝ) :
    ReflectionSeparation.horizontal (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk x (1 - y) := by
  ext j
  fin_cases j <;> simp

/-- Every nonterminal point on the lower outer arc has no bounded-piece
owner other than the lower outer piece. -/
theorem lowerOuterArc_unique_tile
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    {p : Plane}
    (hp : p ∈ lowerOuterArc a b \
      {Schoenflies.Plane.mk 0 a, Schoenflies.Plane.mk 1 b})
    {i : Fin 4} (hi : i ≠ 0) : p ∉ d.piece i := by
  by_cases hzero : p 1 = 0
  · have heq : p = Schoenflies.Plane.mk (p 0) 0 := by
      simpa only [hzero] using plane_eq_mk_coords p
    rw [heq]
    exact other_not_mem_bottom h hc _ hi
  rcases (mem_lowerOuterArc_iff ha.le hb.le).mp hp.1 with hL | hB | hR
  · have heq : p = Schoenflies.Plane.mk 0 (p 1) := by
      simpa only [hL.1] using plane_eq_mk_coords p
    have hpa : p 1 ≠ a := by
      intro heqa
      apply hp.2
      exact Or.inl (by simpa only [heqa] using heq)
    have hy : p 1 ∈ Ioo (0 : ℝ) a :=
      ⟨lt_of_le_of_ne hL.2.1 (Ne.symm hzero), lt_of_le_of_ne hL.2.2 hpa⟩
    rw [heq]
    exact other_not_mem_strict_lower_side h hc (Or.inl rfl) hleft hy hi
  · exact (hzero hB.1).elim
  · have heq : p = Schoenflies.Plane.mk 1 (p 1) := by
      simpa only [hR.1] using plane_eq_mk_coords p
    have hpb : p 1 ≠ b := by
      intro heqb
      apply hp.2
      exact Or.inr (by simpa only [mem_singleton_iff, heqb] using heq)
    have hy : p 1 ∈ Ioo (0 : ℝ) b :=
      ⟨lt_of_le_of_ne hR.2.1 (Ne.symm hzero), lt_of_le_of_ne hR.2.2 hpb⟩
    rw [heq]
    exact other_not_mem_strict_lower_side h hc (Or.inr rfl) hright hy hi

/-- The open lower outer arc contains no extended triple junction. -/
theorem lowerOuterArc_interior_disjoint_junctions
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b) :
    Disjoint (lowerOuterArc a b \
      {Schoenflies.Plane.mk 0 a, Schoenflies.Plane.mk 1 b})
      (tripleContactSet d.extendedPiece) := by
  apply Set.disjoint_left.mpr
  intro p hp
  exact not_mem_junctions_of_unique_tile
    (fun _ hi => lowerOuterArc_unique_tile h hc ha hb hleft hright hp hi)

/-- Every nonterminal point on the reflected upper arc has only the upper
outer piece as a possible bounded-piece owner. -/
theorem upperOuterArc_unique_tile
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    {p : Plane}
    (hp : p ∈ upperOuterArc a b \
      {Schoenflies.Plane.mk 0 (1 - a), Schoenflies.Plane.mk 1 (1 - b)})
    {i : Fin 4} (hi : i ≠ 1) : p ∉ d.piece i := by
  obtain ⟨q, hq, rfl⟩ := hp.1
  have hqends : q ∉ ({Schoenflies.Plane.mk 0 a,
      Schoenflies.Plane.mk 1 b} : Set Plane) := by
    intro hqend
    apply hp.2
    rcases hqend with rfl | rfl
    · exact Or.inl (horizontal_mk_point 0 a)
    · exact Or.inr (horizontal_mk_point 1 b)
  by_cases hzero : q 1 = 0
  · have heq : ReflectionSeparation.horizontal q =
        Schoenflies.Plane.mk (q 0) 1 := by
      ext j
      fin_cases j <;> simp [hzero]
    rw [heq]
    exact other_not_mem_top h hc _ hi
  rcases (mem_lowerOuterArc_iff ha.le hb.le).mp hq with hL | hB | hR
  · have hqeq : q = Schoenflies.Plane.mk 0 (q 1) := by
      simpa only [hL.1] using plane_eq_mk_coords q
    have hqa : q 1 ≠ a := by
      intro heqa
      apply hqends
      exact Or.inl (by simpa only [heqa] using hqeq)
    have hq0 := lt_of_le_of_ne hL.2.1 (Ne.symm hzero)
    have hqa' := lt_of_le_of_ne hL.2.2 hqa
    have hy : 1 - q 1 ∈ Ioo (1 - a) (1 : ℝ) :=
      ⟨by linarith only [hqa'], by linarith only [hq0]⟩
    rw [hqeq, horizontal_mk_point]
    exact other_not_mem_strict_upper_side h hc (Or.inl rfl) hleft hy hi
  · exact (hzero hB.1).elim
  · have hqeq : q = Schoenflies.Plane.mk 1 (q 1) := by
      simpa only [hR.1] using plane_eq_mk_coords q
    have hqb : q 1 ≠ b := by
      intro heqb
      apply hqends
      exact Or.inr (by simpa only [mem_singleton_iff, heqb] using hqeq)
    have hq0 := lt_of_le_of_ne hR.2.1 (Ne.symm hzero)
    have hqb' := lt_of_le_of_ne hR.2.2 hqb
    have hy : 1 - q 1 ∈ Ioo (1 - b) (1 : ℝ) :=
      ⟨by linarith only [hqb'], by linarith only [hq0]⟩
    rw [hqeq, horizontal_mk_point]
    exact other_not_mem_strict_upper_side h hc (Or.inr rfl) hright hy hi

/-- The open upper outer arc contains no extended triple junction. -/
theorem upperOuterArc_interior_disjoint_junctions
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b) :
    Disjoint (upperOuterArc a b \
      {Schoenflies.Plane.mk 0 (1 - a), Schoenflies.Plane.mk 1 (1 - b)})
      (tripleContactSet d.extendedPiece) := by
  apply Set.disjoint_left.mpr
  intro p hp
  exact not_mem_junctions_of_unique_tile
    (fun _ hi => upperOuterArc_unique_tile h hc ha hb hleft hright hp hi)

/-- A maximal junction-to-junction square-boundary arc is one exterior
occurrence of the exact family.  A uniquely owned point identifies its
partner tile. -/
theorem exists_exterior_arc_of_unique_tile
    (F : ExactBoundaryArcFamily d) {A : Set Plane} {p q x : Plane} {i : Fin 4}
    (hA : Schoenflies.IsArcBetween A p q)
    (hAS : A ⊆ frontier unitSquare)
    (hp : p ∈ tripleContactSet d.extendedPiece)
    (hq : q ∈ tripleContactSet d.extendedPiece)
    (havoid : Disjoint (A \ {p, q}) (tripleContactSet d.extendedPiece))
    (hx : x ∈ A) (hunique : ∀ j : Fin 4, j ≠ i → x ∉ d.piece j) :
    ∃ k : Fin (F.n (.inr ())),
      F.partner (.inr ()) k = .inl i ∧ F.arc (.inr ()) k = A := by
  have hxnot : x ∉ tripleContactSet d.extendedPiece :=
    not_mem_junctions_of_unique_tile hunique
  have hxE : x ∈ frontier (d.extendedPiece (.inr ())) := by
    simpa only [SquareDissection.extendedPiece_exterior, frontier_closedSquareExterior]
      using hAS hx
  rw [← F.covers (.inr ())] at hxE
  obtain ⟨k, hxk⟩ := mem_iUnion.mp hxE
  have hkS : F.arc (.inr ()) k ⊆ frontier unitSquare := by
    intro y hy
    simpa only [SquareDissection.extendedPiece_exterior, frontier_closedSquareExterior]
      using (F.subset_frontiers (.inr ()) k hy).1
  have harc : F.arc (.inr ()) k = A :=
    isJordanCurve_frontier_unitSquare.arc_eq_of_common_point_off_vertices
      (F.arc_between (.inr ()) k) hA hkS hAS
      (F.left_mem (.inr ()) k) (F.right_mem (.inr ()) k) hp hq
      (F.arcInterior_disjoint (.inr ()) k) havoid hxk hx hxnot
  refine ⟨k, ?_, harc⟩
  cases hpartner : F.partner (.inr ()) k with
  | inl j =>
    have hxfront := (F.subset_frontiers (.inr ()) k hxk).2
    rw [hpartner, SquareDissection.extendedPiece_tile] at hxfront
    have hxj : x ∈ d.piece j := (d.jordan j).isClosed.closure_eq ▸ hxfront.1
    have hji : j = i := by
      by_contra hne
      exact hunique j hne hxj
    exact congrArg Sum.inl hji
  | inr u =>
    exact False.elim ((F.partner_ne (.inr ()) k)
      (hpartner.trans (congrArg Sum.inr (Subsingleton.elim u ()))))


end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
