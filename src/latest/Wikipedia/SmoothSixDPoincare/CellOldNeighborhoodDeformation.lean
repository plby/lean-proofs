import Wikipedia.SmoothSixDPoincare.CellOldNeighborhoodRetraction

/-! # The actual old-space neighborhood strongly deforms to the old space -/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

variable {N X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

omit [NormedSpace ℝ N] in
theorem neighborhood_time_cover : range (Prod.map (id : I → I) D.oldInclusion) ∪
    range (Prod.map (id : I → I) D.outerInclusion) = univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t, x⟩
  have hx : x ∈ range D.oldInclusion ∪ range D.outerInclusion := by
    rw [D.oldNeighborhood_cover]
    trivial
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨(t, a), rfl⟩
  · exact Or.inr ⟨(t, z), rfl⟩

def stationaryOld : C(I × D.old, D.oldNeighborhood) := D.oldInclusion.comp ContinuousMap.snd

def movingOuter : C(I × OuterDisk.Space N, D.oldNeighborhood) :=
  D.outerInclusion.comp OuterDisk.deformation.toHomotopy.toContinuousMap

theorem neighborhoodMotions_agree (a : I × D.old) (z : I × OuterDisk.Space N)
    (haz : Prod.map id D.oldInclusion a = Prod.map id D.outerInclusion z) :
    D.stationaryOld a = D.movingOuter z := by
  have ha : D.oldInclusion a.2 = D.outerInclusion z.2 := congrArg Prod.snd haz
  have heq : (a.2 : X) = D.cell z.2.val := congrArg Subtype.val ha
  have hn : ‖(z.2.val : N)‖ = 1 := (D.boundary z.2.val).mp (heq ▸ a.2.property)
  change D.oldInclusion a.2 = D.outerInclusion (OuterDisk.deformation (z.1, z.2))
  rw [OuterDisk.deformation.eq_fst z.1 hn]
  exact ha

def neighborhoodMotion : C(I × D.oldNeighborhood, D.oldNeighborhood) :=
  ClosedCover.mapOfClosedPieces (Prod.map id D.oldInclusion) (Prod.map id D.outerInclusion)
    (IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (IsClosedEmbedding.id.prodMap D.outerInclusion_closed)
    D.neighborhood_time_cover D.stationaryOld D.movingOuter D.neighborhoodMotions_agree

theorem neighborhoodMotion_old (t : I) (a : D.old) :
    D.neighborhoodMotion (t, D.oldInclusion a) = D.oldInclusion a :=
  ClosedCover.mapOfClosedPieces_left (Prod.map id D.oldInclusion) (Prod.map id D.outerInclusion)
    (IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (IsClosedEmbedding.id.prodMap D.outerInclusion_closed)
    D.neighborhood_time_cover D.stationaryOld D.movingOuter D.neighborhoodMotions_agree (t, a)

theorem neighborhoodMotion_outer (t : I) (z : OuterDisk.Space N) :
    D.neighborhoodMotion (t, D.outerInclusion z) =
      D.outerInclusion (OuterDisk.deformation (t, z)) :=
  ClosedCover.mapOfClosedPieces_right (Prod.map id D.oldInclusion) (Prod.map id D.outerInclusion)
    (IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (IsClosedEmbedding.id.prodMap D.outerInclusion_closed)
    D.neighborhood_time_cover D.stationaryOld D.movingOuter D.neighborhoodMotions_agree (t, z)

/-- The original old space stays fixed during the full neighborhood deformation. -/
def oldDeformation : (ContinuousMap.id D.oldNeighborhood).HomotopyRel
    (D.oldInclusion.comp D.oldRetraction) (range D.oldInclusion) where
  toFun := D.neighborhoodMotion
  continuous_toFun := D.neighborhoodMotion.continuous
  map_zero_left x := by
    have hx : x ∈ range D.oldInclusion ∪ range D.outerInclusion := by
      rw [D.oldNeighborhood_cover]
      trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact D.neighborhoodMotion_old 0 a
    · rw [D.neighborhoodMotion_outer]
      exact congrArg D.outerInclusion (OuterDisk.deformation.toHomotopy.map_zero_left z)
  map_one_left x := by
    change D.neighborhoodMotion (1, x) = D.oldInclusion (D.oldRetraction x)
    have hx : x ∈ range D.oldInclusion ∪ range D.outerInclusion := by
      rw [D.oldNeighborhood_cover]
      trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · rw [D.neighborhoodMotion_old, D.oldRetraction_old]
    · rw [D.neighborhoodMotion_outer, D.oldRetraction_outer]
      exact congrArg D.outerInclusion (OuterDisk.deformation.toHomotopy.map_one_left z)
  prop' t x hx := by
    obtain ⟨a, rfl⟩ := hx
    exact D.neighborhoodMotion_old t a

/-- The actual inclusion into the old-space neighborhood is a homotopy equivalence. -/
def oldHomotopyEquiv : D.old ≃ₕ D.oldNeighborhood where
  toFun := D.oldInclusion
  invFun := D.oldRetraction
  left_inv := by
    have heq : D.oldRetraction.comp D.oldInclusion = ContinuousMap.id D.old :=
      ContinuousMap.ext D.oldRetraction_old
    rw [heq]
  right_inv := ⟨D.oldDeformation.toHomotopy.symm⟩

theorem oldHomotopyEquiv_apply (a : D.old) : D.oldHomotopyEquiv a = D.oldInclusion a := rfl

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
