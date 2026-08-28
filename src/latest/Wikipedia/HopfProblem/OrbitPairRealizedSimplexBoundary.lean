import Wikipedia.HopfProblem.OrbitPairSubdivisionRealizedAttachments

/-!
# The native realized boundary is the literal barycentric boundary

The standard-coordinate homeomorphism takes the realized boundary
inclusion exactly onto the set where a barycentric coordinate vanishes.
The converse uses the already checked positive supporting face. This
gives a homeomorphism of the actual boundary realization with the literal
geometric boundary, including dimension zero.
-/

noncomputable section

universe u

open CategoryTheory Simplicial Topology

namespace Wikipedia.HopfProblem.OrbitPair.RealizedSimplexBoundary

open FirstHurewicz SecondHurewicz.SimplyConnected RealizationSimplex Subdivision

def coordinateMap (n : ℕ) : C(SSet.toTop.obj (SSet.boundary.{u} n : SSet), Simplex n) :=
  (⟨standardCoordinates n, (standardCoordinates n).continuous⟩ :
    C(SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌), Simplex n)).comp
      (SSet.toTop.map (SSet.boundary n).ι).hom

theorem coordinateMap_characteristic (n k : ℕ)
    (x : (SSet.boundary.{u} n : SSet) _⦋k⦌) (t : Simplex k) :
    coordinateMap n (characteristic (SSet.boundary n : SSet) k x t) =
      stdSimplex.map (SSet.stdSimplex.objEquiv x.val).toOrderHom t := by
  change standardCoordinates n ((SSet.toTop.map (SSet.boundary n).ι)
    (characteristic (SSet.boundary n : SSet) k x t)) = _
  rw [realizedMap_characteristic, standardCoordinates_characteristic]
  rfl

theorem coordinateMap_mem_boundary (n : ℕ) (z : SSet.toTop.obj (SSet.boundary.{u} n : SSet)) :
    coordinateMap n z ∈ simplexBoundary n := by
  obtain ⟨k, x, t, _, rfl⟩ := exists_positive_nonDegenerate (SSet.boundary n : SSet) z
  obtain ⟨i, hi⟩ := (SSet.mem_boundary_iff_notMem_range x.val.val).mp x.val.property
  refine ⟨i, ?_⟩
  rw [coordinateMap_characteristic]
  apply le_antisymm _ (stdSimplex.zero_le _ _)
  apply le_of_not_gt
  intro hp
  obtain ⟨j, hj, _⟩ :=
    (SimplexSupport.map_pos_iff (SSet.stdSimplex.objEquiv x.val.val).toOrderHom t i).mp hp
  exact hi ⟨j, hj⟩

def coordinates (n : ℕ) :
    C(SSet.toTop.obj (SSet.boundary.{u} n : SSet), ↥(simplexBoundary n)) where
  toFun z := ⟨coordinateMap n z, coordinateMap_mem_boundary n z⟩
  continuous_toFun := (coordinateMap n).continuous.subtype_mk _

theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates.{u} n) := by
  intro z w h
  apply realizedMap_injective (SSet.boundary n).ι
  apply (standardCoordinates n).injective
  exact congrArg Subtype.val h

theorem coordinates_surjective (n : ℕ) : Function.Surjective (coordinates.{u} n) := by
  intro s
  let a := SimplexSupport.face n s.val
  obtain ⟨i, hi⟩ := s.property
  have hn : i ∉ Set.range a.inclusion.toOrderHom := by
    rintro ⟨j, hj⟩
    have hp := (SimplexSupport.map_pos_iff a.inclusion.toOrderHom a.point i).mpr
      ⟨j, hj, a.positive j⟩
    rw [a.map_point, hi] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hx : (SSet.stdSimplex.objEquiv.symm a.inclusion :
      (SSet.stdSimplex.{u}.obj ⦋n⦌) _⦋a.dim⦌) ∈ (SSet.boundary n).obj (Opposite.op ⦋a.dim⦌) :=
    (SSet.mem_boundary_iff_notMem_range _).mpr ⟨i, hn⟩
  let x : (SSet.boundary.{u} n : SSet) _⦋a.dim⦌ := ⟨SSet.stdSimplex.objEquiv.symm a.inclusion, hx⟩
  refine ⟨characteristic (SSet.boundary n : SSet) a.dim x a.point, ?_⟩
  apply Subtype.ext
  change coordinateMap n (characteristic (SSet.boundary n : SSet) a.dim x a.point) = s.val
  rw [coordinateMap_characteristic]
  exact a.map_point

theorem coordinates_isClosedEmbedding (n : ℕ) : IsClosedEmbedding (coordinates.{u} n) :=
  (coordinates n).continuous.isClosedEmbedding (coordinates_injective n)

def homeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{u} n : SSet) ≃ₜ ↥(simplexBoundary n) :=
  (coordinates_isClosedEmbedding n).isEmbedding.toHomeomorphOfSurjective
    (coordinates_surjective n)

theorem homeomorph_inclusion (n : ℕ) (z : SSet.toTop.obj (SSet.boundary.{u} n : SSet)) :
    (homeomorph n z).val = standardCoordinates n ((SSet.toTop.map (SSet.boundary n).ι) z) := rfl

end Wikipedia.HopfProblem.OrbitPair.RealizedSimplexBoundary
