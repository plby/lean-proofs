import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePaths
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBoundary
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleIntersectionCycles

/-!
# Actual arc cross-chains and their intersection boundaries

Crossing the two positively oriented arc paths with a cycle gives actual
chains in the two members of the circle-product cover. Their boundaries
are the two signed images of the upper-minus-lower intersection cycle.
The ambient images are the actual edge cross products of the circle paths.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology CircleTopology CirclePaths

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed right factor removes the right-boundary term in every degree. -/
theorem crossProductEdge_boundary_of_right_cycle (n : ℕ) (a : Chains X 1)
    (b : Cycle (singularComplex Y) n) :
    ((singularComplex (X × Y)).d (n + 1) n).hom (crossProductEdge X Y n a b.1) =
      crossProductZeroLeft X Y n (((singularComplex X).d 1 0).hom a) b.1 := by
  cases n with
  | zero => exact crossProductEdge_boundary_zero a b.1
  | succ n =>
      have hb : ((singularComplex Y).d (n + 1) n).hom b.1 = 0 := by
        simpa only [Nat.succ_sub_one] using
          ModuleHomology.cycle_condition (singularComplex Y) (n + 1) b
      simp only [crossProductEdge_boundary, hb, map_zero, sub_zero]

/-- The boundary of a path crossed with a cycle is endpoint insertion at
the target minus endpoint insertion at the source. -/
theorem crossProductEdge_path_boundary (n : ℕ) {x y : X} (p : Path x y)
    (b : Cycle (singularComplex Y) n) :
    ((singularComplex (X × Y)).d (n + 1) n).hom
        (crossProductEdge X Y n (pathChain p) b.1) =
      inducedChain (crossInsertLeft y) n b.1 - inducedChain (crossInsertLeft x) n b.1 := by
  rw [crossProductEdge_boundary_of_right_cycle]
  change crossProductZeroLeft X Y n (boundaryOne X (pathChain p)) b.1 = _
  rw [boundaryOne_pathChain, map_sub, LinearMap.sub_apply]
  simp only [pointChain, crossProductZeroLeft_simplex_left]
  rfl

private theorem const_prodMk_id_eq_crossInsertLeft (x : X) :
    (ContinuousMap.const Y x).prodMk (ContinuousMap.id Y) = crossInsertLeft x := by
  apply ContinuousMap.ext
  intro y
  rfl

variable (X : Type) [TopologicalSpace X]

/-- The first actual arc path crossed with a cycle, in the first open member. -/
def uCrossChain (n : ℕ) (b : Cycle (singularComplex X) n) : Chains (productU X) (n + 1) :=
  inducedChain ((productUHomeomorph X).symm : C(arcU × X, productU X)) (n + 1)
    (crossProductEdge arcU X n (pathChain uPath) b.1)

/-- The second actual arc path crossed with a cycle, in the second open member. -/
def vCrossChain (n : ℕ) (b : Cycle (singularComplex X) n) : Chains (productV X) (n + 1) :=
  inducedChain ((productVHomeomorph X).symm : C(arcV × X, productV X)) (n + 1)
    (crossProductEdge arcV X n (pathChain vPath) b.1)

/-- The first arc cross-chain has the positive intersection-difference boundary. -/
theorem uCrossChain_boundary (n : ℕ) (b : Cycle (singularComplex X) n) :
    ((singularComplex (productU X)).d (n + 1) n).hom (uCrossChain X n b) =
      inducedChain (productIntersectionToU X) n (intersectionDifferenceCycle X n b).1 := by
  rw [uCrossChain, ← inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub]
  congr 1
  · have h := congrArg (fun f => inducedChain f n b.1)
      (threeQuarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft, inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h := congrArg (fun f => inducedChain f n b.1)
      (quarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft, inducedChain_comp,
      LinearMap.comp_apply] using h.symm

/-- The return arc has the negative of the same intersection-difference boundary. -/
theorem vCrossChain_boundary (n : ℕ) (b : Cycle (singularComplex X) n) :
    ((singularComplex (productV X)).d (n + 1) n).hom (vCrossChain X n b) =
      -inducedChain (productIntersectionToV X) n (intersectionDifferenceCycle X n b).1 := by
  rw [vCrossChain, ← inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub, neg_sub]
  congr 1
  · have h := congrArg (fun f => inducedChain f n b.1)
      (quarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft, inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h := congrArg (fun f => inducedChain f n b.1)
      (threeQuarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft, inducedChain_comp,
      LinearMap.comp_apply] using h.symm

/-- The first arc chain maps to the actual product of its ambient circle path. -/
theorem uCrossChain_inclusion (n : ℕ) (b : Cycle (singularComplex X) n) :
    inducedChain (productUInclusion X) (n + 1) (uCrossChain X n b) =
      crossProductEdge Circle X n (pathChain uCirclePath) b.1 := by
  have hi : (productUInclusion X).comp
      ((productUHomeomorph X).symm : C(arcU × X, productU X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(arcU, Circle)).prodMap
        (ContinuousMap.id X) := rfl
  rw [uCrossChain, ← LinearMap.comp_apply, ← inducedChain_comp, hi,
    crossProductEdge_natural, inducedChain_id, LinearMap.id_apply, inducedChain_pathChain]
  rfl

/-- The second arc chain maps to the actual product of its ambient circle path. -/
theorem vCrossChain_inclusion (n : ℕ) (b : Cycle (singularComplex X) n) :
    inducedChain (productVInclusion X) (n + 1) (vCrossChain X n b) =
      crossProductEdge Circle X n (pathChain vCirclePath) b.1 := by
  have hi : (productVInclusion X).comp
      ((productVHomeomorph X).symm : C(arcV × X, productV X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(arcV, Circle)).prodMap
        (ContinuousMap.id X) := rfl
  rw [vCrossChain, ← LinearMap.comp_apply, ← inducedChain_comp, hi,
    crossProductEdge_natural, inducedChain_id, LinearMap.id_apply, inducedChain_pathChain]
  rfl

/-- Adding the ambient arc images gives the actual cross product with their sum. -/
theorem arcCrossChains_inclusion_sum (n : ℕ) (b : Cycle (singularComplex X) n) :
    inducedChain (productUInclusion X) (n + 1) (uCrossChain X n b) +
      inducedChain (productVInclusion X) (n + 1) (vCrossChain X n b) =
        crossProductEdge Circle X n (pathChain uCirclePath + pathChain vCirclePath) b.1 := by
  rw [uCrossChain_inclusion, vCrossChain_inclusion, map_add, LinearMap.add_apply]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
