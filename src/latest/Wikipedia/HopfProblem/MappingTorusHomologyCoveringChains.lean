import Wikipedia.HopfProblem.MappingTorusHomologyCoveringCharts
import Wikipedia.HopfProblem.MappingTorusHomologyCoveringNorm
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTwoChainConnecting

/-!
# Actual small chains for a finite-order mapping-torus covering

The chart strips applied to the unit-interval edge crossed with a fibre
cycle give actual chains in the two open members. The return strip ends
at the next lower section. Summing over a finite order cancels this shift,
so the two sums have opposite intersection boundaries. The actual
Mayer--Vietoris connecting homomorphism therefore returns the sum of the
upper-minus-lower section cycles.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open MappingTorus MappingTorus.HomologyCover
open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)

/-- The unit-interval edge crossed with the fibre cycle, in the first chart strip. -/
def uCrossChain (k n : ℕ) (b : ModuleHomology.Cycle (singularComplex X) n) :
    Chains (U f) (n + 1) :=
  inducedChain (uStrip f k) (n + 1)
    (crossProductEdge unitInterval X n (pathChain Path.id) b.1)

/-- The corresponding actual return-strip chain in the second open member. -/
def vCrossChain (k n : ℕ) (b : ModuleHomology.Cycle (singularComplex X) n) :
    Chains (V f) (n + 1) :=
  inducedChain (vStrip f k) (n + 1)
    (crossProductEdge unitInterval X n (pathChain Path.id) b.1)

/-- The first strip runs from the lower section to the upper section in the same turn. -/
theorem uCrossChain_boundary (k n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ((singularComplex (U f)).d (n + 1) n).hom (uCrossChain f k n b) =
      inducedChain (intersectionToU f) n
        (inducedChain (upperSection f k) n b.1 - inducedChain (lowerSection f k) n b.1) := by
  rw [uCrossChain, ← inducedChain_boundary, crossProductEdge_path_boundary,
    map_sub, map_sub]
  congr 1
  · have h := congrArg (fun g => inducedChain g n b.1) (uStrip_one f k)
    simpa only [inducedChain_comp, LinearMap.comp_apply] using h
  · have h := congrArg (fun g => inducedChain g n b.1) (uStrip_zero f k)
    simpa only [inducedChain_comp, LinearMap.comp_apply] using h

/-- The return strip runs from the upper section to the next lower section. -/
theorem vCrossChain_boundary (k n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ((singularComplex (V f)).d (n + 1) n).hom (vCrossChain f k n b) =
      inducedChain (intersectionToV f) n
        (inducedChain (lowerSection f (k + 1)) n b.1 -
          inducedChain (upperSection f k) n b.1) := by
  rw [vCrossChain, ← inducedChain_boundary, crossProductEdge_path_boundary,
    map_sub, map_sub]
  congr 1
  · have h := congrArg (fun g => inducedChain g n b.1) (vStrip_one f k)
    simpa only [inducedChain_comp, LinearMap.comp_apply] using h
  · have h := congrArg (fun g => inducedChain g n b.1) (vStrip_zero f k)
    simpa only [inducedChain_comp, LinearMap.comp_apply] using h

/-- The actual sum of the first-chart strip chains over the finite subdivision. -/
def uCrossChainSum (m n : ℕ) (b : ModuleHomology.Cycle (singularComplex X) n) :
    Chains (U f) (n + 1) :=
  ∑ k ∈ Finset.range m, uCrossChain f k n b

/-- The actual sum of the second-chart strip chains over the same subdivision. -/
def vCrossChainSum (m n : ℕ) (b : ModuleHomology.Cycle (singularComplex X) n) :
    Chains (V f) (n + 1) :=
  ∑ k ∈ Finset.range m, vCrossChain f k n b

/-- The actual upper-minus-lower intersection cycle summed over all turns. -/
def differenceCycle (m n : ℕ) (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.Cycle (singularComplex (U f ∩ V f : Set (Torus f))) n :=
  ∑ k ∈ Finset.range m,
    (ModuleHomology.mapCycles (singularChainMap (upperSection f k)) n b -
      ModuleHomology.mapCycles (singularChainMap (lowerSection f k)) n b)

@[simp] theorem differenceCycle_val (m n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    (differenceCycle f m n b).1 =
      ∑ k ∈ Finset.range m,
        (inducedChain (upperSection f k) n b.1 - inducedChain (lowerSection f k) n b.1) := by
  simp only [differenceCycle, Submodule.coe_sum, Submodule.coe_sub,
    ModuleHomology.mapCycles_val]

/-- Returning to the same lower section makes the shifted endpoint sum unchanged. -/
theorem lowerSection_chain_sum_shift (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    (∑ k ∈ Finset.range m, inducedChain (lowerSection f (k + 1)) n b.1) =
      ∑ k ∈ Finset.range m, inducedChain (lowerSection f k) n b.1 := by
  apply add_right_cancel (b := inducedChain (lowerSection f 0) n b.1)
  calc
    _ = ∑ k ∈ Finset.range (m + 1), inducedChain (lowerSection f k) n b.1 :=
      (Finset.sum_range_succ' (fun k => inducedChain (lowerSection f k) n b.1) m).symm
    _ = _ := by rw [Finset.sum_range_succ, lowerSection_period f m hf]

/-- The summed first-chart chain has the positive difference-cycle boundary. -/
theorem uCrossChainSum_boundary (m n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ((singularComplex (U f)).d (n + 1) n).hom (uCrossChainSum f m n b) =
      inducedChain (intersectionToU f) n (differenceCycle f m n b).1 := by
  simp only [uCrossChainSum, differenceCycle_val, map_sum, uCrossChain_boundary]

/-- Finite-order endpoint cancellation gives exactly the opposite second-chart boundary. -/
theorem vCrossChainSum_boundary (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ((singularComplex (V f)).d (n + 1) n).hom (vCrossChainSum f m n b) =
      -inducedChain (intersectionToV f) n (differenceCycle f m n b).1 := by
  calc
    _ = inducedChain (intersectionToV f) n
        (∑ k ∈ Finset.range m,
          (inducedChain (lowerSection f (k + 1)) n b.1 -
            inducedChain (upperSection f k) n b.1)) := by
      simp only [vCrossChainSum, map_sum, vCrossChain_boundary]
    _ = _ := by
      rw [differenceCycle_val]
      simp only [Finset.sum_sub_distrib]
      rw [lowerSection_chain_sum_shift f m hf]
      simp only [map_sub]
      abel

/-- The difference cycle class is the sum of the actual section homology maps. -/
theorem differenceCycle_class (m n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.cycleClass (singularComplex (U f ∩ V f : Set (Torus f))) n
        (differenceCycle f m n b) =
      ∑ k ∈ Finset.range m,
        (singularHomologyMap (upperSection f k) n
            (ModuleHomology.cycleClass (singularComplex X) n b) -
          singularHomologyMap (lowerSection f k) n
            (ModuleHomology.cycleClass (singularComplex X) n b)) := by
  simp only [differenceCycle, map_sum, map_sub, ← ModuleHomology.homologyMap_cycleClass]

/-- The fixed lower-first coordinates record the two opposite homology norms. -/
theorem differenceCycle_class_coordinates (m n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    intersectionHomologyEquiv f n
        (ModuleHomology.cycleClass (singularComplex (U f ∩ V f : Set (Torus f))) n
          (differenceCycle f m n b)) =
      (-homologyNorm m f n (ModuleHomology.cycleClass (singularComplex X) n b),
        homologyNorm m f n (ModuleHomology.cycleClass (singularComplex X) n b)) := by
  rw [differenceCycle_class, map_sum]
  simp only [map_sub, upperSection_homology_coordinates, lowerSection_homology_coordinates,
    Prod.mk_sub_mk, zero_sub, sub_zero, ← prod_mk_sum, Finset.sum_neg_distrib,
    homologyNorm_apply]

/-- The actual small-chain cycle formed by the two sums with opposite boundaries. -/
def coverSmallCycle (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.Cycle (smallComplex (U f) (V f)) (n + 1) :=
  twoChainSmallCycle (U f) (V f) n
    (uCrossChainSum f m n b) (vCrossChainSum f m n b) (differenceCycle f m n b)
    (uCrossChainSum_boundary f m n b) (vCrossChainSum_boundary f m hf n b)

/-- The ambient chain is the sum of the two literal open-inclusion images. -/
theorem coverSmallCycle_ambient_val (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    (ModuleHomology.mapCycles (smallInclusion (U f) (V f)) (n + 1)
        (coverSmallCycle f m hf n b)).1 =
      inducedChain (inclusionU f) (n + 1) (uCrossChainSum f m n b) +
        inducedChain (inclusionV f) (n + 1) (vCrossChainSum f m n b) :=
  twoChainSmallCycle_ambient_val (U f) (V f) n
    (uCrossChainSum f m n b) (vCrossChainSum f m n b) (differenceCycle f m n b)
    (uCrossChainSum_boundary f m n b) (vCrossChainSum_boundary f m hf n b)

/-- Equivalently, its underlying chain is the sum of all `2m` actual strip images. -/
theorem coverSmallCycle_ambient_sum_val (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    (ModuleHomology.mapCycles (smallInclusion (U f) (V f)) (n + 1)
        (coverSmallCycle f m hf n b)).1 =
      ∑ k ∈ Finset.range m,
        (inducedChain (inclusionU f) (n + 1) (uCrossChain f k n b) +
          inducedChain (inclusionV f) (n + 1) (vCrossChain f k n b)) := by
  simp only [coverSmallCycle_ambient_val, uCrossChainSum, vCrossChainSum,
    map_sum, Finset.sum_add_distrib]

/-- The actual connecting map returns the common intersection cycle class. -/
theorem coverSmallCycle_connecting (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    mayerVietorisConnecting f n
        (ModuleHomology.cycleClass (singularComplex (Torus f)) (n + 1)
          (ModuleHomology.mapCycles (smallInclusion (U f) (V f)) (n + 1)
            (coverSmallCycle f m hf n b))) =
      ModuleHomology.cycleClass (singularComplex (U f ∩ V f : Set (Torus f))) n
        (differenceCycle f m n b) :=
  connectingHomomorphism_twoChain (U f) (V f) (U_open f) (V_open f) (cover f) n
    (uCrossChainSum f m n b) (vCrossChainSum f m n b) (differenceCycle f m n b)
    (uCrossChainSum_boundary f m n b) (vCrossChainSum_boundary f m hf n b)

/-- The actual raw Mayer--Vietoris coordinates are the signed norm pair. -/
theorem coverSmallCycle_boundaryCoordinates (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    boundaryCoordinates f n
        (ModuleHomology.cycleClass (singularComplex (Torus f)) (n + 1)
          (ModuleHomology.mapCycles (smallInclusion (U f) (V f)) (n + 1)
            (coverSmallCycle f m hf n b))) =
      (-homologyNorm m f n (ModuleHomology.cycleClass (singularComplex X) n b),
        homologyNorm m f n (ModuleHomology.cycleClass (singularComplex X) n b)) := by
  rw [boundaryCoordinates_apply, coverSmallCycle_connecting]
  exact differenceCycle_class_coordinates f m n b

end Wikipedia.HopfProblem.MappingTorusHomology.Covering
