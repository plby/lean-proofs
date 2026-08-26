/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCoordinateMixedDynamicBounds
import ErdosProblems.Erdos547b.Claim616CoordinateMixedDynamicEmbedding

/-!
# Load bounds for a nonselected mixed dynamic hierarchy

The Claim 6.15 coordinate layout has no two-pair selected step.  This module
packages the remaining raw-pool inequalities and uses the literal coordinate
pool load to discharge every deletion caused by an earlier hierarchy prefix.
The only prefix-dependent input left is the degree of the already embedded
parent into the undeleted raw endpoint.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicResidual

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds.HierarchicalSegmentForest
open Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding

universe u v

/-- Prefix-independent pool-capacity bounds, together with the one genuine
prefix-dependent parent-degree bound, for a hierarchy with no selected
two-pair steps. -/
structure MixedDynamicNonselectedLoadFacts
    {r s : ℕ} {B : Type u} {Pool : Type v}
    [Fintype B] [DecidableEq B] [DecidableEq Pool]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (originalImage : Fin r → B)
    (rootOnly : Fin s → Prop)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (pairPool : Fin s → Fin 2 → Pool)
    (orient : Fin s → Fin 2 ≃ Fin 2)
    (whole raw : Pool → Finset B)
    (rho : ℝ) (pairDensity : Fin s → ℝ) : Prop where
  root_only_degree : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    rootOnly i →
    coordinatePoolLoad F rootPool interiorPool (rootPool i) <
      #((raw (rootPool i)).filter
        (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
          i prior)))
  available_capacity : ∀ i c, ¬ rootOnly i →
    rho * (#(whole (pairPool i c)) : ℝ) +
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) ≤
      #(raw (pairPool i c))
  parent_degree : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i →
    1 + rho * (#(whole (pairPool i (orient i 0))) : ℝ) +
        coordinatePoolLoad F rootPool interiorPool
          (pairPool i (orient i 0)) ≤
      #((raw (pairPool i (orient i 0))).filter
        (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
          i prior)))
  density_gap_nonneg : ∀ i, ¬ rootOnly i → 0 ≤ pairDensity i - rho
  pair_capacity : ∀ i c, ¬ rootOnly i →
    (F.segments.size i : ℝ) + rho * (#(whole (pairPool i c)) : ℝ) + 1 +
        (pairDensity i - rho) *
          coordinatePoolLoad F rootPool interiorPool (pairPool i c) ≤
      (pairDensity i - rho) * #(raw (pairPool i c))

namespace MixedDynamicNonselectedLoadFacts

variable {r s : ℕ} {B : Type u} {Pool : Type v}
variable [Fintype B] [DecidableEq B] [DecidableEq Pool]
variable (F : HierarchicalSegmentForest r s)
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (originalImage : Fin r → B)
variable (rootOnly selected : Fin s → Prop)
variable (rootPool : Fin s → Pool)
variable (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
variable (pairPool : Fin s → Fin 2 → Pool)
variable (orient : Fin s → Fin 2 ≃ Fin 2)
variable (whole raw : Pool → Finset B)
variable (rho : ℝ) (rootDensity pairDensity : Fin s → ℝ)

/-- Literal pool-load inequalities imply all six dynamic residual facts when
the source layout has no selected two-pair segments. -/
theorem toResidualFacts
    (hselected : ∀ i, ¬ selected i)
    (H : MixedDynamicNonselectedLoadFacts F G originalImage rootOnly rootPool
      interiorPool pairPool orient whole raw rho pairDensity) :
    MixedDynamicResidualFacts F G originalImage rootOnly selected rootPool
      interiorPool pairPool orient whole raw rho rootDensity pairDensity := by
  classical
  refine
    { root_only_nonempty := ?_
      available_large := ?_
      selected_root_large := ?_
      selected_root_margin := ?_
      parent_neighbours := ?_
      pair_margin := ?_ }
  · intro i prior hi
    exact mixedSelectedRootAvailable_nonempty_of_load F G rootPool interiorPool
      raw originalImage i prior (H.root_only_degree i prior hi)
  · intro i prior c hi
    exact mixedAvailable_large_of_load F G rootPool interiorPool pairPool raw
      whole rho i prior c (H.available_capacity i c hi)
  · intro i prior hi hs
    exact False.elim ((hselected i) hs)
  · intro i prior hi hs
    exact False.elim ((hselected i) hs)
  · intro i prior hi hs
    have hp := mixedParent_neighbours_of_load F G rootPool interiorPool
      pairPool raw originalImage
      (1 + rho * (#(whole (pairPool i (orient i 0))) : ℝ)) i prior
      (orient i 0) (H.parent_degree i prior hi)
    simpa [add_assoc] using hp
  · intro i prior c hi
    exact mixedAvailable_pairMargin_of_load F G rootPool interiorPool pairPool
      raw whole rho (pairDensity i)
        ((F.segments.size i : ℝ) +
          rho * (#(whole (pairPool i c)) : ℝ) + 1)
      i prior c (H.density_gap_nonneg i hi) (H.pair_capacity i c hi)

end MixedDynamicNonselectedLoadFacts

end Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicResidual

#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicResidual.MixedDynamicNonselectedLoadFacts.toResidualFacts
