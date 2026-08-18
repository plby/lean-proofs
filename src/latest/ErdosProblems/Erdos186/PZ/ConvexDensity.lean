/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.Definitions
import ErdosProblems.Erdos186.PZ.ConvexDensity.DimensionOne
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes
import ErdosProblems.Erdos186.PZ.ConvexDensity.AffineSlab
import ErdosProblems.Erdos186.PZ.ConvexDensity.DyadicCells
import ErdosProblems.Erdos186.PZ.ConvexDensity.RelativeDyadicCells
import ErdosProblems.Erdos186.PZ.ConvexDensity.InitialRegularization
import ErdosProblems.Erdos186.PZ.ConvexDensity.GridPartition
import ErdosProblems.Erdos186.PZ.ConvexDensity.InitialBoundary
import ErdosProblems.Erdos186.PZ.ConvexDensity.SeparatedCells
import ErdosProblems.Erdos186.PZ.ConvexDensity.BoundaryWitnesses
import ErdosProblems.Erdos186.PZ.ConvexDensity.ConvexApproxND
import ErdosProblems.Erdos186.PZ.ConvexDensity.Subgradient
import ErdosProblems.Erdos186.PZ.ConvexDensity.ConvexApproximation
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphDensity2D
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphDensity2DAmbient
import ErdosProblems.Erdos186.PZ.ConvexDensity.IndexedGraphDensity
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphWindowNormalization
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphWindowAffine
import ErdosProblems.Erdos186.PZ.ConvexDensity.UnitGraphGrid
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphOscillation
import ErdosProblems.Erdos186.PZ.ConvexDensity.LargeGraphBranch
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphDensityND
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphSlabAmbient
import ErdosProblems.Erdos186.PZ.ConvexDensity.RetainedFibers
import ErdosProblems.Erdos186.PZ.ConvexDensity.ConvexHullClip
import ErdosProblems.Erdos186.PZ.ConvexDensity.Normalization
import ErdosProblems.Erdos186.PZ.ConvexDensity.LinearNormalization
import ErdosProblems.Erdos186.PZ.ConvexDensity.WidthInradius
import ErdosProblems.Erdos186.PZ.ConvexDensity.WidthInradiusQuantitative
import ErdosProblems.Erdos186.PZ.ConvexDensity.Thickening
import ErdosProblems.Erdos186.PZ.ConvexDensity.FiniteCap
import ErdosProblems.Erdos186.PZ.ConvexDensity.CapToGraph
import ErdosProblems.Erdos186.PZ.ConvexDensity.HouseholderCap
import ErdosProblems.Erdos186.PZ.ConvexDensity.CenteredBoundary
import ErdosProblems.Erdos186.PZ.ConvexDensity.BoundaryGraph
import ErdosProblems.Erdos186.PZ.ConvexDensity.Numerics
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchNumerics
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphScale
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchAssembly
import ErdosProblems.Erdos186.PZ.ConvexDensity.FullReduction
import ErdosProblems.Erdos186.PZ.ConvexDensity.EnclosingBox
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedGeometry
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedCore
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedCoreProof

/-!
# The Pham--Zakharov convex-density interface

This module collects the formally verified parts of Section 2 of
Pham--Zakharov.  `PZLemmaOneStatement` is the literal all-dimensional
Lebesgue-volume statement of their Lemma 1.  The one-dimensional specialization
is completely discharged by the median obstruction
`pzLemmaOneStatement_dimension_one`.

The remaining modules expose the exact finite ingredients used in positive
codimension: dyadic mass regularization, quantitative separation of heavy
cells, affine-slab volume formulae, arbitrary-dimensional coordinate/fiber
pigeonholing, and the power--log estimates used to choose the small parameter.
-/

namespace Erdos186.PZ.ConvexDensity

/-- Public source-shaped name for the fully proved one-dimensional case of
Pham--Zakharov's convex-density lemma. -/
theorem phamZakharov_convexDensity_dimension_one :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ tau deltaZero : ℝ,
        0 < tau ∧ tau < 1 ∧ 0 < deltaZero ∧
        ∀ delta : ℝ, 0 < delta → delta < deltaZero →
          ∃ largeEnough : ℕ,
            ∀ (Omega : Set (EuclideanPoint 1))
                (X : Finset (EuclideanPoint 1)),
              IsConvexBody Omega →
              (X : Set (EuclideanPoint 1)) ⊆ Omega →
              largeEnough ≤ X.card →
              ConvexGeometry.IsDeltaConvexPosition delta X →
              ConvexDensityOutput epsilon tau delta Omega X :=
  pzLemmaOneStatement_dimension_one

#print axioms phamZakharov_convexDensity_dimension_one

end Erdos186.PZ.ConvexDensity
