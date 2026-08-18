/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.Alternating
import ErdosProblems.Erdos186.PZ.Intersection.ActualStepInverse
import ErdosProblems.Erdos186.PZ.Intersection.BoundedRelation
import ErdosProblems.Erdos186.PZ.Intersection.CanonicalPostCFPAssembly
import ErdosProblems.Erdos186.PZ.Intersection.CanonicalRoundingCore
import ErdosProblems.Erdos186.PZ.Intersection.CenteredZonotope
import ErdosProblems.Erdos186.PZ.Intersection.CommonWitness
import ErdosProblems.Erdos186.PZ.Intersection.ConcreteSideSelection
import ErdosProblems.Erdos186.PZ.Intersection.ControlledSideSelection
import ErdosProblems.Erdos186.PZ.Intersection.ConvexPools
import ErdosProblems.Erdos186.PZ.Intersection.CoreRetention
import ErdosProblems.Erdos186.PZ.Intersection.CovolumeCovering
import ErdosProblems.Erdos186.PZ.Intersection.DeterminantBounds
import ErdosProblems.Erdos186.PZ.Intersection.DilationVolume
import ErdosProblems.Erdos186.PZ.Intersection.Equation15
import ErdosProblems.Erdos186.PZ.Intersection.FullRankObstruction
import ErdosProblems.Erdos186.PZ.Intersection.GAPErrorBox
import ErdosProblems.Erdos186.PZ.Intersection.Irreducibility
import ErdosProblems.Erdos186.PZ.Intersection.Lattice
import ErdosProblems.Erdos186.PZ.Intersection.Main
import ErdosProblems.Erdos186.PZ.Intersection.NegateWitness
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionBox
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionContainment
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionCardinality
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionNumerics
import ErdosProblems.Erdos186.PZ.Intersection.ResidualAbsorption
import ErdosProblems.Erdos186.PZ.Intersection.SideGeometryAssembly
import ErdosProblems.Erdos186.PZ.Intersection.SideLattice
import ErdosProblems.Erdos186.PZ.Intersection.SideLatticeAssembly
import ErdosProblems.Erdos186.PZ.Intersection.SideSelection
import ErdosProblems.Erdos186.PZ.Intersection.SideTarget
import ErdosProblems.Erdos186.PZ.Intersection.SelectedFullRank
import ErdosProblems.Erdos186.PZ.Intersection.SourceCoreBounds
import ErdosProblems.Erdos186.PZ.Intersection.SourceSideSelection

/-!
# The Pham--Zakharov intersection argument

This module collects the finite balancing, zonotope, rounding, lattice, and
common-subset-sum components of the intersection argument used in Theorem 4.
-/
