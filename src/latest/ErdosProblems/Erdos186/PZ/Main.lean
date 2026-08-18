/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.LemmaSeven
import ErdosProblems.Erdos186.PZ.OneStepConstruction
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeConstruction
import ErdosProblems.Erdos186.CFP.IntegerHigherDimensionalFinal

/-!
# Composition boundary for the Pham--Zakharov upper bound

This is the integration point between the remaining source existence
theorems and the finite density iteration.  The source-specialized post-CFP
intersection is constructed internally by the one-step assembly.
-/

namespace Erdos186.PZ

/-- Conditional end-to-end Pham--Zakharov box bound from the genuine source
inputs still exposed by the one-step assembly. -/
theorem pzBoxBound_of_components
    (assemble : OneStepAssemblyStatement)
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5)
    (hReplacement : Reduction.IrreducibleReplacementStatement)
    (hConvexDensity : ConvexDensity.PZLemmaOneStatement) :
    PZBoxBound :=
  FinalIteration.pzBoxBound_of_oneStep
    (assemble hCFP hReplacement hConvexDensity)

/-- The quantitative guarded-trace construction discharges the complete
Pham--Zakharov irreducible-replacement boundary.  This downstream wrapper
therefore leaves only CFP, convex density, and the source one-step
assembly. -/
theorem pzBoxBound_of_cfp_convexDensity
    (assemble : OneStepAssemblyStatement)
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5)
    (hConvexDensity : ConvexDensity.PZLemmaOneStatement) :
    PZBoxBound :=
  pzBoxBound_of_components assemble hCFP
    Reduction.irreducibleReplacementStatement hConvexDensity

/-- The proved replacement and convex-density theorems reduce the box bound
to the remaining CFP corollary and the concrete source one-step assembly. -/
theorem pzBoxBound_of_cfp
    (assemble : OneStepAssemblyStatement)
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5) :
    PZBoxBound :=
  pzBoxBound_of_cfp_convexDensity assemble hCFP
    ConvexDensity.convexDensityStatement

/-- The proved one-step assembly reduces the complete Pham--Zakharov box
bound to the source-correct nonempty CFP corollary alone. -/
theorem pzBoxBound_of_nonemptyHigherDimensionalCorollary5
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5) :
    PZBoxBound :=
  pzBoxBound_of_cfp OneStepAssembly.oneStepAssembly hCFP

/-- With the unconditional Bilu--Freiman theorem and projected
properization internalized, the Pham--Zakharov box bound depends only on the
remaining centered large-input coverage constructor. -/
theorem pzBoxBound_of_centeredCoverage
    (hcoverage : CFP.UniformCenteredLargeInputLogLossCoverage) :
    PZBoxBound :=
  pzBoxBound_of_nonemptyHigherDimensionalCorollary5
    (CFP.nonemptyHigherDimensionalCorollary5_of_centeredCoverage hcoverage)

/-- The unconditional Pham--Zakharov integer-box bound. -/
theorem pzBoxBound : PZBoxBound :=
  pzBoxBound_of_nonemptyHigherDimensionalCorollary5
    CFP.nonemptyHigherDimensionalCorollary5

#print axioms Erdos186.PZ.pzBoxBound

end Erdos186.PZ
