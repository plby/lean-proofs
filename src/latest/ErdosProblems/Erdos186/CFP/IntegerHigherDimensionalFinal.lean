/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.IntegerTheoremLogLossLargeAssembly
import ErdosProblems.Erdos186.CFP.HigherDimensionalCorollaryFinal
import ErdosProblems.Erdos186.CFP.Bilu.Section93UniformGenericSharpGeometry
import ErdosProblems.Erdos186.CFP.CenteredProjectedLargeInputCoverage

/-!
# Terminal CFP composition

This file records the exact terminal dependency chain from the source
Bilu--Freiman input and the remaining centered reserve-coverage theorem to
the corrected integer and higher-dimensional CFP statements.
-/

namespace Erdos186.CFP

/-- The source-correct integer CFP statement, conditional only on the
source Bilu--Freiman theorem and the concrete centered reserve-coverage
construction. -/
theorem nonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage
    (hBF : BiluFreiman.BiluFreimanStatement)
    (hcoverage : UniformCenteredLargeInputLogLossCoverage) :
    NonemptyIntegerTheorem15 :=
  nonemptyIntegerTheorem15_of_largeInputLogLoss
    (largeInputLogLossNonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage
      hBF hcoverage)

/-- The complete corrected Appendix chain, conditional only on the source
Bilu--Freiman theorem and the concrete centered reserve-coverage
construction.  Projected properization and the small-cardinality branch are
already internal. -/
theorem nonemptyHigherDimensionalCorollary5_of_biluFreiman_of_centeredCoverage
    (hBF : BiluFreiman.BiluFreimanStatement)
    (hcoverage : UniformCenteredLargeInputLogLossCoverage) :
    NonemptyHigherDimensionalCorollary5 :=
  HigherDimensionalCorollary.nonemptyHigherDimensionalCorollary5_of_nonemptyIntegerTheorem15
    (nonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage hBF hcoverage)

/-- The source Bilu--Freiman theorem has been proved internally, so the
integer CFP conclusion now depends only on the centered large-input coverage
constructor. -/
theorem nonemptyIntegerTheorem15_of_centeredCoverage
    (hcoverage : UniformCenteredLargeInputLogLossCoverage) :
    NonemptyIntegerTheorem15 :=
  nonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage
    Bilu.Section93UniformGenericSharpGeometry.biluFreimanStatement hcoverage

/-- The complete Appendix chain after discharging Bilu--Freiman, conditional
only on the centered large-input coverage constructor. -/
theorem nonemptyHigherDimensionalCorollary5_of_centeredCoverage
    (hcoverage : UniformCenteredLargeInputLogLossCoverage) :
    NonemptyHigherDimensionalCorollary5 :=
  nonemptyHigherDimensionalCorollary5_of_biluFreiman_of_centeredCoverage
    Bilu.Section93UniformGenericSharpGeometry.biluFreimanStatement hcoverage

/-- The complete source-correct integer CFP theorem. -/
theorem nonemptyIntegerTheorem15 : NonemptyIntegerTheorem15 :=
  nonemptyIntegerTheorem15_of_centeredCoverage
    uniformCenteredLargeInputLogLossCoverage

/-- The unconditional higher-dimensional CFP corollary used by the
Pham--Zakharov iteration. -/
theorem nonemptyHigherDimensionalCorollary5 :
    NonemptyHigherDimensionalCorollary5 :=
  nonemptyHigherDimensionalCorollary5_of_centeredCoverage
    uniformCenteredLargeInputLogLossCoverage

end Erdos186.CFP

#print axioms
  Erdos186.CFP.nonemptyHigherDimensionalCorollary5_of_biluFreiman_of_centeredCoverage
#print axioms
  Erdos186.CFP.nonemptyHigherDimensionalCorollary5_of_centeredCoverage
#print axioms Erdos186.CFP.nonemptyIntegerTheorem15
#print axioms Erdos186.CFP.nonemptyHigherDimensionalCorollary5
