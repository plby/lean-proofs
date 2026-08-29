/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySchedulerConstruction

/-!
# Scheduler output for the source-faithful cardinal induction

This small integration module projects the provenance-carrying scheduler
certificate to the separating half-way clause retained by
`CardinalInductionAt`.  It constructs no certificate: the compiler remains
the explicit graph-theoretic input.
-/

noncomputable section

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

open Cardinal

/-- The scheduler's separating global certificate is exactly the producer
for the strong half-way half of the simultaneous induction. -/
theorem separatingHalfwayClauseAt_of_separatingGloballyResolvedBlueprintCompiler
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile :
      SeparatingGloballyResolvedBlueprintCompiler Gamma kappa) :
    SeparatingHalfwayClauseAt Gamma kappa := by
  intro A₀ hA₀ hcard
  let S := (hcompile A₀ hA₀ hcard).some
  obtain ⟨W, hstop, hlinks, hheight⟩ :=
    S.exists_separatingHalfwayLinkage
  exact ⟨W, S.certificate.stopover, hstop, hlinks, hheight⟩

/-- A provenance-carrying fair 9.34 scheduler is already the complete
producer for the strong half-way clause; this is the final projection used by
the cardinal-induction step. -/
theorem separatingHalfwayClauseAt_of_fairResolutionCertificateCompiler
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : FairResolutionCertificateCompiler Gamma kappa) :
    SeparatingHalfwayClauseAt Gamma kappa :=
  separatingHalfwayClauseAt_of_separatingGloballyResolvedBlueprintCompiler
    (separatingGloballyResolvedBlueprintCompiler_of_fairResolution hcompile)

/-- Uniform scheduler constructor with precisely the hypotheses available at
the half-way half of the simultaneous cardinal induction. -/
def UniversalFairResolutionCertificateCompiler (V : Type u) : Prop :=
  ∀ kappa : Cardinal.{u},
    UniversalCardinalInductionBelow V kappa →
    UniversalExtensionClauseAt V kappa →
    ℵ₀ ≤ kappa →
    ∀ Gamma : DWeb V, Gamma.IsUnhindered →
      FairResolutionCertificateCompiler Gamma kappa

/-- Once the actual fair scheduler has been constructed, its output has
exactly the strong signature expected by
`universalCardinalInduction_of_steps`. -/
theorem halfwayClauseStep_of_fairResolutionCertificateCompiler
    (hcompile : UniversalFairResolutionCertificateCompiler V) :
    ∀ kappa : Cardinal.{u},
      UniversalCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      ℵ₀ ≤ kappa →
      ∀ Gamma : DWeb V, Gamma.IsUnhindered →
        SeparatingHalfwayClauseAt Gamma kappa := by
  intro kappa hlower hext hkappa Gamma hGamma
  exact separatingHalfwayClauseAt_of_fairResolutionCertificateCompiler
    (hcompile kappa hlower hext hkappa Gamma hGamma)

end CardinalInduction
end Erdos599
