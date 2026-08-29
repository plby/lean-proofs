/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLocalizedFinalCertificate

/-!
# Public half-way projection from localized final certificates

The localized certificate retains a separating stopover, but only the
terminal-boundary inclusion required by `IsLinkageBetween`.  Consequently
it projects to the ordinary public half-way clause without asserting the
false exact-terminal-frontier strengthening.
-/

noncomputable section

open Cardinal

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- Per-web producer of the sound localized final certificate. -/
def LocalizedFairResolutionCertificateCompiler
    (Gamma : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    Nonempty
      (SeparatingResolvedBlueprintRemainderCertificate Gamma A0 kappa)

/-- A localized fair-resolution certificate gives the ordinary half-way
clause, retaining separation internally but making no exact-frontier
claim. -/
theorem halfwayClauseAt_of_localizedFairResolutionCertificateCompiler
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : LocalizedFairResolutionCertificateCompiler Gamma kappa) :
    HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  let C := (hcompile A0 hA0 hcard).some
  obtain ⟨W, hstop, hlinks, hheight⟩ :=
    C.exists_separatingHalfwayLinkage
  exact ⟨W, halfwayLinkageOfAltitude_of_stopover
    hstop.stopover hlinks hheight⟩

/-- Uniform localized producer at the cardinal-induction seam. -/
def UniversalLocalizedFairResolutionCertificateCompiler
    (V : Type u) : Prop :=
  ∀ kappa : Cardinal.{u},
    UniversalCardinalInductionBelow V kappa →
    UniversalExtensionClauseAt V kappa →
    ℵ₀ ≤ kappa →
    ∀ Gamma : DWeb V, Gamma.IsUnhindered →
      LocalizedFairResolutionCertificateCompiler Gamma kappa

/-- Public ordinary half-way step from the sound localized final
certificate producer. -/
theorem halfwayClauseStep_of_localizedFairResolutionCertificateCompiler
    (hcompile : UniversalLocalizedFairResolutionCertificateCompiler V) :
    ∀ kappa : Cardinal.{u},
      UniversalCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      ℵ₀ ≤ kappa →
      ∀ Gamma : DWeb V, Gamma.IsUnhindered →
        HalfwayClauseAt Gamma kappa := by
  intro kappa hlower hext hkappa Gamma hGamma
  exact halfwayClauseAt_of_localizedFairResolutionCertificateCompiler
    (hcompile kappa hlower hext hkappa Gamma hGamma)

end CardinalInduction
end Erdos599
