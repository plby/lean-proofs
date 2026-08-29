/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSplitCanonicalHistoryBase
import ErdosProblems.Erdos599.RegularWeakSplitCandidate
import ErdosProblems.Erdos599.RegularGlobalAdmissibleProvider
import ErdosProblems.Erdos599.RegularWeakSplitRows

/-!
# Selected weak-coordinate provider boundary

This lightweight module contains only the geometric coordinate contract used
by the regular split recursion.  Keeping the proposition below the selected
adapter prevents the local candidate constructor from importing the final
transfinite assembly.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

universe u

variable {V : Type u}

/-- The exact coordinate boundary left after the causal table has registered
all selected target carriers and clean mavericks. -/
def HasWeakSelectedCoordinateProvider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) : Prop :=
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  ∀ (Sigma : Set (Ladder.Stage kappa)),
    Stationary.IsClubBelow kappa Sigma →
    Disjoint Sigma L.phi →
    ∀ request : Ladder.Stage kappa →
      Option ↑(G.source ∩ R.carrier),
    ∀ (i : Ladder.Stage kappa)
        (previous : ∀ j : Ladder.Stage kappa, j < i →
          RegularCompletedPendingSplice.RecursivePayload
            G L Sigma R.carrier ↑(G.source ∩ R.carrier))
        (_hprevious : ∀ j (hji : j < i),
          RegularCompletedPendingSplice.IsValidRecursiveStage request j
            (fun l hlj ↦ previous l (lt_trans hlj hji))
            (previous j hji))
        (B : RegularSplitCanonicalHistoryBase.HistoryBase
          G L Sigma R.carrier ↑(G.source ∩ R.carrier)
            request i previous)
        (gamma : Ladder.Stage kappa),
      RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma R.carrier ↑(G.source ∩ R.carrier)
            request i previous B.base ⊆
        RegularRows.CausalRegular.finalRequest G Q
          hregular.aleph0_le B.baseStage gamma →
      ∃ beta : Ladder.Stage kappa,
        beta ∈ Sigma ∧ B.baseStage < beta ∧
          ∃ P : RegularWeakSplitCandidate.WeakSplitFamilies G,
            RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate G L
              (RegularRows.CausalRegular.finalRequest G Q
                hregular.aleph0_le) B.baseStage beta gamma P

end RegularExtension
end CardinalInduction
end Erdos599
