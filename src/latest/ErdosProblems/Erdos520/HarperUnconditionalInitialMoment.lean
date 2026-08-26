import ErdosProblems.Erdos520.HarperCentralEconomicalAssembly
import ErdosProblems.Erdos520.HarperUnconditionalFinalAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Unconditional Harper initial moment

The shrinking central bands and the growing noncentral unit shells now each
supply one absolute economical local-moment bound.  Merging those two
witnesses and applying the completed Parseval assembly proves the exact
Harper input consumed by the downstream #520 argument, with no premise.
-/

/-- Premise-free form of the Rademacher initial-moment statement used by the
Caich/Lau--Tenenbaum--Wu part of the proof. -/
theorem harperRademacherInitialMomentStatement_unconditional :
    HarperRademacherInitialMomentStatement := by
  obtain ⟨Ccentral, hCcentral, Jcentral, hcentral⟩ :=
    exists_harperEconomicalCentralUnitMomentBound
  obtain ⟨Cnoncentral, hCnoncentral, Jnoncentral, hnoncentral⟩ :=
    exists_harperEconomicalNoncentralLocalMomentBound
  have hlocal : HarperEconomicalLocalMomentBound
      (Ccentral + Cnoncentral) (max Jcentral Jnoncentral) :=
    harperEconomicalLocalMomentBound_of_central_noncentral
      hCcentral hCnoncentral hcentral hnoncentral
  exact harperRademacherInitialMomentStatement_of_economicalLocalMoments
    (add_nonneg hCcentral hCnoncentral) hlocal

end Problem520
end Erdos

#print axioms Erdos.Problem520.harperRademacherInitialMomentStatement_unconditional
