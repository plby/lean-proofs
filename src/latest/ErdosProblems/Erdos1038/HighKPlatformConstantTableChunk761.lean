import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 761 through 761. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk761

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_761 :
    geometryCheck (table.cell ⟨761, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_761 :
    crossingCheck (table.cell ⟨761, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_761 :
    scalarCheck (table.cell ⟨761, by decide⟩) = true := by
  kernel_decide

theorem certificate_761 :
    Certificate (table.cell ⟨761, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_761,
    crossing_of_check crossingCheck_761,
    scalar_of_check scalarCheck_761⟩

end Erdos1038.HighKPlatformConstantTableChunk761
