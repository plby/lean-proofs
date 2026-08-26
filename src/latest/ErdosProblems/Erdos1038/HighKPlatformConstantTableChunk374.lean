import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 374 through 374. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk374

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_374 :
    geometryCheck (table.cell ⟨374, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_374 :
    crossingCheck (table.cell ⟨374, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_374 :
    scalarCheck (table.cell ⟨374, by decide⟩) = true := by
  kernel_decide

theorem certificate_374 :
    Certificate (table.cell ⟨374, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_374,
    crossing_of_check crossingCheck_374,
    scalar_of_check scalarCheck_374⟩

end Erdos1038.HighKPlatformConstantTableChunk374
