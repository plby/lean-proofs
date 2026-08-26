import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 475 through 475. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk475

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_475 :
    geometryCheck (table.cell ⟨475, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_475 :
    crossingCheck (table.cell ⟨475, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_475 :
    scalarCheck (table.cell ⟨475, by decide⟩) = true := by
  kernel_decide

theorem certificate_475 :
    Certificate (table.cell ⟨475, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_475,
    crossing_of_check crossingCheck_475,
    scalar_of_check scalarCheck_475⟩

end Erdos1038.HighKPlatformConstantTableChunk475
