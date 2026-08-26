import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 796 through 796. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk796

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_796 :
    geometryCheck (table.cell ⟨796, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_796 :
    crossingCheck (table.cell ⟨796, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_796 :
    scalarCheck (table.cell ⟨796, by decide⟩) = true := by
  kernel_decide

theorem certificate_796 :
    Certificate (table.cell ⟨796, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_796,
    crossing_of_check crossingCheck_796,
    scalar_of_check scalarCheck_796⟩

end Erdos1038.HighKPlatformConstantTableChunk796
