import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 703 through 703. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk703

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_703 :
    geometryCheck (table.cell ⟨703, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_703 :
    crossingCheck (table.cell ⟨703, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_703 :
    scalarCheck (table.cell ⟨703, by decide⟩) = true := by
  kernel_decide

theorem certificate_703 :
    Certificate (table.cell ⟨703, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_703,
    crossing_of_check crossingCheck_703,
    scalar_of_check scalarCheck_703⟩

end Erdos1038.HighKPlatformConstantTableChunk703
