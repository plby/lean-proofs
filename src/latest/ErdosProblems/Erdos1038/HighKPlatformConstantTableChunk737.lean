import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 737 through 737. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk737

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_737 :
    geometryCheck (table.cell ⟨737, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_737 :
    crossingCheck (table.cell ⟨737, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_737 :
    scalarCheck (table.cell ⟨737, by decide⟩) = true := by
  kernel_decide

theorem certificate_737 :
    Certificate (table.cell ⟨737, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_737,
    crossing_of_check crossingCheck_737,
    scalar_of_check scalarCheck_737⟩

end Erdos1038.HighKPlatformConstantTableChunk737
