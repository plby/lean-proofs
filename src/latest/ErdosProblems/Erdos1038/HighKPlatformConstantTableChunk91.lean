import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 91 through 91. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk91

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_091 :
    geometryCheck (table.cell ⟨91, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_091 :
    crossingCheck (table.cell ⟨91, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_091 :
    scalarCheck (table.cell ⟨91, by decide⟩) = true := by
  kernel_decide

theorem certificate_091 :
    Certificate (table.cell ⟨91, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_091,
    crossing_of_check crossingCheck_091,
    scalar_of_check scalarCheck_091⟩

end Erdos1038.HighKPlatformConstantTableChunk91
