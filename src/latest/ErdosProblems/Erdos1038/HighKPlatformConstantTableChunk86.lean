import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 86 through 86. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk86

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_086 :
    geometryCheck (table.cell ⟨86, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_086 :
    crossingCheck (table.cell ⟨86, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_086 :
    scalarCheck (table.cell ⟨86, by decide⟩) = true := by
  kernel_decide

theorem certificate_086 :
    Certificate (table.cell ⟨86, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_086,
    crossing_of_check crossingCheck_086,
    scalar_of_check scalarCheck_086⟩

end Erdos1038.HighKPlatformConstantTableChunk86
