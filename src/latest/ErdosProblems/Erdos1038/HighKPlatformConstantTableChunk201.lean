import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 201 through 201. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk201

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_201 :
    geometryCheck (table.cell ⟨201, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_201 :
    crossingCheck (table.cell ⟨201, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_201 :
    scalarCheck (table.cell ⟨201, by decide⟩) = true := by
  kernel_decide

theorem certificate_201 :
    Certificate (table.cell ⟨201, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_201,
    crossing_of_check crossingCheck_201,
    scalar_of_check scalarCheck_201⟩

end Erdos1038.HighKPlatformConstantTableChunk201
