import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 11 through 11. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk11

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_011 :
    geometryCheck (table.cell ⟨11, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_011 :
    crossingCheck (table.cell ⟨11, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_011 :
    scalarCheck (table.cell ⟨11, by decide⟩) = true := by
  kernel_decide

theorem certificate_011 :
    Certificate (table.cell ⟨11, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_011,
    crossing_of_check crossingCheck_011,
    scalar_of_check scalarCheck_011⟩

end Erdos1038.HighKPlatformConstantTableChunk11
