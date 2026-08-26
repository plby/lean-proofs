import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 170 through 170. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk170

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_170 :
    geometryCheck (table.cell ⟨170, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_170 :
    crossingCheck (table.cell ⟨170, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_170 :
    scalarCheck (table.cell ⟨170, by decide⟩) = true := by
  kernel_decide

theorem certificate_170 :
    Certificate (table.cell ⟨170, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_170,
    crossing_of_check crossingCheck_170,
    scalar_of_check scalarCheck_170⟩

end Erdos1038.HighKPlatformConstantTableChunk170
