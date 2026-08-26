import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 401 through 401. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk401

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_401 :
    geometryCheck (table.cell ⟨401, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_401 :
    crossingCheck (table.cell ⟨401, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_401 :
    scalarCheck (table.cell ⟨401, by decide⟩) = true := by
  kernel_decide

theorem certificate_401 :
    Certificate (table.cell ⟨401, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_401,
    crossing_of_check crossingCheck_401,
    scalar_of_check scalarCheck_401⟩

end Erdos1038.HighKPlatformConstantTableChunk401
