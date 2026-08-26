import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 191 through 191. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk191

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_191 :
    geometryCheck (table.cell ⟨191, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_191 :
    crossingCheck (table.cell ⟨191, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_191 :
    scalarCheck (table.cell ⟨191, by decide⟩) = true := by
  kernel_decide

theorem certificate_191 :
    Certificate (table.cell ⟨191, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_191,
    crossing_of_check crossingCheck_191,
    scalar_of_check scalarCheck_191⟩

end Erdos1038.HighKPlatformConstantTableChunk191
