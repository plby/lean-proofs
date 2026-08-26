import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 212 through 212. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk212

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_212 :
    geometryCheck (table.cell ⟨212, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_212 :
    crossingCheck (table.cell ⟨212, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_212 :
    scalarCheck (table.cell ⟨212, by decide⟩) = true := by
  kernel_decide

theorem certificate_212 :
    Certificate (table.cell ⟨212, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_212,
    crossing_of_check crossingCheck_212,
    scalar_of_check scalarCheck_212⟩

end Erdos1038.HighKPlatformConstantTableChunk212
