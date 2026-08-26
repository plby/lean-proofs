import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 57 through 57. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk57

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_057 :
    geometryCheck (table.cell ⟨57, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_057 :
    crossingCheck (table.cell ⟨57, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_057 :
    scalarCheck (table.cell ⟨57, by decide⟩) = true := by
  kernel_decide

theorem certificate_057 :
    Certificate (table.cell ⟨57, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_057,
    crossing_of_check crossingCheck_057,
    scalar_of_check scalarCheck_057⟩

end Erdos1038.HighKPlatformConstantTableChunk57
