import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 72 through 72. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk72

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_072 :
    geometryCheck (table.cell ⟨72, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_072 :
    crossingCheck (table.cell ⟨72, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_072 :
    scalarCheck (table.cell ⟨72, by decide⟩) = true := by
  kernel_decide

theorem certificate_072 :
    Certificate (table.cell ⟨72, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_072,
    crossing_of_check crossingCheck_072,
    scalar_of_check scalarCheck_072⟩

end Erdos1038.HighKPlatformConstantTableChunk72
