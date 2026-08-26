import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 337 through 337. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk337

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_337 :
    geometryCheck (table.cell ⟨337, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_337 :
    crossingCheck (table.cell ⟨337, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_337 :
    scalarCheck (table.cell ⟨337, by decide⟩) = true := by
  kernel_decide

theorem certificate_337 :
    Certificate (table.cell ⟨337, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_337,
    crossing_of_check crossingCheck_337,
    scalar_of_check scalarCheck_337⟩

end Erdos1038.HighKPlatformConstantTableChunk337
