import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 327 through 327. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk327

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_327 :
    geometryCheck (table.cell ⟨327, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_327 :
    crossingCheck (table.cell ⟨327, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_327 :
    scalarCheck (table.cell ⟨327, by decide⟩) = true := by
  kernel_decide

theorem certificate_327 :
    Certificate (table.cell ⟨327, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_327,
    crossing_of_check crossingCheck_327,
    scalar_of_check scalarCheck_327⟩

end Erdos1038.HighKPlatformConstantTableChunk327
