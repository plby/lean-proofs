import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 630 through 630. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk630

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_630 :
    geometryCheck (table.cell ⟨630, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_630 :
    crossingCheck (table.cell ⟨630, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_630 :
    scalarCheck (table.cell ⟨630, by decide⟩) = true := by
  kernel_decide

theorem certificate_630 :
    Certificate (table.cell ⟨630, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_630,
    crossing_of_check crossingCheck_630,
    scalar_of_check scalarCheck_630⟩

end Erdos1038.HighKPlatformConstantTableChunk630
