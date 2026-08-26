import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 299 through 299. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk299

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_299 :
    geometryCheck (table.cell ⟨299, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_299 :
    crossingCheck (table.cell ⟨299, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_299 :
    scalarCheck (table.cell ⟨299, by decide⟩) = true := by
  kernel_decide

theorem certificate_299 :
    Certificate (table.cell ⟨299, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_299,
    crossing_of_check crossingCheck_299,
    scalar_of_check scalarCheck_299⟩

end Erdos1038.HighKPlatformConstantTableChunk299
