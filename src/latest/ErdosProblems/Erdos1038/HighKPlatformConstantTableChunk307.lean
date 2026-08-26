import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 307 through 307. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk307

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_307 :
    geometryCheck (table.cell ⟨307, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_307 :
    crossingCheck (table.cell ⟨307, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_307 :
    scalarCheck (table.cell ⟨307, by decide⟩) = true := by
  kernel_decide

theorem certificate_307 :
    Certificate (table.cell ⟨307, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_307,
    crossing_of_check crossingCheck_307,
    scalar_of_check scalarCheck_307⟩

end Erdos1038.HighKPlatformConstantTableChunk307
