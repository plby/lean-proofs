import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 323 through 323. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk323

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_323 :
    geometryCheck (table.cell ⟨323, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_323 :
    crossingCheck (table.cell ⟨323, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_323 :
    scalarCheck (table.cell ⟨323, by decide⟩) = true := by
  kernel_decide

theorem certificate_323 :
    Certificate (table.cell ⟨323, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_323,
    crossing_of_check crossingCheck_323,
    scalar_of_check scalarCheck_323⟩

end Erdos1038.HighKPlatformConstantTableChunk323
