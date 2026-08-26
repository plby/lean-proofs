import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 310 through 310. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk310

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_310 :
    geometryCheck (table.cell ⟨310, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_310 :
    crossingCheck (table.cell ⟨310, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_310 :
    scalarCheck (table.cell ⟨310, by decide⟩) = true := by
  kernel_decide

theorem certificate_310 :
    Certificate (table.cell ⟨310, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_310,
    crossing_of_check crossingCheck_310,
    scalar_of_check scalarCheck_310⟩

end Erdos1038.HighKPlatformConstantTableChunk310
