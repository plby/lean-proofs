import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 641 through 641. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk641

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_641 :
    geometryCheck (table.cell ⟨641, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_641 :
    crossingCheck (table.cell ⟨641, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_641 :
    scalarCheck (table.cell ⟨641, by decide⟩) = true := by
  kernel_decide

theorem certificate_641 :
    Certificate (table.cell ⟨641, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_641,
    crossing_of_check crossingCheck_641,
    scalar_of_check scalarCheck_641⟩

end Erdos1038.HighKPlatformConstantTableChunk641
