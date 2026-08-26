import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 386 through 386. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk386

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_386 :
    geometryCheck (table.cell ⟨386, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_386 :
    crossingCheck (table.cell ⟨386, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_386 :
    scalarCheck (table.cell ⟨386, by decide⟩) = true := by
  kernel_decide

theorem certificate_386 :
    Certificate (table.cell ⟨386, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_386,
    crossing_of_check crossingCheck_386,
    scalar_of_check scalarCheck_386⟩

end Erdos1038.HighKPlatformConstantTableChunk386
