import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 753 through 753. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk753

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_753 :
    geometryCheck (table.cell ⟨753, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_753 :
    crossingCheck (table.cell ⟨753, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_753 :
    scalarCheck (table.cell ⟨753, by decide⟩) = true := by
  kernel_decide

theorem certificate_753 :
    Certificate (table.cell ⟨753, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_753,
    crossing_of_check crossingCheck_753,
    scalar_of_check scalarCheck_753⟩

end Erdos1038.HighKPlatformConstantTableChunk753
