import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 733 through 733. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk733

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_733 :
    geometryCheck (table.cell ⟨733, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_733 :
    crossingCheck (table.cell ⟨733, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_733 :
    scalarCheck (table.cell ⟨733, by decide⟩) = true := by
  kernel_decide

theorem certificate_733 :
    Certificate (table.cell ⟨733, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_733,
    crossing_of_check crossingCheck_733,
    scalar_of_check scalarCheck_733⟩

end Erdos1038.HighKPlatformConstantTableChunk733
