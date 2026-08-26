import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 798 through 798. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk798

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_798 :
    geometryCheck (table.cell ⟨798, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_798 :
    crossingCheck (table.cell ⟨798, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_798 :
    scalarCheck (table.cell ⟨798, by decide⟩) = true := by
  kernel_decide

theorem certificate_798 :
    Certificate (table.cell ⟨798, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_798,
    crossing_of_check crossingCheck_798,
    scalar_of_check scalarCheck_798⟩

end Erdos1038.HighKPlatformConstantTableChunk798
