import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 709 through 709. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk709

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_709 :
    geometryCheck (table.cell ⟨709, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_709 :
    crossingCheck (table.cell ⟨709, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_709 :
    scalarCheck (table.cell ⟨709, by decide⟩) = true := by
  kernel_decide

theorem certificate_709 :
    Certificate (table.cell ⟨709, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_709,
    crossing_of_check crossingCheck_709,
    scalar_of_check scalarCheck_709⟩

end Erdos1038.HighKPlatformConstantTableChunk709
