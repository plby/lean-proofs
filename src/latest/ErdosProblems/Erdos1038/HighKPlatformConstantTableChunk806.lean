import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 806 through 806. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk806

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_806 :
    geometryCheck (table.cell ⟨806, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_806 :
    crossingCheck (table.cell ⟨806, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_806 :
    scalarCheck (table.cell ⟨806, by decide⟩) = true := by
  kernel_decide

theorem certificate_806 :
    Certificate (table.cell ⟨806, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_806,
    crossing_of_check crossingCheck_806,
    scalar_of_check scalarCheck_806⟩

end Erdos1038.HighKPlatformConstantTableChunk806
