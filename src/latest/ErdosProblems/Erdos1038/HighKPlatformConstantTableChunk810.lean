import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 810 through 810. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk810

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_810 :
    geometryCheck (table.cell ⟨810, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_810 :
    crossingCheck (table.cell ⟨810, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_810 :
    scalarCheck (table.cell ⟨810, by decide⟩) = true := by
  kernel_decide

theorem certificate_810 :
    Certificate (table.cell ⟨810, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_810,
    crossing_of_check crossingCheck_810,
    scalar_of_check scalarCheck_810⟩

end Erdos1038.HighKPlatformConstantTableChunk810
