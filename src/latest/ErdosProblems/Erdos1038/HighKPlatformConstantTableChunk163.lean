import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 163 through 163. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk163

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_163 :
    geometryCheck (table.cell ⟨163, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_163 :
    crossingCheck (table.cell ⟨163, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_163 :
    scalarCheck (table.cell ⟨163, by decide⟩) = true := by
  kernel_decide

theorem certificate_163 :
    Certificate (table.cell ⟨163, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_163,
    crossing_of_check crossingCheck_163,
    scalar_of_check scalarCheck_163⟩

end Erdos1038.HighKPlatformConstantTableChunk163
