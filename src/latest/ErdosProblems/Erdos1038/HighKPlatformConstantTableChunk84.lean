import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 84 through 84. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk84

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_084 :
    geometryCheck (table.cell ⟨84, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_084 :
    crossingCheck (table.cell ⟨84, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_084 :
    scalarCheck (table.cell ⟨84, by decide⟩) = true := by
  kernel_decide

theorem certificate_084 :
    Certificate (table.cell ⟨84, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_084,
    crossing_of_check crossingCheck_084,
    scalar_of_check scalarCheck_084⟩

end Erdos1038.HighKPlatformConstantTableChunk84
