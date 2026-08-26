import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 817 through 817. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk817

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_817 :
    geometryCheck (table.cell ⟨817, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_817 :
    crossingCheck (table.cell ⟨817, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_817 :
    scalarCheck (table.cell ⟨817, by decide⟩) = true := by
  kernel_decide

theorem certificate_817 :
    Certificate (table.cell ⟨817, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_817,
    crossing_of_check crossingCheck_817,
    scalar_of_check scalarCheck_817⟩

end Erdos1038.HighKPlatformConstantTableChunk817
