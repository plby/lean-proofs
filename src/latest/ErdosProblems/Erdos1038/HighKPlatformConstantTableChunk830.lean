import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 830 through 830. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk830

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_830 :
    geometryCheck (table.cell ⟨830, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_830 :
    crossingCheck (table.cell ⟨830, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_830 :
    scalarCheck (table.cell ⟨830, by decide⟩) = true := by
  kernel_decide

theorem certificate_830 :
    Certificate (table.cell ⟨830, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_830,
    crossing_of_check crossingCheck_830,
    scalar_of_check scalarCheck_830⟩

end Erdos1038.HighKPlatformConstantTableChunk830
