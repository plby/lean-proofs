import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 326 through 326. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk326

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_326 :
    geometryCheck (table.cell ⟨326, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_326 :
    crossingCheck (table.cell ⟨326, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_326 :
    scalarCheck (table.cell ⟨326, by decide⟩) = true := by
  kernel_decide

theorem certificate_326 :
    Certificate (table.cell ⟨326, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_326,
    crossing_of_check crossingCheck_326,
    scalar_of_check scalarCheck_326⟩

end Erdos1038.HighKPlatformConstantTableChunk326
