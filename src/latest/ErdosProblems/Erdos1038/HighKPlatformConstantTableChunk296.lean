import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 296 through 296. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk296

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_296 :
    geometryCheck (table.cell ⟨296, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_296 :
    crossingCheck (table.cell ⟨296, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_296 :
    scalarCheck (table.cell ⟨296, by decide⟩) = true := by
  kernel_decide

theorem certificate_296 :
    Certificate (table.cell ⟨296, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_296,
    crossing_of_check crossingCheck_296,
    scalar_of_check scalarCheck_296⟩

end Erdos1038.HighKPlatformConstantTableChunk296
