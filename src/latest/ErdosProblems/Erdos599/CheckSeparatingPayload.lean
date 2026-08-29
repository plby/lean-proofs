import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.SingularExtension

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath

universe u

variable {V : Type u}

theorem stageWeb_isNormalized
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hNorm : Gamma.IsNormalized) (L : Gamma.KappaLadder kappa)
    (delta : Ladder.Stage kappa) :
    (L.stageWeb delta).IsNormalized := by
  intro x y hxy
  let Q := Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt delta))
  have hxyQ : Q.graph.Adj x y := Q.essentialPart_adj_imp hxy
  have hxyGamma : Gamma.graph.Adj x y := Gamma.quotient_adj_imp hxyQ
  refine ⟨?_, (hNorm hxyGamma).2⟩
  have hNoEnterQ : Q.NoEdgeEnters Q.source :=
    DWeb.NoEdgeEnters.quotient (G := Gamma)
      (fun {_ _} e hy ↦ (hNorm e).1 hy)
  exact fun hy ↦ hNoEnterQ hxyQ hy.1

/-- The weak payload has the exact bounded-height witness expected by the
separating-stopover enlargement. -/
theorem HalfwayPayload.heightAtMost
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    {U : Set V} (D : HalfwayPayload L delta U) :
    HeightAtMost (L.stageWeb delta) D.C kappa := by
  refine ⟨D.X, ⟨D.heightAwayFromSource, D.R, D.heightWave,
    D.stopoverRoof⟩, D.heightSmall.le⟩

theorem HalfwayPayload.exists_separatingStopover
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    {U : Set V} (D : HalfwayPayload L delta U)
    (hNorm : Gamma.IsNormalized) :
    ∃ C : Set V,
      IsSeparatingHalfwayStopover (L.stageWeb delta) D.W C ∧
        HeightAtMost (L.stageWeb delta) C kappa := by
  have hstop : IsHalfwayStopover (L.stageWeb delta) D.W D.C :=
    ⟨D.linkage, D.trimmed, D.quotientUnhindered⟩
  exact SingularExtension.exists_separatingStopover_of_stopover
    (stageWeb_isNormalized hNorm L delta) hstop D.heightAtMost

end SliceCandidate
end CardinalInduction
end Erdos599
