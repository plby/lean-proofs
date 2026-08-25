import Util.IncidenceGeometry.PolygonalArcReverse
import Util.IncidenceGeometry.PolygonalPathInGeneralPosition

open Classical
noncomputable section

lemma ArcCrossingOrientedCrossingData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc)
    (Γ : FinitePolygonalSet) (α : PolygonalPath) :
    Γ.carrier = γ.carrier →
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ Γ.points) →
        γ.source ∉ α.carrier →
          γ.target ∉ α.carrier →
            PolygonalPathInGeneralPosition α Γ →
              ((γ.carrier ∩ K =
                  ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    γ.target ∉ K) ∨
                (γ.carrier ∩ K =
                  ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    γ.source ∉ K)) →
                ∃ δ : PolygonalArc,
                  δ.carrier = γ.carrier ∧
                    δ.relativeInterior = γ.relativeInterior ∧
                      (∀ v : EuclideanSpace ℝ (Fin 2),
                        v ∈ δ.vertices → v ∈ Γ.points) ∧
                        (∀ v : EuclideanSpace ℝ (Fin 2),
                          v ∈ δ.vertices → v ∉ α.carrier) ∧
                          Set.Finite (α.carrier ∩ δ.carrier) ∧
                            δ.source ∉ α.carrier ∧
                              δ.target ∉ α.carrier ∧
                                δ.carrier ∩ K =
                                  ({δ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                  δ.target ∉ K := by
  intro hΓcarrier hγvertices hγsourceα hγtargetα hgp hattach
  have hfiniteΓ : Set.Finite (α.carrier ∩ Γ.carrier) := hgp.2.2.2.2
  have hpointsAvoid :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ Γ.points → v ∉ α.carrier := hgp.2.1
  have hγverticesAvoid :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∉ α.carrier := by
    intro v hv
    exact hpointsAvoid v (hγvertices v hv)
  rcases hattach with hsource | htarget
  · refine ⟨γ, rfl, rfl, hγvertices, hγverticesAvoid, ?_, hγsourceα,
      hγtargetα, hsource.1, hsource.2⟩
    simpa [hΓcarrier] using hfiniteΓ
  · refine ⟨PolygonalArcReverse γ, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      exact hγvertices v (by simpa [PolygonalArcReverse] using hv)
    · intro v hv
      exact hγverticesAvoid v (by simpa [PolygonalArcReverse] using hv)
    · simpa [PolygonalArcReverse, hΓcarrier] using hfiniteΓ
    · simpa [PolygonalArcReverse] using hγtargetα
    · simpa [PolygonalArcReverse] using hγsourceα
    · simpa [PolygonalArcReverse] using htarget.1
    · simpa [PolygonalArcReverse] using htarget.2
