import Util.IncidenceGeometry.UnitCircle
import Util.IncidenceGeometry.UnitCircleCyclicAngleArcRealization
import Util.IncidenceGeometry.UnitCircleCyclicAngleOrder

open Classical
noncomputable section

lemma UnitCircleCyclicSuccessorArcs
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : (↑S : Set (EuclideanSpace ℝ (Fin 2))) ⊆ UnitCircle p)
    (hcard : 3 ≤ S.card) :
    ∃ (succ :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          {x : EuclideanSpace ℝ (Fin 2) // x ∈ S})
      (carrier arcInterior :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          Set (EuclideanSpace ℝ (Fin 2)))
      (γ :
        (x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) →
          Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
      Function.Bijective succ ∧
        (∀ x, x.1 ≠ (succ x).1) ∧
          (∀ x,
            Continuous (γ x) ∧
              Function.Injective (γ x) ∧
                (∀ t, γ x t ∈ UnitCircle p) ∧
                  γ x ⟨0, by simp⟩ = x.1 ∧
                    γ x ⟨1, by simp⟩ = (succ x).1 ∧
                      carrier x = Set.range (γ x) ∧
                        arcInterior x =
                          Set.range
                            (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                              γ x ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) ∧
            (∀ x y : {y : EuclideanSpace ℝ (Fin 2) // y ∈ S},
              y.1 ∉ arcInterior x) ∧
              (∀ x y,
                x ≠ y → arcInterior x ∩ arcInterior y = ∅) ∧
                (∀ x y,
                  (Sym2.mk x.1 (succ x).1 :
                      Sym2 (EuclideanSpace ℝ (Fin 2))) =
                    Sym2.mk y.1 (succ y).1 →
                    x = y) := by
  rcases UnitCircleCyclicAngleOrder p S hS hcard with ⟨D⟩
  rcases UnitCircleCyclicAngleArcRealization p S D with
    ⟨carrier, arcInterior, γ, hArc, hNoS, hDisjoint⟩
  exact ⟨D.succ, carrier, arcInterior, γ, D.succ_bijective, D.succ_ne, hArc,
    hNoS, hDisjoint, D.endpoint_unique⟩
