import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalPath

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingAttachmentClearance]
lemma ArcCrossingAttachmentClearance
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (a : EuclideanSpace ℝ (Fin 2)) :
    a ∉ α.carrier →
      Set.Finite (α.carrier ∩ γ.carrier) →
        (α.carrier ∩ γ.carrier).Nonempty →
          γ.carrier ∩ K = ({a} : Set (EuclideanSpace ℝ (Fin 2))) →
            ∃ ε : ℝ,
              0 < ε ∧
                (∀ x, x ∈ α.carrier ∩ γ.carrier → ε ≤ dist x a) ∧
                  IsCompact (γ.carrier ∩ {x | ε ≤ dist x a}) ∧
                    Disjoint (γ.carrier ∩ {x | ε ≤ dist x a}) K := by
-- BODY
  intro ha hXfinite hXnonempty hγK
  let X : Set (EuclideanSpace ℝ (Fin 2)) := α.carrier ∩ γ.carrier
  have hXfinite' : Set.Finite X := hXfinite
  have hXnonempty_fin : hXfinite'.toFinset.Nonempty := by
    exact (Set.Finite.toFinset_nonempty hXfinite').2 hXnonempty
  obtain ⟨x0, hx0fin, hx0_min⟩ :=
    Finset.exists_min_image hXfinite'.toFinset (fun x => dist x a) hXnonempty_fin
  have hx0X : x0 ∈ X := (Set.Finite.mem_toFinset hXfinite').1 hx0fin
  have hx0_ne_a : x0 ≠ a := by
    intro hx0a
    exact ha (by simpa [X, hx0a] using hx0X.1)
  have hdist_pos : 0 < dist x0 a := dist_pos.2 hx0_ne_a
  refine ⟨dist x0 a / 2, by linarith, ?_, ?_, ?_⟩
  · intro x hxX
    have hxfin : x ∈ hXfinite'.toFinset :=
      (Set.Finite.mem_toFinset hXfinite').2 (by simpa [X] using hxX)
    have hmin := hx0_min x hxfin
    linarith
  · have hclosed :
        IsClosed {x : EuclideanSpace ℝ (Fin 2) | dist x0 a / 2 ≤ dist x a} := by
      exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    exact (PolygonalArcCarrierCompact γ).inter_right hclosed
  · rw [Set.disjoint_left]
    intro z hzTail hzK
    have hzγK : z ∈ γ.carrier ∩ K := ⟨hzTail.1, hzK⟩
    have hza_mem : z ∈ ({a} : Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [hγK] using hzγK
    have hza : z = a := by
      simpa using hza_mem
    have hzdist : dist x0 a / 2 ≤ dist z a := hzTail.2
    rw [hza, dist_self] at hzdist
    linarith
