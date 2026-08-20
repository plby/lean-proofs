import ErdosProblems.Erdos733.ST.ComplementComponent

open Classical
noncomputable section

-- [TABLET NODE: ComponentSegmentInOpenBall]
lemma ComponentSegmentInOpenBall
    (U C : Set (EuclideanSpace ℝ (Fin 2)))
    (y z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    ComplementComponent Uᶜ C →
      y ∈ C →
        z ∈ Metric.ball y r →
          Metric.ball y r ⊆ U →
            segment ℝ y z ⊆ C := by
-- BODY
  intro hcomp hy hz hball
  rcases hcomp with ⟨_hCne, hCU, hCconn, hmax⟩
  have hrpos : 0 < r := lt_of_le_of_lt dist_nonneg hz
  have hseg_ball : segment ℝ y z ⊆ Metric.ball y r :=
    (convex_ball y r).segment_subset (Metric.mem_ball_self hrpos) hz
  let T : Set (EuclideanSpace ℝ (Fin 2)) := C ∪ segment ℝ y z
  have hTnonempty : T.Nonempty := ⟨y, Or.inl hy⟩
  have hTsubU : T ⊆ U := by
    intro x hx
    rcases hx with hxC | hxseg
    · exact by simpa using hCU hxC
    · exact hball (hseg_ball hxseg)
  have hTsub : T ⊆ (Uᶜ)ᶜ := by
    intro x hx
    simpa using hTsubU hx
  have hseg_conn : IsConnected (segment ℝ y z) :=
    (convex_segment y z).isConnected ⟨y, left_mem_segment ℝ y z⟩
  have hinter : (C ∩ segment ℝ y z).Nonempty :=
    ⟨y, hy, left_mem_segment ℝ y z⟩
  have hTconn : IsConnected T := by
    simpa [T] using hCconn.union hinter hseg_conn
  have hCsubsetT : C ⊆ T := by
    intro x hx
    exact Or.inl hx
  have hTsubsetC : T ⊆ C := hmax T hTnonempty hTsub hTconn hCsubsetT
  intro x hx
  exact hTsubsetC (Or.inr hx)
