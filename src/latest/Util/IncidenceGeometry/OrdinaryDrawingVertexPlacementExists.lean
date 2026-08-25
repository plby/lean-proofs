import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma OrdinaryDrawingVertexPlacementExists (V : Type*) [Fintype V] :
    ∃ placement : V → EuclideanSpace ℝ (Fin 2), Function.Injective placement := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let placement : V → EuclideanSpace ℝ (Fin 2) :=
    fun v => (WithLp.equiv 2 (Fin 2 → ℝ)).symm
      (fun i => if i = 0 then ((e v : ℕ) : ℝ) else 0)
  refine ⟨placement, ?_⟩
  intro v w hvw
  apply e.injective
  apply Fin.ext
  have h0 := congrArg
    (fun p : EuclideanSpace ℝ (Fin 2) => (WithLp.equiv 2 (Fin 2 → ℝ) p) 0) hvw
  simp [placement] at h0
  exact_mod_cast h0
