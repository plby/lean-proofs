import Wikipedia.NoExoticSixSphere.WhitneyCuspDoublePointClosure

/-!
# Actual curve coordinates on the closed cusp double-point locus

The axis coordinate gives a homeomorphism from the real line to the closure
of the ordered double-point locus. Swapping the two source points negates
that coordinate. Selecting the nonnegative coordinate gives a genuine
half-line chart with the singular origin as its endpoint.
-/

noncomputable section

open Set

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization FamilyEmbedding

theorem doublePointCurve_mem_closure (z : ℝ) :
    doublePointCurve z ∈ closure (doublePoints map) := by
  by_cases hz : z = 0
  · rw [hz, doublePointCurve_zero]
    exact origin_mem_closure_doublePoints
  · exact subset_closure (doublePointCurve_mem z hz)

theorem doublePointCurve_reconstruct (q : closure (doublePoints map)) :
    doublePointCurve (q.val.2.1 2) = q.val := by
  have h := (Set.ext_iff.mp closure_doublePoints_eq q.val).mp q.property
  rcases h with ⟨hne, he⟩ | he
  · rcases (map_eq_iff q.val.1 q.val.2.1 q.val.2.2).mp he with h | ⟨z, _, ht, hx, hy⟩
    · exact (hne h).elim
    · change (q.val.2.1 2 ^ 2, (axis (q.val.2.1 2), axis (-q.val.2.1 2))) = q.val
      apply Prod.ext
      · rw [hx]
        exact ht
      · rw [hx]
        exact Prod.ext hx.symm hy.symm
  · have he' : q.val = (0, (0, 0)) := he
    rw [he']
    exact doublePointCurve_zero

def closedDoublePointHomeomorph : ℝ ≃ₜ closure (doublePoints map) where
  toFun z := ⟨doublePointCurve z, doublePointCurve_mem_closure z⟩
  invFun q := q.val.2.1 2
  left_inv _ := rfl
  right_inv q := Subtype.ext (doublePointCurve_reconstruct q)
  continuous_toFun := continuous_doublePointCurve.subtype_mk doublePointCurve_mem_closure
  continuous_invFun :=
    (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2 : Vector 3 →L[ℝ] ℝ).continuous.comp
      (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))

theorem doublePointCurve_neg (z : ℝ) :
    doublePointCurve (-z) = ((doublePointCurve z).1,
      ((doublePointCurve z).2.2, (doublePointCurve z).2.1)) := by
  simp [doublePointCurve]

def nonnegativeDoublePointHomeomorph :
    {z : ℝ // 0 ≤ z} ≃ₜ {q : closure (doublePoints map) // 0 ≤ q.val.2.1 2} where
  toFun z := ⟨closedDoublePointHomeomorph z.val, z.property⟩
  invFun q := ⟨closedDoublePointHomeomorph.symm q.val, q.property⟩
  left_inv z := Subtype.ext (closedDoublePointHomeomorph.symm_apply_apply z.val)
  right_inv q := Subtype.ext (closedDoublePointHomeomorph.apply_symm_apply q.val)
  continuous_toFun := (closedDoublePointHomeomorph.continuous.comp
    continuous_subtype_val).subtype_mk (fun z ↦ z.property)
  continuous_invFun := (closedDoublePointHomeomorph.symm.continuous.comp
    continuous_subtype_val).subtype_mk (fun q ↦ q.property)

end NoExoticSixSphere.WhitneyCusp
