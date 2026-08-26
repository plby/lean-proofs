import ErdosProblems.Erdos941.SpherePairFrames

/-! # Uniqueness of orientation-preserving sphere-pair transporters -/

namespace Erdos941

open PairLocal

theorem dotThree_cross_frame {R : Type*} [CommRing R] (t u v : R × R × R) :
    dotThree (crossThree t u) v = (tripleFrame t u v).det := by
  simp [tripleFrame, Matrix.det_fin_three, crossThree, dotThree]
  ring

theorem eq_of_dotThree_eq {R : Type*} [CommRing R]
    {t u : R × R × R} (h : ∀ v, dotThree t v = dotThree u v) : t = u := by
  have ha := h (1, 0, 0)
  have hb := h (0, 1, 0)
  have hc := h (0, 0, 1)
  simp only [dotThree, mul_one, mul_zero, add_zero, zero_add] at ha hb hc
  exact Prod.ext ha (Prod.ext hb hc)

theorem crossThree_sphereSpecialGroup {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] (g : sphereSpecialGroup R) (t u : R × R × R) :
    g.1 (crossThree t u) = crossThree (g.1 t) (g.1 u) := by
  apply eq_of_dotThree_eq
  intro w
  obtain ⟨v, rfl⟩ := g.1.surjective w
  rw [dotThree_sphereSpecialGroup, dotThree_cross_frame, dotThree_cross_frame]
  have hdet := det_tripleFrame_map g.1.toLinearMap t u v
  change (tripleFrame (g.1 t) (g.1 u) (g.1 v)).det =
    LinearMap.det g.1.toLinearMap * (tripleFrame t u v).det at hdet
  rw [g.2.2, one_mul] at hdet
  exact hdet.symm

theorem sphereSpecialGroup_eq_one_of_fix_pair {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {n e : R} (p : SpherePair R n e)
    (hnd : e ^ 2 ≠ n ^ 2) (g : sphereSpecialGroup R)
    (ht : g.1 p.1.1 = p.1.1) (hu : g.1 p.1.2 = p.1.2) : g = 1 := by
  have hnormal : g.1 (crossThree p.1.1 p.1.2) = crossThree p.1.1 p.1.2 := by
    rw [crossThree_sphereSpecialGroup, ht, hu]
  let P := sphereFrame p.1.1 p.1.2
  have hframe (v : R × R × R) : g.1 (coeffMatrixMap P v) = coeffMatrixMap P v := by
    rw [coeffMatrixMap_sphereFrame, map_add, map_add, map_smul, map_smul, map_smul,
      ht, hu, hnormal]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro t
  have hscale : coeffMatrixMap P (coeffMatrixMap P.adjugate t) = P.det • t := by
    rw [← LinearMap.comp_apply, ← coeffMatrixMap_mul, Matrix.mul_adjugate,
      coeffMatrixMap_smul_one]
  have hfix := hframe (coeffMatrixMap P.adjugate t)
  rw [hscale, map_smul] at hfix
  have hP : P.det ≠ 0 := by
    rw [spherePair_frame_det]
    exact sub_ne_zero.mpr hnd.symm
  exact Prod.ext (mul_left_cancel₀ hP (congrArg Prod.fst hfix))
    (Prod.ext (mul_left_cancel₀ hP (congrArg (fun v => v.2.1) hfix))
      (mul_left_cancel₀ hP (congrArg (fun v => v.2.2) hfix)))

theorem spherePairAction_left_injective {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {n e : R} (p : SpherePair R n e)
    (hnd : e ^ 2 ≠ n ^ 2) : Function.Injective (fun g : sphereSpecialGroup R => g • p) := by
  intro g h hgh
  dsimp only at hgh
  have hfix : (h⁻¹ * g) • p = p := by rw [mul_smul, hgh, inv_smul_smul]
  have heq := sphereSpecialGroup_eq_one_of_fix_pair p hnd (h⁻¹ * g)
    (congrArg (fun q : SpherePair R n e => q.1.1) hfix)
    (congrArg (fun q : SpherePair R n e => q.1.2) hfix)
  exact (inv_mul_eq_one.mp heq).symm

theorem sphereSpecialGroup_ext_of_pair {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {n e : R} (p : SpherePair R n e)
    (hnd : e ^ 2 ≠ n ^ 2) (g h : sphereSpecialGroup R)
    (ht : g.1 p.1.1 = h.1 p.1.1) (hu : g.1 p.1.2 = h.1 p.1.2) : g = h := by
  apply spherePairAction_left_injective p hnd
  apply Subtype.ext
  exact Prod.ext ht hu

end Erdos941
