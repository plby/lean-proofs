import Wikipedia.NoExoticSixSphere.CubicalSuspensionCoordinates
import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionQuotient
import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionCoordinates

/-!
# The native cubical suspension evaluation and its exact fibers

The line coordinate comes first, as in the original cubical suspension
homomorphism. Its evaluation is an actual quotient map, collapsing just
the two endpoint slices and the sphere-pole line. This retains the
coordinate order needed to compare characteristic-disk quotients.
-/

noncomputable section

open Set Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.CubicalSphereSuspension

open CubicalProductSuspension

def evaluation (n : ℕ) : C(unitInterval × Sphere n, Sphere (n + 1)) :=
  ⟨fun p ↦ sphereHomeomorph n
      (OnePointProduct.map (clock p.1, (euclideanOnePointSphere n).symm p.2)),
    (sphereHomeomorph n).continuous.comp (OnePointProduct.continuous_map.comp
      ((clock.continuous.comp continuous_fst).prodMk
        ((euclideanOnePointSphere n).symm.continuous.comp continuous_snd)))⟩

theorem evaluation_reorder (n : ℕ) (p : unitInterval × Sphere n) :
    evaluation n p = JamesSphere.SuspensionCoordinates.reorder n
      (JamesSphere.loopEvaluation n (p.2, p.1)) :=
  (JamesSphere.SuspensionCoordinates.reorder_loopEvaluation n p.2 p.1).symm

theorem evaluation_zero (n : ℕ) (s : Sphere n) :
    evaluation n (0, s) = spherePole (n + 1) := by
  rw [evaluation_reorder, JamesSphere.loopEvaluation_zero,
    JamesSphere.SuspensionCoordinates.reorder_pole]

theorem evaluation_one (n : ℕ) (s : Sphere n) :
    evaluation n (1, s) = spherePole (n + 1) := by
  rw [evaluation_reorder, JamesSphere.loopEvaluation_one,
    JamesSphere.SuspensionCoordinates.reorder_pole]

theorem evaluation_pole (n : ℕ) (t : unitInterval) :
    evaluation n (t, spherePole n) = spherePole (n + 1) := by
  rw [evaluation_reorder, JamesSphere.loopEvaluation_pole,
    JamesSphere.SuspensionCoordinates.reorder_pole]

theorem evaluation_eq_pole_iff (n : ℕ) (p : unitInterval × Sphere n) :
    evaluation n p = spherePole (n + 1) ↔ p.1 = 0 ∨ p.1 = 1 ∨ p.2 = spherePole n := by
  rcases p with ⟨t, s⟩
  constructor
  · intro he
    by_cases ht₀ : t = 0
    · exact Or.inl ht₀
    by_cases ht₁ : t = 1
    · exact Or.inr (Or.inl ht₁)
    by_cases hs : s = spherePole n
    · exact Or.inr (Or.inr hs)
    have h₀ : 0 < (t : ℝ) :=
      lt_of_le_of_ne t.property.1 (fun h ↦ ht₀ (Subtype.ext h.symm))
    have h₁ : (t : ℝ) < 1 :=
      lt_of_le_of_ne t.property.2 (fun h ↦ ht₁ (Subtype.ext h))
    rw [evaluation_reorder, ← JamesSphere.SuspensionCoordinates.reorder_pole n] at he
    exact False.elim (JamesSphere.loopEvaluation_ne_pole n hs t h₀ h₁
      ((JamesSphere.SuspensionCoordinates.reorder n).injective he))
  · rintro (rfl | rfl | rfl)
    · exact evaluation_zero n s
    · exact evaluation_one n s
    · exact evaluation_pole n t

theorem evaluation_eq_iff (n : ℕ) (p q : unitInterval × Sphere n) :
    evaluation n p = evaluation n q ↔ p = q ∨
      (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = spherePole n) ∧
      (q.1 = 0 ∨ q.1 = 1 ∨ q.2 = spherePole n) := by
  constructor
  · intro he
    by_cases hp : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = spherePole n
    · exact Or.inr ⟨hp, (evaluation_eq_pole_iff n q).mp
        (he.symm.trans ((evaluation_eq_pole_iff n p).mpr hp))⟩
    · have ht₀ : p.1 ≠ 0 := fun h ↦ hp (Or.inl h)
      have ht₁ : p.1 ≠ 1 := fun h ↦ hp (Or.inr (Or.inl h))
      have hm := (sphereHomeomorph n).injective he
      have hnot : OnePointProduct.map
          (clock p.1, (euclideanOnePointSphere n).symm p.2) ≠ ∞ := by
        intro hi
        have hz : evaluation n p = spherePole (n + 1) := by
          change sphereHomeomorph n (OnePointProduct.map
            (clock p.1, (euclideanOnePointSphere n).symm p.2)) = _
          rw [hi, sphereHomeomorph_infty]
        exact hp ((evaluation_eq_pole_iff n p).mp hz)
      obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hnot
      have hleft := (OnePointProduct.map_eq_coe_iff _ v).mp hv.symm
      have hright := (OnePointProduct.map_eq_coe_iff _ v).mp (hm.symm.trans hv.symm)
      have ht := (JamesSphere.clock_eq_iff p.1 q.1).mp (hleft.1.trans hright.1.symm)
      have htime : p.1 = q.1 := by
        rcases ht with ht | ⟨ht, _⟩
        · exact ht
        · exact False.elim (ht.elim ht₀ ht₁)
      exact Or.inl (Prod.ext htime ((euclideanOnePointSphere n).symm.injective
        (hleft.2.trans hright.2.symm)))
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · exact ((evaluation_eq_pole_iff n p).mpr hp).trans
        ((evaluation_eq_pole_iff n q).mpr hq).symm

theorem evaluation_surjective (n : ℕ) : Function.Surjective (evaluation n) := by
  intro y
  obtain ⟨p, hp⟩ := JamesSphere.loopEvaluation_surjective n
    ((JamesSphere.SuspensionCoordinates.reorder n).symm y)
  refine ⟨(p.2, p.1), ?_⟩
  rw [evaluation_reorder, hp, Homeomorph.apply_symm_apply]

theorem evaluation_isQuotientMap (n : ℕ) : IsQuotientMap (evaluation n) :=
  IsQuotientMap.of_surjective_continuous (evaluation_surjective n) (evaluation n).continuous

theorem evaluation_quotient (n : ℕ) (t : unitInterval) (u : Fin n → unitInterval) :
    evaluation n (t, SmoothCube.quotient n u) = SmoothCube.quotient (n + 1) (Fin.cons t u) :=
  quotient_product n (Fin.cons t u)

theorem loop_evaluation {m n : ℕ} (p : GenLoop (Fin m) (Sphere n) (spherePole n))
    (u : Fin (m + 1) → unitInterval) :
    (loop p).val u = evaluation n (u 0, p.val (Fin.tail u)) := rfl

end NoExoticSixSphere.CubicalSphereSuspension
