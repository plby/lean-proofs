import ErdosProblems.Erdos941.SphereOrbitCount

/-! # Counting integral sphere pairs rather than their orthogonal orbits -/

namespace Erdos941

open PairLocal

def spherePairEquivFinset (n : ℕ) (e : ℤ) :
    SpherePair ℤ (n : ℤ) e ≃ {p // p ∈ spherePairs n e} where
  toFun p := ⟨p.1, mem_spherePairs.mpr p.2⟩
  invFun p := ⟨p.1, mem_spherePairs.mp p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance finite_integer_spherePair (n : ℕ) (e : ℤ) : Finite (SpherePair ℤ (n : ℤ) e) :=
  Finite.of_equiv _ (spherePairEquivFinset n e).symm

theorem card_integer_spherePair (n : ℕ) (e : ℤ) :
    Nat.card (SpherePair ℤ (n : ℤ) e) = (spherePairs n e).card := by
  rw [Nat.card_congr (spherePairEquivFinset n e), Nat.card_eq_fintype_card, Fintype.card_coe]

def integerSphereGroupColumns (g : sphereSpecialGroup ℤ) :
    {v // v ∈ spherePoints 1} × {v // v ∈ spherePoints 1} × {v // v ∈ spherePoints 1} :=
  (⟨g.1 (1, 0, 0), mem_spherePoints.mpr (by simpa [normThree, tripleNorm, norm3] using g.2.1 (1, 0, 0))⟩,
    ⟨g.1 (0, 1, 0), mem_spherePoints.mpr (by simpa [normThree, tripleNorm, norm3] using g.2.1 (0, 1, 0))⟩,
    ⟨g.1 (0, 0, 1), mem_spherePoints.mpr (by simpa [normThree, tripleNorm, norm3] using g.2.1 (0, 0, 1))⟩)

theorem integerSphereGroupColumns_injective : Function.Injective integerSphereGroupColumns := by
  intro g h heq
  have h0 := congrArg (fun v => v.1.1) heq
  have h1 := congrArg (fun v => v.2.1.1) heq
  have h2 := congrArg (fun v => v.2.2.1) heq
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.1.toLinearMap v = h.1.toLinearMap v
  rw [map_eq_three_combination g.1.toLinearMap, map_eq_three_combination h.1.toLinearMap]
  change g.1.toLinearMap (1, 0, 0) = h.1.toLinearMap (1, 0, 0) at h0
  change g.1.toLinearMap (0, 1, 0) = h.1.toLinearMap (0, 1, 0) at h1
  change g.1.toLinearMap (0, 0, 1) = h.1.toLinearMap (0, 0, 1) at h2
  rw [h0, h1, h2]

instance finite_integer_sphereSpecialGroup : Finite (sphereSpecialGroup ℤ) :=
  Finite.of_injective integerSphereGroupColumns integerSphereGroupColumns_injective

theorem card_le_group_mul_card_orbits (G X : Type*) [Group G] [MulAction G X]
    [Finite G] [Finite X] :
    Nat.card X ≤ Nat.card G * Nat.card (Quotient (MulAction.orbitRel G X)) := by
  classical
  let f : G × Quotient (MulAction.orbitRel G X) → X := fun z => z.1 • z.2.out
  have hf : Function.Surjective f := by
    intro x
    have hrel := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)).symm
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    exact ⟨(g, Quotient.mk _ x), hg⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

theorem spherePairs_card_le_group_mul_orbits (n : ℕ) (e : ℤ) :
    (spherePairs n e).card ≤ Nat.card (sphereSpecialGroup ℤ) *
      Nat.card (SpherePairOrbits ℤ (n : ℤ) e) := by
  rw [← card_integer_spherePair]
  exact card_le_group_mul_card_orbits (sphereSpecialGroup ℤ) (SpherePair ℤ (n : ℤ) e)

theorem exists_sphere_pair_count_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (e : ℤ), n ≠ 0 → e ^ 2 ≠ (n : ℤ) ^ 2 →
      ((spherePairs n e).card : ℝ) ≤
        C * pairSquareContent (-(n : ℤ)) (-(2 * e)) *
          ((spherePairDiscriminant n e).natAbs : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := exists_sphere_pair_orbit_bound_all hε
  have hG : (0 : ℝ) < Nat.card (sphereSpecialGroup ℤ) := by exact_mod_cast Nat.card_pos
  refine ⟨Nat.card (sphereSpecialGroup ℤ) * C, mul_pos hG hC, ?_⟩
  intro n e hn hnd
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hcard : ((spherePairs n e).card : ℝ) ≤ Nat.card (sphereSpecialGroup ℤ) *
      (Nat.card (SpherePairOrbits ℤ (n : ℤ) e) : ℝ) := by
    exact_mod_cast spherePairs_card_le_group_mul_orbits n e
  exact hcard.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound n e hnZ hnd) hG.le)

end Erdos941
