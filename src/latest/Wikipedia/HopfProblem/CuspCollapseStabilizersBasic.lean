import Wikipedia.HopfProblem.CuspRetractionPolar
import Wikipedia.HopfProblem.ToricDivisors

/-!
# Chart stabilizers and the circle of a central toric ray

An acting-torus element fixes a point precisely when every nonzero chart
coordinate has phase one.  The height-one circle through a ray has only
the corresponding chart phase, so it fixes the entire ray divisor,
including all of its boundary strata.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

/-- The stabilizer condition in an actual affine chart. -/
theorem torusAction_inclusion_eq_self_iff (u : ActingTorus) (s : Triangle)
    (z : CoordinateSpace 3) :
    torusAction u (inclusion s z) = inclusion s z ↔
      ∀ i, z i ≠ 0 → factors s u i = 1 := by
  rw [torusAction_inclusion, (inclusion_openEmbedding s).injective.eq_iff]
  constructor
  · intro h i hi
    apply mul_right_cancel₀ hi
    simpa only [scale, Pi.mul_apply, one_mul] using congrFun h i
  · intro h
    funext i
    change factors s u i * z i = z i
    by_cases hi : z i = 0
    · simp only [hi, mul_zero]
    · rw [h i hi, one_mul]

theorem compactTorusAction_inclusion_eq_self_iff (u : CompactTorus) (s : Triangle)
    (z : CoordinateSpace 3) :
    compactTorusAction u (inclusion s z) = inclusion s z ↔
      ∀ i, z i ≠ 0 → factors s (compactTorusUnits u) i = 1 :=
  torusAction_inclusion_eq_self_iff (compactTorusUnits u) s z

/-- The compact one-parameter subgroup of the height-one ray `(v,1)`. -/
def rayCompactPhase (v : Fin 2 → ℤ) (a : Circle) : CompactTorus :=
  ![a ^ v 0, a ^ v 1, a]

@[simp] theorem rayCompactPhase_two (v : Fin 2 → ℤ) (a : Circle) :
    rayCompactPhase v a 2 = a := rfl

theorem rayCompactPhase_vertex_coe (s : Triangle) (j : Fin 3) (a : Circle) :
    (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) =
      fun i => (a : ℂ) ^ s.rays i j := by
  funext i
  fin_cases i <;> simp [rayCompactPhase, vertex]

/-- A monomial evaluated on a single coordinate phase is the
corresponding matrix column of powers. -/
theorem monomial_single_coordinate_phase (A : Matrix (Fin 3) (Fin 3) ℤ)
    (j : Fin 3) (a : ℂ) :
    monomial A (fun k => if k = j then a else 1) = fun i => a ^ A i j := by
  funext i
  change (∏ k, (if k = j then a else 1) ^ A i k) = _
  calc
    (∏ k, (if k = j then a else 1) ^ A i k) =
        ∏ k, if k = j then a ^ A i k else 1 := by
      apply Finset.prod_congr rfl
      intro k _
      split_ifs <;> simp
    _ = a ^ A i j := by simp

/-- The inverse ray matrix turns the ray circle into a single chart
phase.  This calculation does not use nonvanishing of chart coordinates. -/
theorem factors_rayCompactPhase_vertex (s : Triangle) (j : Fin 3) (a : Circle) :
    factors s (compactTorusUnits (rayCompactPhase (s.vertex j) a)) =
      fun i => if i = j then (a : ℂ) else 1 := by
  let w : CoordinateSpace 3 := fun i => if i = j then (a : ℂ) else 1
  have hw : w ∈ torus := by
    intro i
    dsimp [w]
    split_ifs
    · exact a.coe_ne_zero
    · exact one_ne_zero
  have hv : (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) =
      monomial s.rays w := by
    rw [rayCompactPhase_vertex_coe]
    exact (monomial_single_coordinate_phase s.rays j a).symm
  change monomial s.dual (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) = _
  rw [hv, monomial_mul_on_torus _ _ hw, dual_rays, monomial_one]

/-- The ray circle fixes every point of the corresponding actual central
component, not only its open stratum. -/
theorem rayCompactPhase_fixes_of_mem_rayDivisor (v : Fin 2 → ℤ) (a : Circle)
    {x : Space} (hx : x ∈ rayDivisor v) :
    compactTorusAction (rayCompactPhase v a) x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨j, hj, rfl⟩ := (mem_rayDivisor_inclusion v s z).mp hx
  apply (compactTorusAction_inclusion_eq_self_iff _ s z).mpr
  intro i hi
  have hij : i ≠ j := by
    intro h
    subst i
    exact hi hj
  rw [factors_rayCompactPhase_vertex]
  exact if_neg hij

end Wikipedia.HopfProblem.ToricSpace
