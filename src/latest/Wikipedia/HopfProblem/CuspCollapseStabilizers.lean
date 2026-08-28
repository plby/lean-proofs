import Wikipedia.HopfProblem.CuspCollapseFibreTorus
import Wikipedia.HopfProblem.CuspCollapseStabilizersBasic

/-!
# Fibre-torus stabilizers in the actual toric charts

The three chart phases of a fibre-torus element have product one. A point with
at most one zero coordinate therefore has trivial stabilizer. With exactly two
zero coordinates, the stabilizer is the circle in their vertex-difference
direction. At the chart origin the entire fibre torus acts trivially.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

/-- The coordinate phases of a compact fibre-torus element in a toric chart. -/
def fibreCoordinatePhase (s : Triangle) (u : CompactFibreTorus) : CompactTorus :=
  fun i => ⟨factors s (compactTorusUnits (compactFibrePhase u)) i,
    mem_sphere_zero_iff_norm.mpr
      (norm_factors_compactTorusUnits s (compactFibrePhase u) i)⟩

@[simp] theorem fibreCoordinatePhase_coe (s : Triangle) (u : CompactFibreTorus)
    (i : Fin 3) :
    (fibreCoordinatePhase s u i : ℂ) =
      factors s (compactTorusUnits (compactFibrePhase u)) i := rfl

theorem fibreCoordinatePhase_prod (s : Triangle) (u : CompactFibreTorus) :
    ∏ i, fibreCoordinatePhase s u i = 1 := by
  apply Circle.ext
  change Circle.coeHom (∏ i, fibreCoordinatePhase s u i) = (1 : ℂ)
  rw [map_prod]
  change (∏ i, factors s (compactTorusUnits (compactFibrePhase u)) i) = 1
  simpa [Fin.prod_univ_succ, Triangle.time, mul_assoc]
    using time_factors s (compactTorusUnits (compactFibrePhase u))

theorem monomial_rays_fibreCoordinatePhase (s : Triangle) (u : CompactFibreTorus) :
    monomial s.rays (fun i => (fibreCoordinatePhase s u i : ℂ)) =
      fun i => (compactFibrePhase u i : ℂ) :=
  monomial_rays_factors s (compactTorusUnits (compactFibrePhase u))

theorem compactFibreAction_inclusion_eq_self_iff_coordinatePhase
    (u : CompactFibreTorus) (s : Triangle) (z : CoordinateSpace 3) :
    compactFibreAction u (inclusion s z) = inclusion s z ↔
      ∀ i, z i ≠ 0 → fibreCoordinatePhase s u i = 1 := by
  rw [compactFibreAction_eq_compact, compactTorusAction_inclusion_eq_self_iff]
  simp only [← fibreCoordinatePhase_coe, Circle.coe_eq_one]

/-- The vertex-difference circle is the quotient of the two height-one ray circles. -/
theorem compactFibrePhase_vertexDifference (s : Triangle) (j k : Fin 3) (a : Circle) :
    compactFibrePhase (fun i => a ^ (s.vertex k i - s.vertex j i)) =
      rayCompactPhase (s.vertex j) a⁻¹ * rayCompactPhase (s.vertex k) a := by
  funext i
  fin_cases i <;>
    simp [compactFibrePhase, rayCompactPhase, zpow_sub, mul_comm]

theorem factors_vertexDifferencePhase (s : Triangle) (j k : Fin 3) (a : Circle) :
    factors s (fibreMultiplier
      (compactFibreUnits (fun i => a ^ (s.vertex k i - s.vertex j i)))) =
      (fun i => if i = j then (a : ℂ)⁻¹ else 1) *
        (fun i => if i = k then (a : ℂ) else 1) := by
  rw [← compactTorusUnits_compactFibrePhase, compactFibrePhase_vertexDifference,
    map_mul, factors_mul, factors_rayCompactPhase_vertex, factors_rayCompactPhase_vertex]
  rfl

theorem vertexDifferencePhase_injective (s : Triangle) (j k : Fin 3) (hjk : j ≠ k) :
    Function.Injective (fun a : Circle =>
      (fun i : Fin 2 => a ^ (s.vertex k i - s.vertex j i))) := by
  intro a b hab
  have h := congrArg (fun u => factors s (fibreMultiplier (compactFibreUnits u)) k) hab
  rw [factors_vertexDifferencePhase, factors_vertexDifferencePhase] at h
  apply Circle.ext
  simpa [hjk.symm] using h

/-- With at most one zero coordinate, the fibre-torus stabilizer is trivial. -/
theorem compactFibreAction_inclusion_eq_self_iff_of_at_most_one_zero
    (u : CompactFibreTorus) (s : Triangle) (z : CoordinateSpace 3) (j : Fin 3)
    (hz : ∀ i, i ≠ j → z i ≠ 0) :
    compactFibreAction u (inclusion s z) = inclusion s z ↔ u = 1 := by
  constructor
  · intro h
    have hf := (compactFibreAction_inclusion_eq_self_iff_coordinatePhase u s z).mp h
    have hrest (i : Fin 3) (hij : i ≠ j) : fibreCoordinatePhase s u i = 1 :=
      hf i (hz i hij)
    have hp : (∏ i, fibreCoordinatePhase s u i) = fibreCoordinatePhase s u j :=
      Finset.prod_eq_single j (fun i _ hij => hrest i hij) (by simp)
    have hj : fibreCoordinatePhase s u j = 1 :=
      hp.symm.trans (fibreCoordinatePhase_prod s u)
    have hall : fibreCoordinatePhase s u = 1 := by
      funext i
      by_cases hij : i = j
      · simpa only [hij, Pi.one_apply] using hj
      · exact hrest i hij
    have hr := monomial_rays_fibreCoordinatePhase s u
    have hc : (fun i => (fibreCoordinatePhase s u i : ℂ)) = 1 := by
      rw [hall]
      rfl
    rw [hc, monomial_ones] at hr
    funext i
    apply Circle.ext
    have hi := congrFun hr i.castSucc
    fin_cases i <;> simpa [compactFibrePhase] using hi.symm
  · rintro rfl
    exact compactFibreAction_one _

/-- Exactly two zero coordinates leave precisely their vertex-difference circle. -/
theorem compactFibreAction_inclusion_eq_self_iff_of_two_zero
    (u : CompactFibreTorus) (s : Triangle) (z : CoordinateSpace 3) (j k : Fin 3)
    (hjk : j ≠ k) (hzj : z j = 0) (hzk : z k = 0)
    (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) :
    compactFibreAction u (inclusion s z) = inclusion s z ↔
      ∃ a : Circle, ∀ i : Fin 2, u i = a ^ (s.vertex k i - s.vertex j i) := by
  constructor
  · intro h
    have hf := (compactFibreAction_inclusion_eq_self_iff_coordinatePhase u s z).mp h
    have hrest (i : Fin 3) (hij : i ≠ j) (hik : i ≠ k) :
        fibreCoordinatePhase s u i = 1 := hf i (hz i hij hik)
    have hp : fibreCoordinatePhase s u j * fibreCoordinatePhase s u k = 1 := by
      calc
        fibreCoordinatePhase s u j * fibreCoordinatePhase s u k =
            ∏ i ∈ ({j, k} : Finset (Fin 3)), fibreCoordinatePhase s u i :=
          (Finset.prod_pair hjk).symm
        _ = ∏ i, fibreCoordinatePhase s u i := by
          apply Finset.prod_subset (Finset.subset_univ _)
          intro i _ hi
          have hi' : i ≠ j ∧ i ≠ k := by simpa using hi
          exact hrest i hi'.1 hi'.2
        _ = 1 := fibreCoordinatePhase_prod s u
    have hj : fibreCoordinatePhase s u j = (fibreCoordinatePhase s u k)⁻¹ :=
      eq_inv_iff_mul_eq_one.mpr hp
    let a := fibreCoordinatePhase s u k
    have hc : (fun i => (fibreCoordinatePhase s u i : ℂ)) =
        (fun i => if i = j then (a : ℂ)⁻¹ else 1) *
          (fun i => if i = k then (a : ℂ) else 1) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [hj, hjk, a]
      · by_cases hik : i = k
        · subst i
          simp [hjk.symm, a]
        · simp [hij, hik, hrest i hij hik]
    have hr := monomial_rays_fibreCoordinatePhase s u
    rw [hc, monomial_mul, monomial_single_coordinate_phase,
      monomial_single_coordinate_phase] at hr
    refine ⟨a, ?_⟩
    intro i
    apply Circle.ext
    have hi := congrFun hr i.castSucc
    have hphase : compactFibrePhase u i.castSucc = u i := by
      fin_cases i <;> rfl
    rw [hphase] at hi
    change (u i : ℂ) = (a : ℂ) ^ (s.vertex k i - s.vertex j i)
    rw [vertex, vertex, zpow_sub₀ a.coe_ne_zero, div_eq_mul_inv]
    simpa only [Pi.mul_apply, inv_zpow, mul_comm] using hi.symm
  · rintro ⟨a, ha⟩
    have hu : u = fun i => a ^ (s.vertex k i - s.vertex j i) := funext ha
    rw [compactFibreAction, torusAction_inclusion_eq_self_iff, hu]
    intro i hi
    have hij : i ≠ j := fun hij => hi (hij ▸ hzj)
    have hik : i ≠ k := fun hik => hi (hik ▸ hzk)
    rw [factors_vertexDifferencePhase]
    simp [hij, hik]

/-- The entire fibre torus fixes every affine chart origin. -/
@[simp] theorem compactFibreAction_inclusion_zero (u : CompactFibreTorus) (s : Triangle) :
    compactFibreAction u (inclusion s 0) = inclusion s 0 := by
  rw [compactFibreAction, torusAction_inclusion_eq_self_iff]
  intro i hi
  exact (hi rfl).elim

end Wikipedia.HopfProblem.ToricSpace
