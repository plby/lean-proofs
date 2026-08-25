import Mathlib.Tactic
import Util.IncidenceGeometry.FiniteCyclicAngleSuccessor
import Util.IncidenceGeometry.PlanarClockwiseSweptTwoRayEndpointConesInSector
import Util.IncidenceGeometry.PlanarNormalizedAngleRepresentation
import Util.IncidenceGeometry.PlanarRot90ClockwiseWedgeRayPartition
import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness
import Util.IncidenceGeometry.PlanarRot90Decomposition
import Util.IncidenceGeometry.PlanarRot90Norm
import Util.IncidenceGeometry.PlanarRot90Orthogonal
import Util.IncidenceGeometry.PlanarSlitDiskEndpointConesAvoidRay

open Classical
noncomputable section

lemma FinitePlanarClockwiseSuccessorSectors {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (p : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (u : ι → EuclideanSpace ℝ (Fin 2))
    (hρ : 0 < ρ)
    (hu : ∀ i : ι, u i ≠ 0)
    (hposRayDistinct :
      ∀ {i j : ι}, (∃ t : ℝ, 0 < t ∧ u j = t • u i) → i = j) :
    ∃ clockwiseNext : Equiv.Perm ι,
      ∃ fullClockwiseTurn : ℝ,
      ∃ clockwiseTurn : ι → ι → ℝ,
      ∃ sector : ι → Set (EuclideanSpace ℝ (Fin 2)),
        fullClockwiseTurn = 2 * Real.pi ∧
        0 < fullClockwiseTurn ∧
        (∀ i j : ι, 0 < clockwiseTurn i j) ∧
        (∀ i j : ι, clockwiseTurn i j ≤ fullClockwiseTurn) ∧
        (∀ i j : ι, clockwiseTurn i j = fullClockwiseTurn ↔ j = i) ∧
        (∀ i j : ι, j ≠ i →
          clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
        (∀ i : ι, clockwiseNext i = i ↔ ∀ j : ι, j = i) ∧
        (∀ i : ι,
          if h : clockwiseNext i = i then
            sector i =
              Metric.ball p ρ \
                ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
                  ({p} : Set (EuclideanSpace ℝ (Fin 2))))
          else
            ∃ c s : ℝ,
              (s ≠ 0 ∨ c < 0) ∧
              u (clockwiseNext i) = c • u i - s • PlanarRot90 (u i) ∧
              sector i =
                (let base : EuclideanSpace ℝ (Fin 2) := u i
                 let baseChart : EuclideanSpace ℝ (Fin 2) →
                    EuclideanSpace ℝ (Fin 2) :=
                  fun z => p + z 0 • base + z 1 • PlanarRot90 base
                 if 0 < s then
                   baseChart ''
                    {z : EuclideanSpace ℝ (Fin 2) |
                      z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                      z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
                 else if s < 0 then
                   baseChart ''
                    {z : EuclideanSpace ℝ (Fin 2) |
                      z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                      (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
                 else
                   baseChart ''
                    {z : EuclideanSpace ℝ (Fin 2) |
                      z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                      z 1 < 0})) ∧
        (∀ i : ι, IsOpen (sector i) ∧ IsConnected (sector i)) ∧
        (∀ i : ι, sector i ⊆ Metric.ball p ρ) ∧
        (∀ i j : ι,
          Disjoint (sector i)
            {q | ∃ t : ℝ, 0 < t ∧ q = p + t • u j}) ∧
        (∀ q : EuclideanSpace ℝ (Fin 2),
          q ∈ Metric.ball p ρ →
            q ≠ p →
              (∀ i : ι,
                q ∉ {x | ∃ t : ℝ, 0 < t ∧ x = p + t • u i}) →
                ∃ i : ι, q ∈ sector i) := by
  classical
  let θ : ι → ℝ := fun i =>
    let z : ℂ := ((u i) 0 : ℂ) + ((u i) 1 : ℂ) * Complex.I
    let a : ℝ := Complex.arg z
    if 0 ≤ a then a else a + 2 * Real.pi
  have hnorm : ∀ i : ι,
      0 ≤ θ i ∧ θ i < 2 * Real.pi ∧
        ∃ r : ℝ, 0 < r ∧
          u i =
            r • WithLp.toLp 2
              (fun k : Fin 2 => if k = 0 then Real.cos (θ i) else Real.sin (θ i)) := by
    intro i
    simpa [θ] using PlanarNormalizedAngleRepresentation (u i) (hu i)
  have hθ_mem : ∀ i : ι, 0 ≤ θ i ∧ θ i < 2 * Real.pi := by
    intro i
    exact ⟨(hnorm i).1, (hnorm i).2.1⟩
  have hθ_ray :
      ∀ i : ι, ∃ r : ℝ, 0 < r ∧
        u i =
          r • WithLp.toLp 2
            (fun k : Fin 2 => if k = 0 then Real.cos (θ i) else Real.sin (θ i)) := by
    intro i
    exact (hnorm i).2.2
  have hθ_inj : Function.Injective θ := by
    intro i j hij
    rcases hθ_ray i with ⟨ri, hri, hui⟩
    rcases hθ_ray j with ⟨rj, hrj, huj⟩
    apply hposRayDistinct (i := i) (j := j)
    refine ⟨rj / ri, div_pos hrj hri, ?_⟩
    calc
      u j =
          rj • WithLp.toLp 2
            (fun k : Fin 2 => if k = 0 then Real.cos (θ j) else Real.sin (θ j)) := huj
      _ =
          rj • WithLp.toLp 2
            (fun k : Fin 2 => if k = 0 then Real.cos (θ i) else Real.sin (θ i)) := by
            rw [hij]
      _ =
          (rj / ri) •
            (ri • WithLp.toLp 2
              (fun k : Fin 2 => if k = 0 then Real.cos (θ i) else Real.sin (θ i))) := by
            rw [smul_smul]
            field_simp [ne_of_gt hri]
      _ = (rj / ri) • u i := by
            rw [hui]
  rcases FiniteCyclicAngleSuccessor θ hθ_mem hθ_inj with
    ⟨clockwiseNext, clockwiseTurn, hturn_eq, hturn_pos, hturn_le, hturn_full,
      hminimal_le, _hminimal_lt, hfixed, hgap_empty, hgap_cover⟩
  rcases PlanarRot90ClockwiseWedgeRayPartition p ρ u θ clockwiseNext clockwiseTurn
      hρ hu hposRayDistinct hθ_mem hθ_inj hθ_ray hturn_eq hfixed
      hgap_empty hgap_cover with
    ⟨sector, hsector_def, hsector_open_connected, hsector_ball,
      hsector_disjoint, hsector_cover⟩
  refine ⟨clockwiseNext, 2 * Real.pi, clockwiseTurn, sector, rfl, ?_,
    hturn_pos, hturn_le, hturn_full, hminimal_le, hfixed, hsector_def,
    hsector_open_connected, hsector_ball, hsector_disjoint, hsector_cover⟩
  exact mul_pos (by norm_num) Real.pi_pos
