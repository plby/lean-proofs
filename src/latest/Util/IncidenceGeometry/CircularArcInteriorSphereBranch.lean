import Util.IncidenceGeometry.TwoCirclesIntersectionsAtMostTwo
import Mathlib.Topology.Order.IntermediateValue

open Classical
noncomputable section

lemma CircularArcInteriorSphereBranch
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hr : 0 < r) (hγcont : Continuous γ) (hγinj : Function.Injective γ)
    (hcircle : ∀ t, dist (γ t) c = r)
    (τ : Set.Icc (0 : ℝ) 1) (hτ0 : 0 < τ.1) (hτ1 : τ.1 < 1)
    {ρ : ℝ} (hρpos : 0 < ρ)
    (hρlt_source : ρ < dist (γ τ) (γ ⟨0, by simp⟩))
    (hρlt_target : ρ < dist (γ τ) (γ ⟨1, by simp⟩)) :
    ∃ q₁ q₂ : EuclideanSpace ℝ (Fin 2),
      q₁ ≠ q₂ ∧
        q₁ ∈ Metric.sphere (γ τ) ρ ∧
          q₁ ∈ Set.range γ ∧
            q₂ ∈ Metric.sphere (γ τ) ρ ∧
              q₂ ∈ Set.range γ ∧
                ∀ q,
                  q ∈ Metric.sphere (γ τ) ρ →
                    q ∈ Set.range γ → q = q₁ ∨ q = q₂ := by
  let zeroI : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  let oneI : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
  let x0 : EuclideanSpace ℝ (Fin 2) := γ τ
  have hτ_nonneg : zeroI ≤ τ := by
    change (0 : ℝ) ≤ τ.1
    exact le_of_lt hτ0
  have hτ_le_one : τ ≤ oneI := by
    change τ.1 ≤ (1 : ℝ)
    exact le_of_lt hτ1
  have hcx : c ≠ x0 := by
    intro h
    have hx0_circle : dist x0 c = r := by
      simpa [x0] using hcircle τ
    rw [h, dist_self] at hx0_circle
    linarith
  let S : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p : EuclideanSpace ℝ (Fin 2) | dist p c = r ∧ dist p x0 = ρ}
  have hAtMost : S.Finite ∧ S.ncard ≤ 2 := by
    simpa [S] using TwoCirclesIntersectionsAtMostTwo c x0 hcx r ρ
  let f : Set.Icc (0 : ℝ) 1 → ℝ := fun u => dist (γ u) x0
  have hfcont : Continuous f := hγcont.dist continuous_const
  have hleft_mem : ρ ∈ Set.Icc (f τ) (f zeroI) := by
    constructor
    · dsimp [f, x0]
      simpa using hρpos.le
    · have hsource := le_of_lt hρlt_source
      rw [dist_comm] at hsource
      simpa [f, x0, zeroI] using hsource
  have hleft_image : ρ ∈ f '' Set.Icc zeroI τ :=
    (intermediate_value_Icc' hτ_nonneg hfcont.continuousOn) hleft_mem
  rcases hleft_image with ⟨s, hsInterval, hsρ⟩
  have hright_mem : ρ ∈ Set.Icc (f τ) (f oneI) := by
    constructor
    · dsimp [f, x0]
      simpa using hρpos.le
    · have htarget := le_of_lt hρlt_target
      rw [dist_comm] at htarget
      simpa [f, x0, oneI] using htarget
  have hright_image : ρ ∈ f '' Set.Icc τ oneI :=
    (intermediate_value_Icc hτ_le_one hfcont.continuousOn) hright_mem
  rcases hright_image with ⟨u, huInterval, huρ⟩
  let q₁ : EuclideanSpace ℝ (Fin 2) := γ s
  let q₂ : EuclideanSpace ℝ (Fin 2) := γ u
  have hq₁_sphere : q₁ ∈ Metric.sphere x0 ρ := by
    rw [Metric.mem_sphere]
    simpa [q₁, f] using hsρ
  have hq₂_sphere : q₂ ∈ Metric.sphere x0 ρ := by
    rw [Metric.mem_sphere]
    simpa [q₂, f] using huρ
  have hq₁_range : q₁ ∈ Set.range γ := ⟨s, rfl⟩
  have hq₂_range : q₂ ∈ Set.range γ := ⟨u, rfl⟩
  have hq_ne : q₁ ≠ q₂ := by
    intro hq
    have hsu : s = u := hγinj hq
    have hs_eq : s = τ := by
      apply le_antisymm
      · exact hsInterval.2
      · simpa [hsu] using huInterval.1
    have hρ_zero : ρ = 0 := by
      have hsρ' : f s = ρ := hsρ
      rw [hs_eq] at hsρ'
      dsimp [f, x0] at hsρ'
      simpa [dist_self] using hsρ'.symm
    linarith
  have hq₁S : q₁ ∈ S := by
    constructor
    · dsimp [q₁]
      exact hcircle s
    · exact Metric.mem_sphere.mp hq₁_sphere
  have hq₂S : q₂ ∈ S := by
    constructor
    · dsimp [q₂]
      exact hcircle u
    · exact Metric.mem_sphere.mp hq₂_sphere
  refine ⟨q₁, q₂, hq_ne, by simpa [x0] using hq₁_sphere, hq₁_range,
    by simpa [x0] using hq₂_sphere, hq₂_range, ?_⟩
  intro q hqSphere hqRange
  by_cases hq1 : q = q₁
  · exact Or.inl hq1
  by_cases hq2 : q = q₂
  · exact Or.inr hq2
  exfalso
  have hqS : q ∈ S := by
    rcases hqRange with ⟨w, rfl⟩
    constructor
    · exact hcircle w
    · exact Metric.mem_sphere.mp (by simpa [x0] using hqSphere)
  have htwo_lt : 2 < S.ncard := by
    refine (Set.two_lt_ncard_iff hAtMost.1).2 ?_
    exact ⟨q₁, q₂, q, hq₁S, hq₂S, hqS, hq_ne, Ne.symm hq1, Ne.symm hq2⟩
  exact (not_lt_of_ge hAtMost.2) htwo_lt
