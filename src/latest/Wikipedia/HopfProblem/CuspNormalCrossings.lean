import Wikipedia.HopfProblem.NormalCrossing
import Wikipedia.HopfProblem.CuspSubmersion

/-!
# Normal-crossing charts on the central cusp fibre

The affine equation `t = z₀z₁z₂` gives centred normal-crossing charts
upstairs. Restriction to the tube and descent through the holomorphic
covering give the same local equations on the actual quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

open ToricCharts ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃

namespace ToricSpace

theorem time_normalCrossingAt (x : Space) (hx : time x = 0) : HasNormalCrossingAt time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have he : (parametrization s).symm ∈ IsManifold.maximalAtlas I₃ ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self s)
  apply normalCrossingAt_of_chart (parametrization s).symm he _ hx
  · intro w _
    exact time_inclusion s w
  · change inclusion s z ∈ (parametrization s).target
    rw [parametrization_target]
    exact mem_range_self z

end ToricSpace

namespace CuspQuotient

open ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

theorem projection_normalCrossingAt (x : QuotientSpace C ε) (hx : projection C ε x = 0) :
    letI := chartedSpace C ε hε hε1 hC hR
    HasNormalCrossingAt (projection C ε) x := by
  let := tubeAction C (disc ε)
  let hq := quotientMap_covering C ε hε hε1 hC hR
  obtain ⟨a, rfl⟩ := hq.surjective x
  have ha : time (a : Space) = 0 := hx
  have h := (time_normalCrossingAt (a : Space) ha).restrict (tubeOpen (disc ε)) a
  have h' : HasNormalCrossingAt (projection C ε ∘ quotientMap C ε) a := by
    simpa only [Function.comp_def, projection_quotientMap] using h
  exact h'.descend hq (fun v => tubeTranslate_holomorphic C (disc ε) v.toAdd hC)

/-- The local defining function is a product of one, two, or three distinct
coordinates, in a chart centred at the given central-fibre point. -/
theorem central_local_equation (x : QuotientSpace C ε) (hx : projection C ε x = 0) :
    letI := chartedSpace C ε hε hε1 hC hR
    ∃ J : Finset (Fin 3), ∃ e : OpenPartialHomeomorph (QuotientSpace C ε) E₃,
      (J.card = 1 ∨ J.card = 2 ∨ J.card = 3) ∧
      e ∈ IsManifold.maximalAtlas I₃ ω (QuotientSpace C ε) ∧
      x ∈ e.source ∧ e x = 0 ∧
      ∀ w ∈ e.target, projection C ε (e.symm w) = ∏ j ∈ J, w j := by
  let := chartedSpace C ε hε hε1 hC hR
  obtain ⟨J, hJ, e, he, hx', hc, hp⟩ := projection_normalCrossingAt C ε hε hε1 hC hR x hx
  have hpos : 0 < J.card := Finset.card_pos.mpr hJ
  have hle : J.card ≤ 3 := by simpa using Finset.card_le_card (Finset.subset_univ J)
  exact ⟨J, e, by omega, he, hx', hc, hp⟩

end CuspQuotient

end Wikipedia.HopfProblem
