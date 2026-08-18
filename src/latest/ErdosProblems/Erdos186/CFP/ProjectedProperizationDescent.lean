/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationTerminal
import ErdosProblems.Erdos186.CFP.ProjectedProperizationRankDrop

/-!
# Accumulated primitive descent for projected properization

The state remembers three facts through every primitive rank drop: unit-ball
points of the initial coefficient body survive, the whole initial map range
survives, and a point of radius `t` in the current body lifts to the initial
body with additive cost `drops * h`.  Strong induction stops at a descendant
whose map is injective on the common radius-`h` ball.
-/

namespace Erdos186.CFP.ProjectedProperization

open Bilu.Mahler
open Bilu.Section92ShortKernel
open Bilu.Section92ShortKernel.PrimitiveIntegralQuotient
open ProjectedProperizationRankDrop

noncomputable section

/-- Data preserved while quotienting primitive kernel directions. -/
structure DescentState {r e h : ℕ}
    (p₀ : Seminorm ℝ (Fin r → ℝ))
    (phi₀ : IntegralPoint r →+ LatticePoint e) where
  rank : ℕ
  drops : ℕ
  rank_add_drops : rank + drops = r
  seminorm : Seminorm ℝ (Fin rank → ℝ)
  definite : IsDefinite seminorm
  full : AdmitsIndependent seminorm rank 1
  map : IntegralPoint rank →+ LatticePoint e
  unit_survives : ∀ z₀ : IntegralPoint r,
    p₀ (integralEmbed z₀) ≤ 1 →
      ∃ z : IntegralPoint rank,
        seminorm (integralEmbed z) ≤ 1 ∧ map z = phi₀ z₀
  range_survives : ∀ z₀ : IntegralPoint r,
    ∃ z : IntegralPoint rank, map z = phi₀ z₀
  lift_back : ∀ (t : ℝ), 0 ≤ t → ∀ z : IntegralPoint rank,
    seminorm (integralEmbed z) ≤ t →
      ∃ z₀ : IntegralPoint r,
        phi₀ z₀ = map z ∧
          p₀ (integralEmbed z₀) ≤ t + (drops : ℝ) * (h : ℝ)

namespace DescentState

variable {r e h : ℕ} {p₀ : Seminorm ℝ (Fin r → ℝ)}
  {phi₀ : IntegralPoint r →+ LatticePoint e}

/-- Initial state before any quotient. -/
def initial (hp₀ : IsDefinite p₀) (hfull : AdmitsIndependent p₀ r 1) :
    DescentState (h := h) p₀ phi₀ where
  rank := r
  drops := 0
  rank_add_drops := by simp
  seminorm := p₀
  definite := hp₀
  full := hfull
  map := phi₀
  unit_survives := fun z hz ↦ ⟨z, hz, rfl⟩
  range_survives := fun z ↦ ⟨z, rfl⟩
  lift_back := by
    intro t ht z hz
    exact ⟨z, rfl, by simpa using hz⟩

/-- One failed injectivity test strictly lowers rank and adds at most `h`
to the eventual lifting cost. -/
def reduce (X : DescentState (h := h) p₀ phi₀)
    (S : PrimitiveKernelStep X.seminorm X.map (h : ℝ)) :
    DescentState (h := h) p₀ phi₀ := by
  let p' : Seminorm ℝ (Fin S.quotient.complementRank → ℝ) :=
    genericCoordinateProjectedSeminorm S X.definite
  refine
    { rank := S.quotient.complementRank
      drops := X.drops + 1
      rank_add_drops := ?_
      seminorm := p'
      definite := ?_
      full := ?_
      map := S.quotient.reducedMap
      unit_survives := ?_
      range_survives := ?_
      lift_back := ?_ }
  · have hrank := S.quotient.rank_eq
    calc
      S.quotient.complementRank + (X.drops + 1) =
          (S.quotient.complementRank + 1) + X.drops := by omega
      _ = X.rank + X.drops := by rw [hrank]
      _ = r := X.rank_add_drops
  · exact isDefinite_genericCoordinateProjectedSeminorm S X.definite
  · exact admitsIndependent_genericCoordinateProjectedSeminorm S X.definite X.full
  · intro z₀ hz₀
    obtain ⟨z, hz, hmap⟩ := X.unit_survives z₀ hz₀
    refine ⟨S.quotient.complementCoordinates z, ?_, ?_⟩
    · exact genericCoordinateProjectedSeminorm_complementCoordinates_le_one
        S X.definite z hz
    · rw [S.quotient.reducedMap_complementCoordinates, hmap]
  · intro z₀
    obtain ⟨z, hmap⟩ := X.range_survives z₀
    refine ⟨S.quotient.complementCoordinates z, ?_⟩
    rw [S.quotient.reducedMap_complementCoordinates, hmap]
  · intro t ht z hz
    obtain ⟨x, hmap, hx⟩ :=
      exists_integral_lift_of_genericCoordinateProjectedSeminorm_le
        S X.definite ht z hz
    obtain ⟨z₀, hz₀map, hz₀⟩ := X.lift_back (t + (h : ℝ))
      (add_nonneg ht (by positivity)) x hx
    refine ⟨z₀, hz₀map.trans hmap, ?_⟩
    calc
      p₀ (integralEmbed z₀) ≤
          (t + (h : ℝ)) + (X.drops : ℝ) * (h : ℝ) := hz₀
      _ = t + ((X.drops + 1 : ℕ) : ℝ) * (h : ℝ) := by
        push_cast
        ring

/-- Every state has a descendant which passes the common bounded-ball
injectivity test. -/
theorem exists_injective_descendant
    (X : DescentState (h := h) p₀ phi₀) :
    ∃ Y : DescentState (h := h) p₀ phi₀,
      Set.InjOn Y.map
        {z : IntegralPoint Y.rank |
          Y.seminorm (integralEmbed z) ≤ (h : ℝ)} := by
  have aux : ∀ n : ℕ,
      ∀ X : DescentState (h := h) p₀ phi₀, X.rank = n →
        ∃ Y : DescentState (h := h) p₀ phi₀,
          Set.InjOn Y.map
            {z : IntegralPoint Y.rank |
              Y.seminorm (integralEmbed z) ≤ (h : ℝ)} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hX
      by_cases hinj : Set.InjOn X.map
          {z : IntegralPoint X.rank |
            X.seminorm (integralEmbed z) ≤ (h : ℝ)}
      · exact ⟨X, hinj⟩
      · obtain ⟨S⟩ := exists_primitiveKernelStep_of_not_injOn_ball
          X.seminorm X.map (h : ℝ) hinj
        let Y := X.reduce S
        have hYlt : Y.rank < n := by
          rw [← hX]
          exact complementRank_lt S
        exact ih Y.rank hYlt Y rfl
  exact aux X.rank X rfl

end DescentState

end

end Erdos186.CFP.ProjectedProperization

#print axioms Erdos186.CFP.ProjectedProperization.DescentState.reduce
#print axioms
  Erdos186.CFP.ProjectedProperization.DescentState.exists_injective_descendant
