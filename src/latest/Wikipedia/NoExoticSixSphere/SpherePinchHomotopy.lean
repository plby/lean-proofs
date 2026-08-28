import Wikipedia.NoExoticSixSphere.SpherePinchMap
import Mathlib.Topology.Homotopy.Basic

/-!
# A homotopy of the actual pinch from based input homotopies

Currying the given homotopies makes them maps into the actual continuous
path space. Hemisphere gluing there gives a jointly continuous homotopy
of pinch maps, fixed on the original equator. No group-law identification
or smoothness of the given homotopies is required.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SphereFold

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y] (v : UnitSphere E)
  (f₀ g₀ f₁ g₁ : C(UnitSphere E, Y))
  (hbase₀ : f₀ (antipode v) = g₀ (antipode v))
  (hbase₁ : f₁ (antipode v) = g₁ (antipode v))

def pinchHomotopyRel
    (Hf : f₀.HomotopyRel f₁ {antipode v}) (Hg : g₀.HomotopyRel g₁ {antipode v}) :
    (pinch v f₀ g₀ hbase₀).HomotopyRel (pinch v f₁ g₁ hbase₁) (equator v) := by
  let swap : C(UnitSphere E × unitInterval, unitInterval × UnitSphere E) :=
    ⟨Prod.swap, continuous_swap⟩
  let a : C(UnitSphere E, C(unitInterval, Y)) :=
    (Hf.toHomotopy.toContinuousMap.comp swap).curry
  let b : C(UnitSphere E, C(unitInterval, Y)) :=
    (Hg.toHomotopy.toContinuousMap.comp swap).curry
  have hab : a (antipode v) = b (antipode v) := by
    apply ContinuousMap.ext
    intro t
    change Hf (t, antipode v) = Hg (t, antipode v)
    rw [Hf.eq_fst t (mem_singleton _), Hg.eq_fst t (mem_singleton _), hbase₀]
  let p := pinch v a b hab
  refine {
    toContinuousMap := p.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro x
    change p x 0 = pinch v f₀ g₀ hbase₀ x
    by_cases hx : 0 ≤ height v x
    · rw [pinch_north v a b hab x hx, pinch_north v f₀ g₀ hbase₀ x hx]
      exact Hf.toHomotopy.map_zero_left _
    · rw [pinch_south v a b hab x (lt_of_not_ge hx).le,
        pinch_south v f₀ g₀ hbase₀ x (lt_of_not_ge hx).le]
      exact Hg.toHomotopy.map_zero_left _
  · intro x
    change p x 1 = pinch v f₁ g₁ hbase₁ x
    by_cases hx : 0 ≤ height v x
    · rw [pinch_north v a b hab x hx, pinch_north v f₁ g₁ hbase₁ x hx]
      exact Hf.toHomotopy.map_one_left _
    · rw [pinch_south v a b hab x (lt_of_not_ge hx).le,
        pinch_south v f₁ g₁ hbase₁ x (lt_of_not_ge hx).le]
      exact Hg.toHomotopy.map_one_left _
  · intro t x hx
    have hx0 : height v x = 0 := hx
    change p x t = pinch v f₀ g₀ hbase₀ x
    rw [pinch_equator v a b hab x hx0, pinch_equator v f₀ g₀ hbase₀ x hx0]
    exact Hf.eq_fst t (mem_singleton _)

theorem pinch_homotopic
    (Hf : f₀.HomotopicRel f₁ {antipode v}) (Hg : g₀.HomotopicRel g₁ {antipode v}) :
    (pinch v f₀ g₀ hbase₀).Homotopic (pinch v f₁ g₁ hbase₁) := by
  obtain ⟨Hf⟩ := Hf
  obtain ⟨Hg⟩ := Hg
  exact ⟨(pinchHomotopyRel v f₀ g₀ f₁ g₁ hbase₀ hbase₁ Hf Hg).toHomotopy⟩

end NoExoticSixSphere.SphereFold
