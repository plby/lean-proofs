import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous motion of both endpoints inside a fixed interval
-/

namespace Erdos964

open Filter MeasureTheory
open scoped Topology

theorem intervalIntegrable_of_continuousOn_Icc (g : ℝ → ℝ) (a b s t : ℝ)
    (hg : ContinuousOn g (Set.Icc a b)) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    IntervalIntegrable g volume s t := by
  apply ContinuousOn.intervalIntegrable
  apply hg.mono
  intro x hx
  exact ⟨(le_min hs.1 ht.1).trans hx.1, hx.2.trans (max_le hs.2 ht.2)⟩

theorem integral_eq_primitive_sub_on_Icc (g : ℝ → ℝ) (a b s t : ℝ)
    (hg : ContinuousOn g (Set.Icc a b)) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    (∫ x in s..t, g x) = (∫ x in a..t, g x) - ∫ x in a..s, g x := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_continuousOn_Icc g a b a s hg ha hs)
    (intervalIntegrable_of_continuousOn_Icc g a b s t hg hs ht)
  linarith

theorem tendsto_intervalIntegral_endpoints {ι : Type*} {l : Filter ι}
    (g : ℝ → ℝ) (a b u₀ v₀ : ℝ) (u v : ι → ℝ)
    (hg : ContinuousOn g (Set.Icc a b))
    (hu₀ : u₀ ∈ Set.Icc a b) (hv₀ : v₀ ∈ Set.Icc a b)
    (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀))
    (huI : ∀ᶠ i in l, u i ∈ Set.Icc a b) (hvI : ∀ᶠ i in l, v i ∈ Set.Icc a b) :
    Tendsto (fun i => ∫ x in u i..v i, g x) l (𝓝 (∫ x in u₀..v₀, g x)) := by
  have hab : a ≤ b := hu₀.1.trans hu₀.2
  have hprimitive : ContinuousOn (fun t => ∫ x in a..t, g x) (Set.Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn g (Set.uIcc a b) volume by
        simpa only [Set.uIcc_of_le hab] using hg.integrableOn_Icc)
    simpa only [Set.uIcc_of_le hab] using h
  have huwithin : Tendsto u l (𝓝[Set.Icc a b] u₀) := tendsto_nhdsWithin_iff.mpr ⟨hu, huI⟩
  have hvwithin : Tendsto v l (𝓝[Set.Icc a b] v₀) := tendsto_nhdsWithin_iff.mpr ⟨hv, hvI⟩
  have h := ((hprimitive v₀ hv₀).tendsto.comp hvwithin).sub
    ((hprimitive u₀ hu₀).tendsto.comp huwithin)
  rw [← integral_eq_primitive_sub_on_Icc g a b u₀ v₀ hg hu₀ hv₀] at h
  apply h.congr'
  filter_upwards [huI, hvI] with i hui hvi
  exact (integral_eq_primitive_sub_on_Icc g a b (u i) (v i) hg hui hvi).symm

end Erdos964
