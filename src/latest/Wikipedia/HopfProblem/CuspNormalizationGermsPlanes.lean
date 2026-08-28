import Wikipedia.HopfProblem.ToricComponentCharts
import Mathlib.Topology.Germ

/-!
# Germs on the actual coordinate-plane union

A function vanishes as a germ on a finite union of coordinate planes if
and only if its pullback to every actual plane vanishes as a germ.  This
is proved for ordinary functions and neighbourhood filters, before any
analytic-ring construction.

At an arbitrary point of the central equation `z₀ z₁ z₂ = 0`, translation
to the origin gives the union of exactly its vanishing coordinate planes
as a set germ.  Nonvanishing coordinates stay nonzero on a genuine open
neighbourhood.  Thus the one-, two-, and three-branch cases use the actual
central-fibre equation, rather than a polynomial surrogate.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open ToricCharts ToricFan ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

/-- The literal union of the selected coordinate planes in complex
three-space. -/
def planeUnion (s : Finset (Fin 3)) : Set E₃ :=
  {z | ∃ j ∈ s, z j = 0}

theorem planeUnion_eq_product_zero (s : Finset (Fin 3)) :
    planeUnion s = {z : E₃ | ∏ j ∈ s, z j = 0} := by
  ext z
  simp only [planeUnion, Finset.prod_eq_zero_iff]

@[simp] theorem insertZero_zero (j : Fin 3) : insertZero j (0 : E₂) = 0 := by
  ext k
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · exact insertZero_at _ 0
  · simp [insertZero, Fin.insertNth_apply_succAbove]

@[simp] theorem removeCoordinate_zero (j : Fin 3) : removeCoordinate j (0 : E₃) = 0 := rfl

theorem insertZero_add (j : Fin 3) (z w : E₂) :
    insertZero j (z + w) = insertZero j z + insertZero j w := by
  ext k
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simp only [Pi.add_apply, insertZero_at, add_zero]
  · simp [insertZero, Fin.insertNth_apply_succAbove]

theorem insertZero_mem_planeUnion {s : Finset (Fin 3)} {j : Fin 3} (hj : j ∈ s) (z : E₂) :
    insertZero j z ∈ planeUnion s := ⟨j, hj, insertZero_at j z⟩

theorem insertZero_tendsto_planeUnion {s : Finset (Fin 3)} {j : Fin 3} (hj : j ∈ s) :
    Tendsto (insertZero j) (𝓝 (0 : E₂)) (𝓝[planeUnion s] (0 : E₃)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have ht : Tendsto (insertZero j) (𝓝 (0 : E₂)) (𝓝 (insertZero j 0)) :=
      (insertZero_holomorphic j).continuous.continuousAt
    simpa only [insertZero_zero] using ht
  · exact Eventually.of_forall (insertZero_mem_planeUnion hj)

/-- Vanishing on the singular set germ is exactly simultaneous vanishing
of all actual coordinate-branch pullback germs. -/
theorem eventually_zero_on_union_iff (s : Finset (Fin 3)) (f : E₃ → ℂ) :
    f =ᶠ[𝓝[planeUnion s] (0 : E₃)] 0 ↔
      ∀ j ∈ s, (f ∘ insertZero j) =ᶠ[𝓝 (0 : E₂)] 0 := by
  constructor
  · intro hf j hj
    exact hf.comp_tendsto (insertZero_tendsto_planeUnion hj)
  · intro hf
    have hlocal (j : s) :
        ∀ᶠ z in 𝓝 (0 : E₃), f (insertZero j (removeCoordinate j z)) = 0 := by
      have ht : Tendsto (removeCoordinate j) (𝓝 (0 : E₃)) (𝓝 (0 : E₂)) :=
        (removeCoordinate_holomorphic j).continuous.continuousAt
      exact (hf j j.property).comp_tendsto ht
    have hall : ∀ᶠ z in 𝓝 (0 : E₃), ∀ j : s,
        f (insertZero j (removeCoordinate j z)) = 0 :=
      eventually_all.mpr hlocal
    filter_upwards [hall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hs
    obtain ⟨j, hj, hzj⟩ := hs
    change f z = 0
    simpa only [insertZero_removeCoordinate j z hzj] using hz ⟨j, hj⟩

/-- Equality of actual restricted function germs can likewise be checked
branch by branch. -/
theorem eventually_eq_on_union_iff (s : Finset (Fin 3)) (f g : E₃ → ℂ) :
    f =ᶠ[𝓝[planeUnion s] (0 : E₃)] g ↔
      ∀ j ∈ s, (f ∘ insertZero j) =ᶠ[𝓝 (0 : E₂)] (g ∘ insertZero j) := by
  simpa only [EventuallyEq, Pi.sub_apply, Pi.zero_apply, Function.comp_apply,
    sub_eq_zero] using eventually_zero_on_union_iff s (f - g)

theorem time_eq_product (z : E₃) : Triangle.time z = ∏ j : Fin 3, z j := by
  simp [Triangle.time, Fin.prod_univ_succ, mul_assoc]

/-- The active branches at an actual central point. -/
def activeBranches (a : E₃) : Finset (Fin 3) :=
  Finset.univ.filter fun j => a j = 0

@[simp] theorem mem_activeBranches (a : E₃) (j : Fin 3) :
    j ∈ activeBranches a ↔ a j = 0 := by simp [activeBranches]

theorem activeBranches_nonempty_iff (a : E₃) :
    (activeBranches a).Nonempty ↔ Triangle.time a = 0 := by
  rw [time_eq_product, Finset.prod_eq_zero_iff]
  simp only [Finset.Nonempty, mem_activeBranches, Finset.mem_univ, true_and]

theorem activeBranches_card (a : E₃) (ha : Triangle.time a = 0) :
    (activeBranches a).card = 1 ∨ (activeBranches a).card = 2 ∨
      (activeBranches a).card = 3 := by
  have hp := Finset.card_pos.mpr ((activeBranches_nonempty_iff a).mpr ha)
  have hb : (activeBranches a).card ≤ 3 := by
    simpa using Finset.card_le_card (Finset.subset_univ (activeBranches a))
  omega

/-- After centering at `a`, the inactive coordinate factors are units on
an actual neighbourhood, so precisely the active planes remain. -/
theorem translatedCentral_eventually_eq_planes (a : E₃) :
    {z : E₃ | Triangle.time (a + z) = 0} =ᶠ[𝓝 (0 : E₃)] planeUnion (activeBranches a) := by
  have hn (j : Fin 3) : ∀ᶠ z in 𝓝 (0 : E₃), a j = 0 ∨ a j + z j ≠ 0 := by
    by_cases hj : a j = 0
    · exact Eventually.of_forall fun _ => Or.inl hj
    · have hc : ContinuousAt (fun z : E₃ => a j + z j) 0 :=
        continuous_const.continuousAt.add (continuous_apply j).continuousAt
      have he : a j + (0 : E₃) j ≠ 0 := by simpa using hj
      exact (hc.eventually_ne he).mono fun _ h => Or.inr h
  have hall : ∀ᶠ z in 𝓝 (0 : E₃), ∀ j : Fin 3, a j = 0 ∨ a j + z j ≠ 0 :=
    eventually_all.mpr hn
  filter_upwards [hall] with z hz
  apply propext
  change Triangle.time (a + z) = 0 ↔ ∃ j ∈ activeBranches a, z j = 0
  rw [time_eq_product, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, _, hj⟩
    have haj : a j = 0 := (hz j).resolve_right (fun h => h hj)
    exact ⟨j, (mem_activeBranches a j).mpr haj,
      by simpa only [Pi.add_apply, haj, zero_add] using hj⟩
  · rintro ⟨j, hj, hzj⟩
    exact ⟨j, Finset.mem_univ _,
      by simp only [Pi.add_apply, (mem_activeBranches a j).mp hj, hzj, add_zero]⟩

theorem nhdsWithin_translatedCentral (a : E₃) :
    𝓝[{z : E₃ | Triangle.time (a + z) = 0}] (0 : E₃) =
      𝓝[planeUnion (activeBranches a)] (0 : E₃) :=
  nhdsWithin_eq_iff_eventuallyEq.mpr (translatedCentral_eventually_eq_planes a)

end Wikipedia.HopfProblem.CuspNormalization.Germs
