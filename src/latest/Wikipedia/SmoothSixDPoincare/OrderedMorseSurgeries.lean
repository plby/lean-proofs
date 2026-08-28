import Wikipedia.SmoothSixDPoincare.MorseSurgeryWindows
import Mathlib.Data.Finset.Sort

/-!
# The finite surgery sequence in increasing critical-value order

The ordering is constructed from the original function values. Every
critical point occurs exactly once, and consecutive indices have genuine
regular-band bridges between their already constructed surgery windows.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

variable (S : SurgeryWindows E f)

/-- The finite set of actual critical values. -/
def values : Finset ℝ := (S.finite.image f).toFinset

/-- The number of surgeries in the sequence. -/
def count : ℕ := S.values.card

/-- Enumerate every original critical point in increasing critical-value order. -/
def point : Fin S.count ≃ criticalPoints E f :=
  ((S.values.orderIsoOfFin rfl).toEquiv.trans
    (Equiv.setCongr (S.finite.image f).coe_toFinset)).trans
      (Equiv.Set.imageOfInjOn f (criticalPoints E f) S.distinct).symm

theorem point_value (i : Fin S.count) :
    f (S.point i) = S.values.orderEmbOfFin rfl i := by
  let e := Equiv.Set.imageOfInjOn f (criticalPoints E f) S.distinct
  let v : f '' criticalPoints E f :=
    Equiv.setCongr (S.finite.image f).coe_toFinset (S.values.orderIsoOfFin rfl i)
  have h := congrArg (fun x : f '' criticalPoints E f => (x : ℝ)) (e.apply_symm_apply v)
  exact h

theorem point_strictMono : StrictMono (fun i : Fin S.count => f (S.point i)) := by
  intro i j hij
  change f (S.point i) < f (S.point j)
  rw [S.point_value, S.point_value]
  exact (S.values.orderEmbOfFin rfl).strictMono hij

theorem point_consecutive (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ r : criticalPoints E f, ¬(f (S.point i) < f r ∧ f r < f (S.point j)) := by
  intro r hr
  obtain ⟨k, rfl⟩ := S.point.surjective r
  have hik : i < k := S.point_strictMono.lt_iff_lt.mp hr.1
  have hkj : k < j := S.point_strictMono.lt_iff_lt.mp hr.2
  have hik' : i.val < k.val := hik
  have hkj' : k.val < j.val := hkj
  omega

theorem ordered_windows (i j : Fin S.count) (hij : i < j) :
    S.upper (S.point i) < S.lower (S.point j) :=
  S.upper_lt_lower _ _ (S.point_strictMono hij)

theorem consecutive_regular (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ x, f x ∈ Icc (S.upper (S.point i)) (S.lower (S.point j)) →
      x ∉ criticalPoints E f :=
  S.regular_between _ _ (S.point_consecutive i j hij)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- The finite ordered sequence has actual compatible ambient and level bridges. -/
theorem exists_consecutiveBandBridge
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    letI := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data (S.point i)).UpperLevel (S.data (S.point j)).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper (S.point i)} =
          {x : M | f x ≤ S.lower (S.point j)} ∧
        ∀ x : (S.data (S.point i)).UpperLevel, (b x : M) = D x := by
  have hlt : i < j := by change i.val < j.val; omega
  exact S.exists_bandBridge hf _ _ (S.point_strictMono hlt) (S.point_consecutive i j hij)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
