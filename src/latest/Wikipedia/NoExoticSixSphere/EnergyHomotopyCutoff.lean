import Wikipedia.NoExoticSixSphere.RealIntervalProgress
import Mathlib.Topology.Homotopy.Basic

/-!
# Cutting off an energy-nonincreasing homotopy

The time cutoff fixes a lower sublevel. Above a second, larger threshold it
uses the full original homotopy. If the original endpoint lies below that
second threshold, so does the cutoff endpoint.
-/

open Set unitInterval

namespace NoExoticSixSphere.EnergyHomotopyCutoff

open RealIntervalProgress

variable {X : Type*} [TopologicalSpace X]

noncomputable def time (e : C(X, ℝ)) (l k : ℝ) (p : I × X) : I :=
  ⟨(p.1 : ℝ) * progress l k (e p.2), unitInterval.mul_mem p.1.2
    (projIcc (0 : ℝ) 1 zero_le_one ((e p.2 - l) / (k - l))).2⟩

theorem continuous_time (e : C(X, ℝ)) (l k : ℝ) : Continuous (time e l k) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    ((continuous_progress l k).comp (e.continuous.comp continuous_snd))).subtype_mk _

theorem time_zero (e : C(X, ℝ)) (l k : ℝ) (x : X) : time e l k (0, x) = 0 := by
  apply Subtype.ext
  simp [time]

theorem time_low (e : C(X, ℝ)) (l k : ℝ) (hlk : l ≤ k) {x : X} (hx : e x ≤ l)
    (s : I) : time e l k (s, x) = 0 := by
  apply Subtype.ext
  simp [time, progress_before hlk hx]

theorem time_one_high (e : C(X, ℝ)) (l k : ℝ) (hlk : l < k) {x : X} (hx : k ≤ e x) :
    time e l k (1, x) = 1 := by
  apply Subtype.ext
  simp [time, progress_after hlk hx]

variable {g : C(X, X)} (H : ContinuousMap.Homotopy (ContinuousMap.id X) g)

noncomputable def map (e : C(X, ℝ)) (l k : ℝ) : C(I × X, X) :=
  H.toContinuousMap.comp
    ⟨fun p ↦ (time e l k p, p.2), (continuous_time e l k).prodMk continuous_snd⟩

noncomputable def endpoint (e : C(X, ℝ)) (l k : ℝ) : C(X, X) :=
  (map H e l k).comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

noncomputable def homotopy (e : C(X, ℝ)) (l k : ℝ) (hlk : l ≤ k) :
    ContinuousMap.HomotopyRel (ContinuousMap.id X) (endpoint H e l k) {x | e x ≤ l} where
  toContinuousMap := map H e l k
  map_zero_left x := by
    change H (time e l k (0, x), x) = x
    rw [time_zero, H.apply_zero]
    rfl
  map_one_left _ := rfl
  prop' s x hx := by
    change H (time e l k (s, x), x) = x
    rw [time_low e l k hlk hx, H.apply_zero]
    rfl

theorem energy_le (e : C(X, ℝ)) (l k : ℝ)
    (henergy : ∀ s x, e (H (s, x)) ≤ e x) (s : I) (x : X) :
    e (map H e l k (s, x)) ≤ e x := henergy _ _

theorem endpoint_lt (e : C(X, ℝ)) (l k : ℝ) (hlk : l < k)
    (henergy : ∀ s x, e (H (s, x)) ≤ e x) {x : X} (hx : e (g x) < k) :
    e (endpoint H e l k x) < k := by
  by_cases hlow : e x < k
  · exact (energy_le H e l k henergy 1 x).trans_lt hlow
  · change e (H (time e l k (1, x), x)) < k
    rw [time_one_high e l k hlk (le_of_not_gt hlow), H.apply_one]
    exact hx

end NoExoticSixSphere.EnergyHomotopyCutoff
