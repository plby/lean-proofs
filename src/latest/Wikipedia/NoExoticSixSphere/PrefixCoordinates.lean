import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuous prefix straightening in linear coordinates

At stage `s`, the initial prefix is replaced by the radial segment to its
value at `s`, while the tail is unchanged. The formula uses `max s t`.
Although its scalar coefficient is not continuous at `(0,0)`, it is bounded
by one and multiplies a coordinate map vanishing there; the product is
jointly continuous, including for arbitrary parameter spaces.
-/

open unitInterval

namespace NoExoticSixSphere.PrefixCoordinates

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

def endingTime (s t : I) : I :=
  ⟨max (s : ℝ) (t : ℝ), (le_max_left _ _).trans' s.2.1, max_le s.2.2 t.2.2⟩

noncomputable def coefficient (s t : I) : ℝ := (t : ℝ) / max (s : ℝ) (t : ℝ)

theorem coefficient_norm_le (s t : I) : ‖coefficient s t‖ ≤ 1 := by
  have hm : 0 ≤ max (s : ℝ) (t : ℝ) := s.2.1.trans (le_max_left _ _)
  have hc : 0 ≤ coefficient s t := div_nonneg t.2.1 hm
  rw [Real.norm_eq_abs, abs_of_nonneg hc]
  by_cases hz : max (s : ℝ) (t : ℝ) = 0
  · simp [coefficient, hz]
  · apply (div_le_iff₀ (lt_of_le_of_ne hm (Ne.symm hz))).mpr
    simpa only [one_mul] using le_max_right (s : ℝ) (t : ℝ)

theorem continuous_endingTime : Continuous (fun p : I × I ↦ endingTime p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_fst).max
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

noncomputable def straightening (L : C(I × X, E)) (hzero : ∀ x, L (0, x) = 0) :
    C(I × (I × X), E) where
  toFun q := coefficient q.1 q.2.1 • L (endingTime q.1 q.2.1, q.2.2)
  continuous_toFun := by
    have hs : Continuous (fun q : I × (I × X) ↦ (q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous (fun q : I × (I × X) ↦ (q.2.1 : ℝ)) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have hm : Continuous (fun q : I × (I × X) ↦ max (q.1 : ℝ) (q.2.1 : ℝ)) := hs.max ht
    have he : Continuous (fun q : I × (I × X) ↦ endingTime q.1 q.2.1) :=
      continuous_endingTime.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hL : Continuous (fun q : I × (I × X) ↦ L (endingTime q.1 q.2.1, q.2.2)) :=
      L.continuous.comp (he.prodMk (continuous_snd.comp continuous_snd))
    apply continuous_iff_continuousAt.mpr
    intro q
    by_cases hz : max (q.1 : ℝ) (q.2.1 : ℝ) = 0
    · have heq : endingTime q.1 q.2.1 = 0 := Subtype.ext hz
      have hLq : L (endingTime q.1 q.2.1, q.2.2) = 0 := by rw [heq, hzero]
      have hlim : Filter.Tendsto
          (fun p : I × (I × X) ↦ L (endingTime p.1 p.2.1, p.2.2)) (nhds q) (nhds 0) := by
        simpa only [hLq] using hL.tendsto q
      have hb : Filter.IsBoundedUnder (· ≤ ·) (nhds q)
          (fun p : I × (I × X) ↦ ‖coefficient p.1 p.2.1‖) :=
        Filter.isBoundedUnder_of ⟨1, fun p ↦ coefficient_norm_le p.1 p.2.1⟩
      change Filter.Tendsto _ (nhds q)
        (nhds (coefficient q.1 q.2.1 • L (endingTime q.1 q.2.1, q.2.2)))
      rw [hLq, smul_zero]
      exact hb.smul_tendsto_zero hlim
    · exact (ht.continuousAt.div hm.continuousAt hz).smul hL.continuousAt

theorem straightening_prefix (L : C(I × X, E)) (hzero : ∀ x, L (0, x) = 0)
    (s t : I) (x : X) (ht : t ≤ s) :
    straightening L hzero (s, (t, x)) = ((t : ℝ) / (s : ℝ)) • L (s, x) := by
  have he : endingTime s t = s := Subtype.ext (max_eq_left ht)
  change coefficient s t • L (endingTime s t, x) = _
  rw [coefficient, max_eq_left (show (t : ℝ) ≤ (s : ℝ) from ht), he]

theorem straightening_tail (L : C(I × X, E)) (hzero : ∀ x, L (0, x) = 0)
    (s t : I) (x : X) (ht : s ≤ t) : straightening L hzero (s, (t, x)) = L (t, x) := by
  have he : endingTime s t = t := Subtype.ext (max_eq_right ht)
  change coefficient s t • L (endingTime s t, x) = _
  rw [coefficient, max_eq_right (show (s : ℝ) ≤ (t : ℝ) from ht), he]
  by_cases hz : (t : ℝ) = 0
  · have ht0 : t = 0 := Subtype.ext hz
    rw [ht0, hzero, smul_zero]
  · rw [div_self hz, one_smul]

theorem straightening_zero (L : C(I × X, E)) (hzero : ∀ x, L (0, x) = 0)
    (t : I) (x : X) : straightening L hzero (0, (t, x)) = L (t, x) :=
  straightening_tail L hzero 0 t x t.2.1

theorem straightening_one (L : C(I × X, E)) (hzero : ∀ x, L (0, x) = 0)
    (t : I) (x : X) : straightening L hzero (1, (t, x)) = (t : ℝ) • L (1, x) := by
  rw [straightening_prefix L hzero 1 t x t.2.2]
  change ((t : ℝ) / 1) • L (1, x) = _
  rw [div_one]

end NoExoticSixSphere.PrefixCoordinates
