import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# An overlapping reversed circle arc contains a fixed point

The orientation condition is stated concretely: on an interval, the image
parameters have a continuous strictly decreasing real lift.  An overlap of
the two open arc images gives an integer shift at one pair of parameters;
the intermediate value theorem then gives a fixed point in the open arc.
-/

open Set

namespace Puzzling139335.CentralRotation

private theorem decreasing_lift_fixed_shift {a b s t r : ℝ} {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) (hanti : StrictAntiOn φ (Icc a b))
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (heq : φ t = s + r) :
    ∃ u ∈ Ioo a b, φ u = u + r := by
  have hab : a ≤ b := hs.1.le.trans hs.2.le
  have hat : φ t < φ a := hanti (left_mem_Icc.mpr hab) (Ioo_subset_Icc_self ht) ht.1
  have htb : φ b < φ t := hanti (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hab) ht.2
  have hbounds : r ∈ Ioo (φ b - b) (φ a - a) := by
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨u, hu, he⟩ := intermediate_value_Ioo' hab (hφ.sub continuousOn_id) hbounds
  change φ u - u = r at he
  exact ⟨u, hu, by linarith⟩

/-- Equality of two real circle parameters is equality up to an integer. -/
theorem circle_eq_iff_exists_int {x y : ℝ} :
    (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) ↔
      ∃ n : ℤ, x = y + n := by
  constructor
  · intro h
    have hz : ((x - y : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  · rintro ⟨n, rfl⟩
    have hn : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩
    rw [AddCircle.coe_add, hn, add_zero]

/-- A continuous decreasing lift cannot represent the identity on a
nondegenerate interval.  Otherwise its displacement would be both strictly
decreasing and integer-valued. -/
theorem decreasing_lift_not_identity {a b : ℝ} {φ : ℝ → ℝ} (hab : a < b)
    (hφ : ContinuousOn φ (Icc a b)) (hanti : StrictAntiOn φ (Icc a b)) :
    ¬ (∀ t ∈ Icc a b, (φ t : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))) := by
  intro hall
  obtain ⟨na, hna⟩ := circle_eq_iff_exists_int.mp (hall a (left_mem_Icc.mpr hab.le))
  obtain ⟨nb, hnb⟩ := circle_eq_iff_exists_int.mp (hall b (right_mem_Icc.mpr hab.le))
  have hφab := hanti (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have hnlt : (nb : ℝ) < na := by linarith
  have hnlt' : nb < na := by exact_mod_cast hnlt
  have hnle' : nb + 1 ≤ na := by omega
  have hnle : (nb : ℝ) + 1 ≤ na := by exact_mod_cast hnle'
  have hmid : (nb : ℝ) + 1 / 2 ∈ Ioo (φ b - b) (φ a - a) := by
    constructor <;> linarith
  obtain ⟨u, hu, he⟩ := intermediate_value_Ioo' hab.le (hφ.sub continuousOn_id) hmid
  change φ u - u = (nb : ℝ) + 1 / 2 at he
  obtain ⟨nu, hnu⟩ := circle_eq_iff_exists_int.mp (hall u (Ioo_subset_Icc_self hu))
  have hlo : (nb : ℝ) < nu := by linarith
  have hhi : (nu : ℝ) < (nb : ℝ) + 1 := by linarith
  have hlo' : nb < nu := by exact_mod_cast hlo
  have hhi' : nu < nb + 1 := by exact_mod_cast hhi
  omega

/-- A decreasing lift of an arc map, together with overlap of the source and
target open arc images, forces an actual fixed point in that open arc. -/
theorem exists_fixedPoint_of_decreasing_lift {X : Type*} {a b : ℝ}
    {f : AddCircle (1 : ℝ) → X} (hinj : Function.Injective f)
    {k : X → X} {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) (hanti : StrictAntiOn φ (Icc a b))
    (hagrees : ∀ t ∈ Icc a b, k (f (t : AddCircle (1 : ℝ))) =
      f (φ t : AddCircle (1 : ℝ)))
    (hoverlap : (k '' ((fun t : ℝ => f (t : AddCircle (1 : ℝ))) '' Ioo a b) ∩
      ((fun t : ℝ => f (t : AddCircle (1 : ℝ))) '' Ioo a b)).Nonempty) :
    ∃ u ∈ Ioo a b, k (f (u : AddCircle (1 : ℝ))) = f (u : AddCircle (1 : ℝ)) := by
  obtain ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, s, hs, hst⟩ := hoverlap
  have hcircle : (φ t : AddCircle (1 : ℝ)) = (s : AddCircle (1 : ℝ)) :=
    hinj ((hagrees t (Ioo_subset_Icc_self ht)).symm.trans hst.symm)
  obtain ⟨n, hn⟩ := circle_eq_iff_exists_int.mp hcircle
  obtain ⟨u, hu, hfix⟩ := decreasing_lift_fixed_shift hφ hanti hs ht hn
  refine ⟨u, hu, ?_⟩
  rw [hagrees u (Ioo_subset_Icc_self hu)]
  exact congrArg f (circle_eq_iff_exists_int.mpr ⟨n, hfix⟩)

end Puzzling139335.CentralRotation
