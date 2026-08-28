import Wikipedia.NoExoticSixSphere.CollaredIntervalPush
import Wikipedia.NoExoticSixSphere.CylinderFiberSlab
import Mathlib.Topology.Piecewise

/-!
# A continuous endpoint-time function on the two actual slab collars

The two collar pieces are disjoint and clopen in their union. Selecting
the corresponding endpoint time is therefore continuous. Interpolation
toward that time stays in the same collar and preserves the original
cylinder map when its end neighborhoods are constant.
-/

noncomputable section

open Set TopologicalSpace
open scoped unitInterval

namespace NoExoticSixSphere.CylinderFiberSlab.BoundaryPush

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t a b : ℝ)

def domain : Opens (slab F z s t) := timeDomain F z s t
  ⟨Iio a ∪ Ioi b, isOpen_Iio.union isOpen_Ioi⟩

def time : C(domain F z s t a b, ℝ) where
  toFun p := p.val.val.val.1
  continuous_toFun := continuous_fst.comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))

theorem time_mem (p : domain F z s t a b) : time F z s t a b p < a ∨ b < time F z s t a b p :=
  p.property

variable (hab : a ≤ b)

include hab in
theorem left_isClopen : IsClopen {p : domain F z s t a b | time F z s t a b p < a} := by
  have he : {p : domain F z s t a b | ¬ time F z s t a b p < a} =
      {p | b < time F z s t a b p} := by
    ext p
    constructor
    · exact fun hp ↦ (time_mem F z s t a b p).resolve_left hp
    · intro hp hlt
      exact (not_lt_of_ge hab) (hp.trans hlt)
  have ho : IsOpen {p : domain F z s t a b | b < time F z s t a b p} :=
    isOpen_lt continuous_const (time F z s t a b).continuous
  have hc : IsClosed {p : domain F z s t a b | time F z s t a b p < a} := by
    apply isOpen_compl_iff.mp
    change IsOpen {p : domain F z s t a b | ¬ time F z s t a b p < a}
    rw [he]
    exact ho
  exact ⟨hc, isOpen_lt (time F z s t a b).continuous continuous_const⟩

def endpoint : C(domain F z s t a b, ℝ) where
  toFun p := if time F z s t a b p < a then s else t
  continuous_toFun := by
    apply Continuous.if ?_ continuous_const continuous_const
    intro p hp
    rw [(left_isClopen F z s t a b hab).frontier_eq] at hp
    exact hp.elim

theorem endpoint_left (p : domain F z s t a b) (hp : time F z s t a b p < a) :
    endpoint F z s t a b hab p = s := if_pos hp

theorem endpoint_right (p : domain F z s t a b) (hp : b < time F z s t a b p) :
    endpoint F z s t a b hab p = t :=
  if_neg (not_lt_of_ge (hab.trans hp.le))

def timeHomotopy : C(unitInterval × domain F z s t a b, ℝ) where
  toFun p := (1 - (p.1 : ℝ)) * time F z s t a b p.2 +
    (p.1 : ℝ) * endpoint F z s t a b hab p.2
  continuous_toFun :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((time F z s t a b).continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul
          ((endpoint F z s t a b hab).continuous.comp continuous_snd))

theorem timeHomotopy_zero (p : domain F z s t a b) :
    timeHomotopy F z s t a b hab (0, p) = time F z s t a b p := by
  change (1 - (0 : ℝ)) * _ + (0 : ℝ) * _ = _
  simp

theorem timeHomotopy_one (p : domain F z s t a b) :
    timeHomotopy F z s t a b hab (1, p) = endpoint F z s t a b hab p := by
  change (1 - (1 : ℝ)) * _ + (1 : ℝ) * _ = _
  simp

theorem timeHomotopy_left (hsa : s < a) (p : domain F z s t a b)
    (hp : time F z s t a b p < a) (u : unitInterval) :
    timeHomotopy F z s t a b hab (u, p) ∈ Ico s a := by
  change (1 - (u : ℝ)) * time F z s t a b p +
    (u : ℝ) * endpoint F z s t a b hab p ∈ Ico s a
  rw [endpoint_left F z s t a b hab p hp]
  exact (convex_Ico s a) ⟨p.val.property.1, hp⟩ ⟨le_rfl, hsa⟩
    (sub_nonneg.mpr u.property.2) u.property.1 (sub_add_cancel 1 (u : ℝ))

theorem timeHomotopy_right (hbt : b < t) (p : domain F z s t a b)
    (hp : b < time F z s t a b p) (u : unitInterval) :
    timeHomotopy F z s t a b hab (u, p) ∈ Ioc b t := by
  change (1 - (u : ℝ)) * time F z s t a b p +
    (u : ℝ) * endpoint F z s t a b hab p ∈ Ioc b t
  rw [endpoint_right F z s t a b hab p hp]
  exact (convex_Ioc b t) ⟨hp, p.val.property.2⟩ ⟨hbt, le_rfl⟩
    (sub_nonneg.mpr u.property.2) u.property.1 (sub_add_cancel 1 (u : ℝ))

theorem timeHomotopy_preserves (hsa : s < a) (hbt : b < t)
    (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
    (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))
    (p : domain F z s t a b) (u : unitInterval) :
    F (timeHomotopy F z s t a b hab (u, p), p.val.val.val.2) = z := by
  rcases time_mem F z s t a b p with hl | hr
  · have hh := timeHomotopy_left F z s t a b hab hsa p hl u
    exact (hleft _ ⟨hh.1, hh.2.le⟩ _).trans
      ((hleft _ ⟨p.val.property.1, hl.le⟩ _).symm.trans p.val.val.property)
  · have hh := timeHomotopy_right F z s t a b hab hbt p hr u
    exact (hright _ ⟨hh.1.le, hh.2⟩ _).trans
      ((hright _ ⟨hr.le, p.val.property.2⟩ _).symm.trans p.val.val.property)

theorem timeHomotopy_mem_interval (hsa : s < a) (hbt : b < t)
    (p : domain F z s t a b) (u : unitInterval) :
    timeHomotopy F z s t a b hab (u, p) ∈ Icc s t := by
  rcases time_mem F z s t a b p with hl | hr
  · have hh := timeHomotopy_left F z s t a b hab hsa p hl u
    exact ⟨hh.1, hh.2.le.trans (hab.trans hbt.le)⟩
  · have hh := timeHomotopy_right F z s t a b hab hbt p hr u
    exact ⟨hsa.le.trans (hab.trans hh.1.le), hh.2⟩

theorem timeHomotopy_mem_collar (hsa : s < a) (hbt : b < t)
    (p : domain F z s t a b) (u : unitInterval) :
    timeHomotopy F z s t a b hab (u, p) < a ∨
      b < timeHomotopy F z s t a b hab (u, p) := by
  rcases time_mem F z s t a b p with hl | hr
  · exact Or.inl (timeHomotopy_left F z s t a b hab hsa p hl u).2
  · exact Or.inr (timeHomotopy_right F z s t a b hab hbt p hr u).1

theorem endpoint_eq_end (p : domain F z s t a b) :
    endpoint F z s t a b hab p = s ∨ endpoint F z s t a b hab p = t := by
  rcases time_mem F z s t a b p with hl | hr
  · exact Or.inl (endpoint_left F z s t a b hab p hl)
  · exact Or.inr (endpoint_right F z s t a b hab p hr)

theorem endpoint_of_boundary (hsa : s < a) (hbt : b < t) (p : domain F z s t a b)
    (hp : time F z s t a b p = s ∨ time F z s t a b p = t) :
    endpoint F z s t a b hab p = time F z s t a b p := by
  rcases hp with hs | ht
  · exact (endpoint_left F z s t a b hab p (hs.trans_lt hsa)).trans hs.symm
  · exact (endpoint_right F z s t a b hab p (hbt.trans_eq ht.symm)).trans ht.symm

theorem timeHomotopy_fixed (hsa : s < a) (hbt : b < t) (p : domain F z s t a b)
    (hp : time F z s t a b p = s ∨ time F z s t a b p = t) (u : unitInterval) :
    timeHomotopy F z s t a b hab (u, p) = time F z s t a b p := by
  change (1 - (u : ℝ)) * time F z s t a b p +
    (u : ℝ) * endpoint F z s t a b hab p = time F z s t a b p
  rw [endpoint_of_boundary F z s t a b hab hsa hbt p hp]
  ring

end NoExoticSixSphere.CylinderFiberSlab.BoundaryPush
