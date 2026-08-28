import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderRetiming
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderClocks

/-!
# Deforming the two actual open-cover pieces toward their end spaces

The decreasing clock keeps the lower open piece invariant and ends in
the right-space image. The reflected clock keeps the upper piece
invariant and ends in the left-space image. Both families start at the
identity and fix both original end spaces throughout.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)

def lowerMotion : C(I × space e f, space e f) :=
  retimeFamily e f Clock.lowerClock Clock.lowerClock_zero Clock.lowerClock_one

def upperMotion : C(I × space e f, space e f) :=
  retimeFamily e f Clock.upperClock Clock.upperClock_zero Clock.upperClock_one

theorem lowerMotion_initial (p : space e f) : lowerMotion e f (0, p) = p :=
  retimeFamily_initial e f Clock.lowerClock Clock.lowerClock_zero Clock.lowerClock_one
    Clock.lowerClock_initial p

theorem upperMotion_initial (p : space e f) : upperMotion e f (0, p) = p :=
  retimeFamily_initial e f Clock.upperClock Clock.upperClock_zero Clock.upperClock_one
    Clock.upperClock_initial p

theorem lowerMotion_right (s : I) (y : Y) : lowerMotion e f (s, right e f y) = right e f y :=
  retimeFamily_right e f Clock.lowerClock Clock.lowerClock_zero Clock.lowerClock_one s y

theorem upperMotion_left (s : I) (x : X) : upperMotion e f (s, left e f x) = left e f x :=
  retimeFamily_left e f Clock.upperClock Clock.upperClock_zero Clock.upperClock_one s x

theorem lowerMotion_tube (s t : I) (a : A) :
    lowerMotion e f (s, tube e f (t, a)) = tube e f (Clock.lowerClock (s, t), a) :=
  retimeFamily_tube e f Clock.lowerClock Clock.lowerClock_zero Clock.lowerClock_one s t a

theorem upperMotion_tube (s t : I) (a : A) :
    upperMotion e f (s, tube e f (t, a)) = tube e f (Clock.upperClock (s, t), a) :=
  retimeFamily_tube e f Clock.upperClock Clock.upperClock_zero Clock.upperClock_one s t a

theorem lowerMotion_mem (s : I) (p : lower e f) : lowerMotion e f (s, p.val) ∈ lower e f := by
  change (height e f (retimeFamily e f Clock.lowerClock _ _ (s, p.val)) : ℝ) < 2 / 3
  rw [height_retimeFamily]
  exact lt_of_le_of_lt (Clock.lowerClock_le s (height e f p.val)) p.property

theorem upperMotion_mem (s : I) (p : upper e f) : upperMotion e f (s, p.val) ∈ upper e f := by
  change (1 : ℝ) / 3 < height e f (retimeFamily e f Clock.upperClock _ _ (s, p.val))
  rw [height_retimeFamily]
  exact lt_of_lt_of_le p.property (Clock.le_upperClock s (height e f p.val))

theorem lowerMotion_terminal (p : lower e f) :
    lowerMotion e f (1, p.val) ∈ Set.range (right e f) := by
  rcases jointly_surjective e f p.val with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨t, a, ht⟩
  · exact ((left_notMem_lower e f x) (hx ▸ p.property)).elim
  · rw [← hy, lowerMotion_right]
    exact Set.mem_range_self y
  · have htime : (t : ℝ) < 2 / 3 := by
      have hp := p.property
      change (height e f p.val : ℝ) < 2 / 3 at hp
      rw [← ht, height_tube] at hp
      exact hp
    rw [← ht, lowerMotion_tube, Clock.lowerClock_terminal_zero t htime.le, tube_zero]
    exact Set.mem_range_self (f a)

theorem upperMotion_terminal (p : upper e f) :
    upperMotion e f (1, p.val) ∈ Set.range (left e f) := by
  rcases jointly_surjective e f p.val with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨t, a, ht⟩
  · rw [← hx, upperMotion_left]
    exact Set.mem_range_self x
  · exact ((right_notMem_upper e f y) (hy ▸ p.property)).elim
  · have htime : (1 : ℝ) / 3 < t := by
      have hp := p.property
      change (1 : ℝ) / 3 < height e f p.val at hp
      rw [← ht, height_tube] at hp
      exact hp
    rw [← ht, upperMotion_tube, Clock.upperClock_terminal_one t htime.le, tube_one]
    exact Set.mem_range_self (e a)

def lowerDeformation : C(I × lower e f, lower e f) :=
  ⟨fun p ↦ ⟨lowerMotion e f (p.1, p.2.val), lowerMotion_mem e f p.1 p.2⟩,
    ((lowerMotion e f).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

def upperDeformation : C(I × upper e f, upper e f) :=
  ⟨fun p ↦ ⟨upperMotion e f (p.1, p.2.val), upperMotion_mem e f p.1 p.2⟩,
    ((upperMotion e f).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

end NoExoticSixSphere.DoubleMappingCylinder
