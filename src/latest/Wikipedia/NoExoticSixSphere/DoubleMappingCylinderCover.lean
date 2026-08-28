import Wikipedia.NoExoticSixSphere.DoubleMappingCylinder

/-!
# A genuine open cover of the actual double mapping cylinder

The globally defined height is one on the left space, zero on the
right space, and the original time coordinate on the connecting
cylinder. Its overlapping open sublevels give a real open cover.
Every overlap point has an interior cylinder representative.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)

def liftedTubeHeight : C(I × A, ULift.{u} I) :=
  ⟨fun p ↦ ULift.up p.1, continuous_uliftUp.comp continuous_fst⟩

def liftedHeight : space e f ⟶ TopCat.of (ULift.{u} I) :=
  glue e f (Z := TopCat.of (ULift.{u} I))
    (ContinuousMap.const Y (ULift.up 0)) (liftedTubeHeight (A := A))
    (fun _ ↦ rfl) (ContinuousMap.const X (ULift.up 1)) (fun _ ↦ rfl)

def height : C(space e f, I) :=
  ⟨fun p ↦ (liftedHeight e f p).down, continuous_uliftDown.comp (liftedHeight e f).hom.continuous⟩

theorem height_left (x : X) : height e f (left e f x) = 1 :=
  congrArg (fun m : X ⟶ TopCat.of (ULift.{u} I) ↦ (m x).down)
    (left_glue e f (Z := TopCat.of (ULift.{u} I))
      (ContinuousMap.const Y (ULift.up 0)) (liftedTubeHeight (A := A))
      (fun _ ↦ rfl) (ContinuousMap.const X (ULift.up 1)) (fun _ ↦ rfl))

theorem height_right (y : Y) : height e f (right e f y) = 0 :=
  congrArg (fun m : Y ⟶ TopCat.of (ULift.{u} I) ↦ (m y).down)
    (right_glue e f (Z := TopCat.of (ULift.{u} I))
      (ContinuousMap.const Y (ULift.up 0)) (liftedTubeHeight (A := A))
      (fun _ ↦ rfl) (ContinuousMap.const X (ULift.up 1)) (fun _ ↦ rfl))

theorem height_tube (t : I) (a : A) : height e f (tube e f (t, a)) = t :=
  congrArg (fun m : TopCat.of (I × A) ⟶ TopCat.of (ULift.{u} I) ↦ (m (t, a)).down)
    (tube_glue e f (Z := TopCat.of (ULift.{u} I))
      (ContinuousMap.const Y (ULift.up 0)) (liftedTubeHeight (A := A))
      (fun _ ↦ rfl) (ContinuousMap.const X (ULift.up 1)) (fun _ ↦ rfl))

def lower : Set (space e f) := {p | (height e f p : ℝ) < 2 / 3}

def upper : Set (space e f) := {p | (1 : ℝ) / 3 < height e f p}

theorem lower_isOpen : IsOpen (lower e f) :=
  isOpen_lt (continuous_subtype_val.comp (height e f).continuous) continuous_const

theorem upper_isOpen : IsOpen (upper e f) :=
  isOpen_lt continuous_const (continuous_subtype_val.comp (height e f).continuous)

theorem cover : lower e f ∪ upper e f = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  by_cases hp : (height e f p : ℝ) < 2 / 3
  · exact Or.inl hp
  · right
    change (1 : ℝ) / 3 < (height e f p : ℝ)
    linarith

theorem left_mem_upper (x : X) : left e f x ∈ upper e f := by
  change (1 : ℝ) / 3 < (height e f (left e f x) : ℝ)
  rw [height_left]
  norm_num

theorem left_notMem_lower (x : X) : left e f x ∉ lower e f := by
  change ¬(height e f (left e f x) : ℝ) < 2 / 3
  rw [height_left]
  norm_num

theorem right_mem_lower (y : Y) : right e f y ∈ lower e f := by
  change (height e f (right e f y) : ℝ) < 2 / 3
  rw [height_right]
  norm_num

theorem right_notMem_upper (y : Y) : right e f y ∉ upper e f := by
  change ¬(1 : ℝ) / 3 < (height e f (right e f y) : ℝ)
  rw [height_right]
  norm_num

theorem tube_mem_overlap_iff (t : I) (a : A) : tube e f (t, a) ∈ lower e f ∩ upper e f ↔
    (1 : ℝ) / 3 < t ∧ (t : ℝ) < 2 / 3 := by
  change ((height e f (tube e f (t, a)) : ℝ) < 2 / 3 ∧
    (1 : ℝ) / 3 < height e f (tube e f (t, a))) ↔ _
  rw [height_tube]
  exact and_comm

theorem overlap_representative (p : (lower e f ∩ upper e f : Set (space e f))) :
    ∃ t a, tube e f (t, a) = p.val ∧ (1 : ℝ) / 3 < t ∧ (t : ℝ) < 2 / 3 := by
  rcases jointly_surjective e f p.val with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨t, a, ht⟩
  · exact ((left_notMem_lower e f x) (hx ▸ p.property.1)).elim
  · exact ((right_notMem_upper e f y) (hy ▸ p.property.2)).elim
  · exact ⟨t, a, ht, (tube_mem_overlap_iff e f t a).mp (ht ▸ p.property)⟩

end NoExoticSixSphere.DoubleMappingCylinder
