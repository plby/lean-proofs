import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.HopfProblem.SphereHomologySuspension

/-!
# Suspension of maps between the actual Euclidean spheres

The construction uses the genuine cylinder quotient and the proved latitude
homeomorphisms. On every latitude it preserves height and applies the original
map to the sphere coordinate. Its fiber over an equatorial value is exactly
the equatorial copy of the original fiber.

This is not a stability theorem: no inverse to suspension on homotopy classes
is asserted here.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.SphereMapSuspension

open Wikipedia.HopfProblem.CuspCentralHomology
  Wikipedia.HopfProblem.SphereHomology

variable {m n : ℕ}

def quotientMap (f : C(Sphere m, Sphere n)) : C(Suspension (Sphere m), Suspension (Sphere n)) where
  toFun := Quotient.map (fun p : unitInterval × Sphere m ↦ (p.1, f p.2)) (by
    rintro p q ⟨ht, h0 | h1 | hxy⟩
    · exact ⟨ht, Or.inl h0⟩
    · exact ⟨ht, Or.inr (Or.inl h1)⟩
    · exact ⟨ht, Or.inr (Or.inr (congrArg f hxy))⟩)
  continuous_toFun := by
    apply Suspension.isQuotientMap_mk.continuous_iff.mpr
    exact Suspension.continuous_mk.comp (continuous_fst.prodMk
      (f.continuous.comp continuous_snd))

@[simp] theorem quotientMap_mk (f : C(Sphere m, Sphere n))
    (t : unitInterval) (x : Sphere m) :
    quotientMap f (Suspension.mk t x) = Suspension.mk t (f x) := rfl

/-- Suspension on the literal Euclidean unit spheres, with their existing topology. -/
def map (f : C(Sphere m, Sphere n)) : C(Sphere (m + 1), Sphere (n + 1)) :=
  (suspensionSphereHomeomorph n : C(_, _)).comp
    ((quotientMap f).comp ((suspensionSphereHomeomorph m).symm : C(_, _)))

@[simp] theorem map_point (f : C(Sphere m, Sphere n)) (t : unitInterval) (x : Sphere m) :
    map f (Latitude.point m t x) = Latitude.point n t (f x) := by
  change suspensionSphereHomeomorph n
    (quotientMap f ((suspensionSphereHomeomorph m).symm (Latitude.point m t x))) = _
  rw [← suspensionSphereHomeomorph_mk, Homeomorph.symm_apply_apply, quotientMap_mk,
    suspensionSphereHomeomorph_mk]

@[simp] theorem map_head (f : C(Sphere m, Sphere n)) (y : Sphere (m + 1)) :
    (map f y).val 0 = y.val 0 := by
  obtain ⟨⟨t, x⟩, rfl⟩ := Latitude.point_surjective m y
  rw [map_point]
  rfl

def middle : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem middle_ne_zero : middle ≠ 0 := by
  intro h
  have := congrArg (fun t : unitInterval ↦ (t : ℝ)) h
  norm_num [middle] at this

@[simp] theorem middle_ne_one : middle ≠ 1 := by
  intro h
  have := congrArg (fun t : unitInterval ↦ (t : ℝ)) h
  norm_num [middle] at this

/-- The actual equatorial inclusion, with a zero first coordinate. -/
def equator (n : ℕ) : C(Sphere n, Sphere (n + 1)) :=
  ⟨Latitude.point n middle,
    (Latitude.point_continuous n).comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem equator_head (x : Sphere n) : (equator n x).val 0 = 0 := by
  change Latitude.height middle = 0
  norm_num [Latitude.height, middle]

@[simp] theorem equator_tail (x : Sphere n) (i : Fin (n + 1)) :
    (equator n x).val i.succ = x.val i := by
  change Latitude.radius middle * x.val i = x.val i
  norm_num [Latitude.radius, Latitude.height, middle]

theorem equator_injective (n : ℕ) : Function.Injective (equator n) := by
  intro x y h
  ext i
  have hi := congrArg (fun z : Sphere (n + 1) ↦ z.val i.succ) h
  simpa only [equator_tail] using hi

@[simp] theorem map_equator (f : C(Sphere m, Sphere n)) (x : Sphere m) :
    map f (equator m x) = equator n (f x) := map_point f middle x

/-- No extra components appear in the distinguished fiber under suspension. -/
theorem map_eq_equator_iff (f : C(Sphere m, Sphere n)) (y : Sphere (m + 1)) (b : Sphere n) :
    map f y = equator n b ↔ ∃ x : Sphere m, y = equator m x ∧ f x = b := by
  obtain ⟨⟨t, x⟩, rfl⟩ := Latitude.point_surjective m y
  constructor
  · intro h
    rw [map_point] at h
    obtain ⟨ht, h0 | h1 | hxb⟩ := (Latitude.point_eq_iff n t middle (f x) b).mp h
    · exact (middle_ne_zero (ht.symm.trans h0)).elim
    · exact (middle_ne_one (ht.symm.trans h1)).elim
    · exact ⟨x, congrArg (fun s ↦ Latitude.point m s x) ht, hxb⟩
  · rintro ⟨z, hz, hzb⟩
    rw [hz, map_equator, hzb]

@[simp] theorem map_id (n : ℕ) : map (ContinuousMap.id (Sphere n)) = ContinuousMap.id _ := by
  ext y
  obtain ⟨⟨t, x⟩, rfl⟩ := Latitude.point_surjective n y
  rw [map_point]
  rfl

theorem map_comp {k : ℕ} (f : C(Sphere m, Sphere n)) (g : C(Sphere n, Sphere k)) :
    map (g.comp f) = (map g).comp (map f) := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨⟨t, x⟩, rfl⟩ := Latitude.point_surjective m y
  change map (g.comp f) (Latitude.point m t x) =
    map g (map f (Latitude.point m t x))
  rw [map_point, map_point, map_point]
  rfl

end NoExoticSixSphere.SphereMapSuspension
