import Wikipedia.HopfProblem.DegreeCollapseMooreWedgeHomotopy

/-!
# Straightening product homotopies in the native based path space

The fat-wedge neighborhood height supplies the duration at the two
ends. In the interior add the homotopy-time bump times distance from
the common pole. A zero duration then forces the native path to be
constant. Thus the original homotopy lifts continuously to Moore loops,
fixing the exact zero-duration identity. Straighten it there and normalize
back to the original native paths, without changing either endpoint map.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.PathWedgeHomotopy

open NoExoticSixSphere SphereMooreCommutator

def height (n : ℕ) (v : Parameter n) : ℝ :=
  (FatWedge.sphereData (spherePole n) 2).height v

theorem height_nonneg (n : ℕ) (v : Parameter n) : 0 ≤ height n v :=
  ((FatWedge.sphereData (spherePole n) 2).height v).property.1

theorem height_continuous (n : ℕ) : Continuous (height n) :=
  continuous_subtype_val.comp (FatWedge.sphereData (spherePole n) 2).height.continuous

theorem height_zero_iff (n : ℕ) (v : Parameter n) : height n v = 0 ↔ v ∈ Boundary n := by
  change ((FatWedge.sphereData (spherePole n) 2).height v : ℝ) = (0 : I) ↔ _
  rw [Subtype.coe_inj, (FatWedge.sphereData (spherePole n) 2).zero_iff]
  exact SubspaceCofibration.mem_range _ v

def duration (n : ℕ) (u : I × Parameter n) : ℝ :=
  height n u.2 + (u.1 : ℝ) * (1 - (u.1 : ℝ)) * dist u.2 (point n)

theorem duration_nonneg (n : ℕ) (u : I × Parameter n) : 0 ≤ duration n u :=
  add_nonneg (height_nonneg n u.2)
    (mul_nonneg (mul_nonneg u.1.property.1 (sub_nonneg.mpr u.1.property.2)) dist_nonneg)

theorem duration_continuous (n : ℕ) : Continuous (duration n) := by
  have ht : Continuous (fun u : I × Parameter n ↦ (u.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact (height_continuous n |>.comp continuous_snd).add
    ((ht.mul (continuous_const.sub ht)).mul (continuous_snd.dist continuous_const))

theorem duration_zero (n : ℕ) (v : Parameter n) : duration n (0, v) = height n v := by
  change height n v + (0 : ℝ) * (1 - 0) * dist v (point n) = _
  rw [zero_mul, zero_mul, add_zero]

theorem duration_one (n : ℕ) (v : Parameter n) : duration n (1, v) = height n v := by
  change height n v + (1 : ℝ) * (1 - 1) * dist v (point n) = _
  rw [sub_self, mul_zero, zero_mul, add_zero]

theorem duration_point (n : ℕ) (t : I) : duration n (t, point n) = 0 := by
  change height n (point n) + _ * dist (point n) (point n) = 0
  rw [(height_zero_iff n (point n)).mpr (boundaryPoint n).property,
    dist_self, mul_zero, add_zero]

variable (n : ℕ) {Y : Type} [TopologicalSpace Y] {y : Y}
  (f : C(Parameter n, Path y y)) (hf : ∀ v ∈ Boundary n, f v = Path.refl y)

def endpoint : C(Parameter n, Moore.Loop y) :=
  ⟨Moore.Loop.timed f (height n) (height_nonneg n),
    Moore.Loop.continuous_timed f f.continuous (height n) (height_continuous n)
      (height_nonneg n) (fun v hv ↦ hf v ((height_zero_iff n v).mp hv))⟩

theorem endpoint_normalization (v : Parameter n) : Moore.Loop.toPath (endpoint n f hf v) = f v :=
  Moore.Loop.toPath_timed f (height n) (height_nonneg n) v
    (fun hv ↦ hf v ((height_zero_iff n v).mp hv))

theorem endpoint_boundary (v : Parameter n) (hv : v ∈ Boundary n) : endpoint n f hf v = 1 :=
  Moore.Loop.timed_eq_one_of_zero f (height n) (height_nonneg n) v
    ((height_zero_iff n v).mpr hv)

variable {f} {g : C(Parameter n, Path y y)}
  (hg : ∀ v ∈ Boundary n, g v = Path.refl y)
  (H : f.HomotopyRel g {point n})

include hf hg in
theorem path_eq_refl_of_duration_zero (u : I × Parameter n) (hu : duration n u = 0) :
    H u = Path.refl y := by
  have hb : 0 ≤ (u.1 : ℝ) * (1 - (u.1 : ℝ)) * dist u.2 (point n) :=
    mul_nonneg (mul_nonneg u.1.property.1 (sub_nonneg.mpr u.1.property.2)) dist_nonneg
  have hh : height n u.2 = 0 := by
    have h := height_nonneg n u.2
    change height n u.2 + _ = 0 at hu
    linarith
  have hv := (height_zero_iff n u.2).mp hh
  by_cases h0 : u.1 = 0
  · exact (congrArg (fun t : I ↦ H (t, u.2)) h0).trans
      ((H.apply_zero u.2).trans (hf u.2 hv))
  by_cases h1 : u.1 = 1
  · exact (congrArg (fun t : I ↦ H (t, u.2)) h1).trans
      ((H.apply_one u.2).trans (hg u.2 hv))
  have ht0 : (u.1 : ℝ) ≠ 0 := fun h ↦ h0 (Subtype.ext h)
  have ht1 : (1 : ℝ) - (u.1 : ℝ) ≠ 0 := fun h ↦ h1 (Subtype.ext (sub_eq_zero.mp h).symm)
  have hd : dist u.2 (point n) = 0 := by
    change height n u.2 + _ = 0 at hu
    rw [hh, zero_add] at hu
    exact (mul_eq_zero.mp hu).resolve_left (mul_ne_zero ht0 ht1)
  have hp : u.2 = point n := dist_eq_zero.mp hd
  exact (H.eq_fst u.1 (show u.2 ∈ ({point n} : Set (Parameter n)) from hp)).trans
    (hf u.2 hv)

def liftedHomotopy : (endpoint n f hf).HomotopyRel (endpoint n g hg) {point n} where
  toFun := Moore.Loop.timed H (duration n) (duration_nonneg n)
  continuous_toFun := Moore.Loop.continuous_timed H H.continuous (duration n)
    (duration_continuous n) (duration_nonneg n) (path_eq_refl_of_duration_zero n hf hg H)
  map_zero_left v := Moore.Loop.timed_eq_of_duration_eq H (duration n) (duration_nonneg n)
    (0, v) (endpoint n f hf v)
    ((H.apply_zero v).trans (endpoint_normalization n f hf v).symm) (duration_zero n v)
  map_one_left v := Moore.Loop.timed_eq_of_duration_eq H (duration n) (duration_nonneg n)
    (1, v) (endpoint n g hg v)
    ((H.apply_one v).trans (endpoint_normalization n g hg v).symm) (duration_one n v)
  prop' t v hv := by
    have he : v = point n := hv
    subst v
    exact (Moore.Loop.timed_eq_one_of_zero H (duration n) (duration_nonneg n)
      (t, point n) (duration_point n t)).trans
      (endpoint_boundary n f hf _ (boundaryPoint n).property).symm

include hf hg H in
theorem exists_relative : Nonempty (f.HomotopyRel g (Boundary n)) := by
  obtain ⟨K⟩ := MooreWedgeHomotopy.exists_relative n
    (endpoint_boundary n f hf) (endpoint_boundary n g hg) (liftedHomotopy n hf hg H)
  exact ⟨(K.compContinuousMap Moore.Loop.normalizationMap).cast
    (ContinuousMap.ext (endpoint_normalization n f hf))
    (ContinuousMap.ext (endpoint_normalization n g hg))⟩

end Wikipedia.HopfProblem.DegreeCollapse.PathWedgeHomotopy
