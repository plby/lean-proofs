import Wikipedia.NoExoticSixSphere.SphereMooreCommutatorExtension
import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionRelative

/-!
# Straightening based product homotopies in the actual Moore loop space

Remove the two axis tracks by reversing and multiplying Moore loops.
The residual axis tracks are explicit backtracks. Their simultaneous
contraction fixes both homotopy endpoints, so the original fat-wedge
cofibration extends this contraction in the compact-open path space.
The resulting homotopy is stationary on the entire fat wedge.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.MooreWedgeHomotopy

open NoExoticSixSphere SphereMooreCommutator
open OrbitPair

def leftAxis (n : ℕ) : C(Parameter n, Parameter n) :=
  ⟨fun v ↦ ![v 0, spherePole n], by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_const⟩

def rightAxis (n : ℕ) : C(Parameter n, Parameter n) :=
  ⟨fun v ↦ ![spherePole n, v 1], by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_apply 1⟩

theorem leftAxis_boundary (n : ℕ) (v : Parameter n) : leftAxis n v ∈ Boundary n :=
  ⟨1, rfl⟩

theorem rightAxis_boundary (n : ℕ) (v : Parameter n) : rightAxis n v ∈ Boundary n :=
  ⟨0, rfl⟩

theorem axis_cases (n : ℕ) (v : Boundary n) :
    (leftAxis n v.val = point n ∧ rightAxis n v.val = v.val) ∨
      (leftAxis n v.val = v.val ∧ rightAxis n v.val = point n) := by
  obtain ⟨i, hi⟩ := v.property
  fin_cases i
  · left
    constructor <;> funext j <;> fin_cases j
    · exact hi
    · rfl
    · exact hi.symm
    · rfl
  · right
    constructor <;> funext j <;> fin_cases j
    · rfl
    · exact hi.symm
    · rfl
    · exact hi

variable (n : ℕ) {Y : Type} [TopologicalSpace Y] {y : Y}
  {f g : C(Parameter n, Moore.Loop y)}
  (hf : ∀ v ∈ Boundary n, f v = 1) (hg : ∀ v ∈ Boundary n, g v = 1)
  (H : f.HomotopyRel g {point n})

include hf in
theorem homotopy_point (t : I) : H (t, point n) = 1 :=
  (H.eq_fst t (Set.mem_singleton _)).trans (hf _ (boundaryPoint n).property)

def corrected : C(I × Parameter n, Moore.Loop y) :=
  ⟨fun u ↦ Moore.Loop.reverse (H (u.1, leftAxis n u.2)) * H u *
      Moore.Loop.reverse (H (u.1, rightAxis n u.2)),
    ((Moore.Loop.continuous_reverse.comp (H.continuous.comp
      (continuous_fst.prodMk ((leftAxis n).continuous.comp continuous_snd)))).mul
        H.continuous).mul
      (Moore.Loop.continuous_reverse.comp (H.continuous.comp
        (continuous_fst.prodMk ((rightAxis n).continuous.comp continuous_snd))))⟩

include hf in
theorem corrected_zero (v : Parameter n) : corrected n H (0, v) = f v := by
  change Moore.Loop.reverse (H (0, leftAxis n v)) * H (0, v) *
    Moore.Loop.reverse (H (0, rightAxis n v)) = f v
  rw [H.apply_zero, H.apply_zero, H.apply_zero,
    hf _ (leftAxis_boundary n v), hf _ (rightAxis_boundary n v),
    Moore.Loop.reverse_one, one_mul, mul_one]

include hg in
theorem corrected_one (v : Parameter n) : corrected n H (1, v) = g v := by
  change Moore.Loop.reverse (H (1, leftAxis n v)) * H (1, v) *
    Moore.Loop.reverse (H (1, rightAxis n v)) = g v
  rw [H.apply_one, H.apply_one, H.apply_one,
    hg _ (leftAxis_boundary n v), hg _ (rightAxis_boundary n v),
    Moore.Loop.reverse_one, one_mul, mul_one]

def correctedHomotopy : f.Homotopy g where
  toContinuousMap := corrected n H
  map_zero_left := corrected_zero n hf H
  map_one_left := corrected_one n hg H

def contraction : C(I × (I × Boundary n), Moore.Loop y) :=
  ⟨fun u ↦ Moore.Loop.retrace
      (u.1, Moore.Loop.reverse (H (u.2.1, leftAxis n u.2.2.val))) *
    Moore.Loop.retrace (u.1, H (u.2.1, rightAxis n u.2.2.val)), by
      have hl : Continuous (fun u : I × (I × Boundary n) ↦
          H (u.2.1, leftAxis n u.2.2.val)) := by fun_prop
      have hr : Continuous (fun u : I × (I × Boundary n) ↦
          H (u.2.1, rightAxis n u.2.2.val)) := by fun_prop
      exact (Moore.Loop.continuous_retrace.comp
        (continuous_fst.prodMk (Moore.Loop.continuous_reverse.comp hl))).mul
        (Moore.Loop.continuous_retrace.comp (continuous_fst.prodMk hr))⟩

include hf in
theorem contraction_zero (t : I) (v : Boundary n) :
    contraction n H (0, t, v) = corrected n H (t, v.val) := by
  change Moore.Loop.retrace (0, Moore.Loop.reverse (H (t, leftAxis n v.val))) *
    Moore.Loop.retrace (0, H (t, rightAxis n v.val)) =
      Moore.Loop.reverse (H (t, leftAxis n v.val)) * H (t, v.val) *
        Moore.Loop.reverse (H (t, rightAxis n v.val))
  rw [Moore.Loop.retrace_zero, Moore.Loop.retrace_zero, Moore.Loop.reverse_reverse]
  rcases axis_cases n v with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp only [hl, hr, homotopy_point n hf H, Moore.Loop.reverse_one, one_mul]
  · simp only [hl, hr, homotopy_point n hf H, Moore.Loop.reverse_one, mul_one]

theorem contraction_one (t : I) (v : Boundary n) : contraction n H (1, t, v) = 1 := by
  change Moore.Loop.retrace (1, _) * Moore.Loop.retrace (1, _) = 1
  rw [Moore.Loop.retrace_one, Moore.Loop.retrace_one, mul_one]

include hf in
theorem contraction_endpoint_zero (s : I) (v : Boundary n) :
    contraction n H (s, 0, v) = 1 := by
  change Moore.Loop.retrace (s, Moore.Loop.reverse (H (0, leftAxis n v.val))) *
    Moore.Loop.retrace (s, H (0, rightAxis n v.val)) = 1
  rw [H.apply_zero, H.apply_zero, hf _ (leftAxis_boundary n v.val),
    hf _ (rightAxis_boundary n v.val), Moore.Loop.reverse_one,
    Moore.Loop.retrace_identity, mul_one]

include hg in
theorem contraction_endpoint_one (s : I) (v : Boundary n) :
    contraction n H (s, 1, v) = 1 := by
  change Moore.Loop.retrace (s, Moore.Loop.reverse (H (1, leftAxis n v.val))) *
    Moore.Loop.retrace (s, H (1, rightAxis n v.val)) = 1
  rw [H.apply_one, H.apply_one, hg _ (leftAxis_boundary n v.val),
    hg _ (rightAxis_boundary n v.val), Moore.Loop.reverse_one,
    Moore.Loop.retrace_identity, mul_one]

def contractionPaths : C(I × Boundary n, C(I, Moore.Loop y)) :=
  ((contraction n H).comp
    ⟨fun u : (I × Boundary n) × I ↦ (u.1.1, u.2, u.1.2), by fun_prop⟩).curry

include hf hg H in
theorem exists_relative : Nonempty (f.HomotopyRel g (Boundary n)) := by
  let i := SubspaceCofibration.inclusion (Boundary n)
  obtain ⟨K⟩ := HomotopyExtension.exists_relative_of_boundary_contraction
    (Z := TopCat.of (Moore.Loop y)) i
    (FatWedge.sphere_hasHomotopyExtension (spherePole n) 2)
    (correctedHomotopy n hf hg H) (contractionPaths n H)
    (fun v ↦ ContinuousMap.ext (fun t ↦ contraction_zero n hf H t v))
    (fun v t ↦ (contraction_one n H t v).trans (hf v.val v.property).symm)
    (fun s v ↦ (contraction_endpoint_zero n hf H s v).trans (hf v.val v.property).symm)
    (fun s v ↦ (contraction_endpoint_one n hg H s v).trans (hg v.val v.property).symm)
  have hr : Set.range i = Boundary n := by
    ext v
    exact SubspaceCofibration.mem_range _ v
  rw [hr] at K
  exact ⟨K⟩

end Wikipedia.HopfProblem.DegreeCollapse.MooreWedgeHomotopy
