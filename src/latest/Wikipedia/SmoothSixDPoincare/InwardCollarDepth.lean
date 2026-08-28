import Wikipedia.SmoothSixDPoincare.InwardCollarExtension
import Wikipedia.SmoothSixDPoincare.HandleCollarDepth

/-!
# Extend the corner depth continuously through the original collared body

Use the actual collar coordinates on its closed image and the constant
one off its open image. Truncation at one makes the two formulas agree
at the entire inner end. Boundary and fixed-exterior values remain exact.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {i : C(X, Y)}
  (C : InwardBoundaryCollar i) (d : C(X, ℝ))

def depthOnRegion : C(C.region, ℝ) :=
  ⟨fun y => min 1 (HandleCollarDepth.depth ((C.coordinates.symm y).2 : ℝ)
    (d (C.coordinates.symm y).1)),
    continuous_const.min (HandleCollarDepth.continuous_depth.comp
      ((continuous_subtype_val.comp (continuous_snd.comp C.coordinates.symm.continuous)).prodMk
        (d.continuous.comp (continuous_fst.comp C.coordinates.symm.continuous))))⟩

theorem depth_agree (hd : ∀ x, 0 ≤ d x) (a : C.region) (b : C.fixedRegion)
    (hab : a.val = b.val) : C.depthOnRegion d a = 1 := by
  let q := C.coordinates.symm a
  have hq : C.map q = a.val := congrArg Subtype.val (C.coordinates.apply_symm_apply a)
  have ht : q.2 = 1 := (C.map_mem_fixedRegion_iff q).mp ((hq.trans hab).symm ▸ b.property)
  change min 1 (HandleCollarDepth.depth (q.2 : ℝ) (d q.1)) = 1
  rw [ht]
  exact min_eq_left (HandleCollarDepth.depth_ge_left 1 (hd q.1))

def bodyDepth (hd : ∀ x, 0 ≤ d x) : C(Y, ℝ) :=
  ⟨ClosedCover.glue C.region_cover (C.depthOnRegion d) (fun _ => 1),
    ClosedCover.continuous_glue C.region_cover C.closed_region C.closed_fixedRegion
      (C.depthOnRegion d) (fun _ => 1) (C.depthOnRegion d).continuous continuous_const
      (C.depth_agree d hd)⟩

theorem bodyDepth_map (hd : ∀ x, 0 ≤ d x) (q : X × unitInterval) :
    C.bodyDepth d hd (C.map q) = min 1 (HandleCollarDepth.depth (q.2 : ℝ) (d q.1)) := by
  have h := ClosedCover.glue_left C.region_cover (C.depthOnRegion d) (fun _ => (1 : ℝ))
    (C.coordinates q)
  exact h.trans (congrArg (fun p : X × unitInterval =>
    min 1 (HandleCollarDepth.depth (p.2 : ℝ) (d p.1))) (C.coordinates.symm_apply_apply q))

theorem bodyDepth_fixed (hd : ∀ x, 0 ≤ d x) (y : Y) (hy : y ∉ C.innerRegion) :
    C.bodyDepth d hd y = 1 :=
  ClosedCover.glue_right C.region_cover (C.depthOnRegion d) (fun _ => (1 : ℝ))
    (C.depth_agree d hd) ⟨y, hy⟩

theorem bodyDepth_boundary (hd : ∀ x, 0 ≤ d x) (x : X) :
    C.bodyDepth d hd (i x) = min 1 (HandleCollarDepth.depth 0 (d x)) := by
  rw [← C.zero x, C.bodyDepth_map]
  rfl

theorem bodyDepth_lt_one_mem (hd : ∀ x, 0 ≤ d x) {y : Y}
    (hy : C.bodyDepth d hd y < 1) : y ∈ C.innerRegion := by
  by_contra hnot
  rw [C.bodyDepth_fixed d hd y hnot] at hy
  exact (lt_irrefl _ hy).elim

end Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
