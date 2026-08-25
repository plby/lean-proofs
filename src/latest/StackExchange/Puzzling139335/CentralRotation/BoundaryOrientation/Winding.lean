import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.Direction
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Algebra
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Homotopy
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.JordanContraction
import StackExchange.Puzzling139335.JordanTransport

/-!
# Winding of continuous plane paths

All winding values below are differences of actual continuous real lifts of
the angular path.  No rectifiability or boundary measure assumption occurs.
The principal geometric facts are invariance under a direct affine isometry,
constancy as the reference point moves in the complement of the path, and
vanishing outside a closed Jordan region containing the path.
-/

open Set unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

/-- Winding is the angular lift displacement; for closed paths it is an integer. -/
def winding (f : C(I, Plane)) (x : Plane) (hx : ∀ t, f t ≠ x) : ℝ :=
  CircleDegree.displacement (directionPath f x hx)

theorem winding_congr {f g : C(I, Plane)} (hfg : f = g) (x : Plane)
    (hf : ∀ t, f t ≠ x) (hg : ∀ t, g t ≠ x) :
    winding f x hf = winding g x hg := by
  subst g
  rfl

/-- A direct affine isometry does not change winding about the transported point. -/
theorem winding_direct (g : Plane ≃ᵃⁱ[ℝ] Plane) {a : Circle} {b : ℂ}
    (hg : ∀ p, PlaneIsometries.complexEquiv (g p) =
      (a : ℂ) * PlaneIsometries.complexEquiv p + b)
    (f : C(I, Plane)) (x : Plane) (hx : ∀ t, f t ≠ x) :
    winding ((⟨g, g.continuous⟩ : C(Plane, Plane)).comp f) (g x)
        (fun t => g.injective.ne (hx t)) =
      winding f x hx := by
  have hpath : directionPath ((⟨g, g.continuous⟩ : C(Plane, Plane)).comp f) (g x)
      (fun t => g.injective.ne (hx t)) =
      ContinuousMap.const I (circleAngle a) + directionPath f x hx := by
    ext t
    exact directionFrom_direct g hg x ⟨f t, hx t⟩
  unfold winding
  rw [hpath, CircleDegree.displacement_const_add]

/-- Moving the reference point along a path disjoint from a closed plane loop
leaves its winding unchanged. -/
theorem winding_eq_of_avoiding_path (f : C(I, Plane)) (hclosed : f 0 = f 1)
    {x y : Plane} (α : Path x y) (hα : ∀ s t, f t ≠ α s)
    (hx : ∀ t, f t ≠ x) (hy : ∀ t, f t ≠ y) :
    winding f x hx = winding f y hy := by
  let H : C(I × I, AddCircle (1 : ℝ)) :=
    directionDifference.comp
      ⟨fun st => ⟨(f st.2, α st.1), hα st.1 st.2⟩,
        ((f.continuous.comp continuous_snd).prodMk
          (α.continuous.comp continuous_fst)).subtype_mk _⟩
  have hH : ∀ s, H (s, 1) = H (s, 0) := by
    intro s
    apply congrArg directionDifference
    apply Subtype.ext
    exact Prod.ext hclosed.symm rfl
  have hzero : CircleDegree.slice H 0 = directionPath f x hx := by
    ext t
    apply congrArg directionDifference
    apply Subtype.ext
    exact Prod.ext rfl α.source
  have hone : CircleDegree.slice H 1 = directionPath f y hy := by
    ext t
    apply congrArg directionDifference
    apply Subtype.ext
    exact Prod.ext rfl α.target
  simpa only [winding, hzero, hone] using
    CircleDegree.displacement_slice_eq H hH 0 1

/-- Winding is constant on every path-connected subset of a loop's complement. -/
theorem winding_eq_of_joinedIn (f : C(I, Plane)) (hclosed : f 0 = f 1)
    {x y : Plane} (hxy : JoinedIn (range f)ᶜ x y)
    (hx : ∀ t, f t ≠ x) (hy : ∀ t, f t ≠ y) :
    winding f x hx = winding f y hy := by
  obtain ⟨α, hα⟩ := hxy
  apply winding_eq_of_avoiding_path f hclosed α ?_ hx hy
  intro s t h
  exact hα s ⟨t, h⟩

/-- A closed path contained in a Jordan region has zero winding about every
point outside that region. -/
theorem winding_eq_zero_of_jordan_container {P : Set Plane} (hP : IsJordanRegion P)
    (f : C(I, Plane)) (hf : ∀ t, f t ∈ P) (hclosed : f 0 = f 1)
    {x : Plane} (hx : x ∉ P) (havoid : ∀ t, f t ≠ x) :
    winding f x havoid = 0 := by
  have hnull := (loop_homotopic_const_complement hP f hf hclosed hx).comp_continuousMap
    (directionFrom x)
  have hstart : (directionFrom x).comp (mapInPointComplement f hf hx) =
      directionPath f x havoid := by
    ext t
    rfl
  have hend : (directionFrom x).comp
      (ContinuousMap.const I (mapInPointComplement f hf hx 0)) =
      ContinuousMap.const I (directionPath f x havoid 0) := by
    ext t
    rfl
  rw [hstart, hend] at hnull
  exact (CircleDegree.displacement_eq_zero_iff_homotopicRel_const _).mpr hnull

/-- The winding of a Jordan boundary loop is independent of its interior
reference point. -/
theorem winding_eq_inside_jordan {P : Set Plane} (hP : IsJordanRegion P)
    (f : C(I, Plane)) (hf : range f ⊆ frontier P) (hclosed : f 0 = f 1)
    {x y : Plane} (hxP : x ∈ interior P) (hyP : y ∈ interior P)
    (hx : ∀ t, f t ≠ x) (hy : ∀ t, f t ≠ y) :
    winding f x hx = winding f y hy := by
  apply winding_eq_of_joinedIn f hclosed
    ((hP.isPathConnected_interior.joinedIn x hxP y hyP).mono ?_) hx hy
  intro z hz hzf
  exact (hf hzf).2 hz

end

end Puzzling139335.CentralRotation.BoundaryOrientation
