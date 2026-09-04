/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Bases

/-!
# Metric and Euclidean geometry used in the Anderson--Keisler construction

This file isolates two elementary pieces of the sphere-cutting argument.

* A countable dense set in a separable pseudometric space, together with the
  radii `1 / (n + 1)`, gives a countable topological basis of balls.  The
  frontier of every member of this basis is contained in the corresponding
  metric sphere.  Consequently the same construction can be iterated on
  subspaces, including the spheres occurring in a cutting hierarchy.
* A Euclidean sphere meets a set contained in an affine line in at most two
  points, provided the line is based at one point of the sphere.  This is the
  finite-intersection fact used after the relevant affine intersections have
  been shown to be lines by general position.
-/

open Set Topology TopologicalSpace
open Metric
open Module

namespace Erdos909

noncomputable section

section CountableBallBasis

variable {X : Type*} [PseudoMetricSpace X]

/-- The positive radii used for the countable ball bases. -/
def invNatRadius (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

@[simp]
theorem invNatRadius_pos (n : ℕ) : 0 < invNatRadius n := by
  exact one_div_pos.mpr (by positivity)

/-- Balls with center in `D` and radius `1 / (n + 1)`. -/
def invNatBallBasis (D : Set X) : Set (Set X) :=
  {U | ∃ c ∈ D, ∃ n : ℕ, U = ball c (invNatRadius n)}

theorem mem_invNatBallBasis_iff {D : Set X} {U : Set X} :
    U ∈ invNatBallBasis D ↔
      ∃ c ∈ D, ∃ n : ℕ, U = ball c (invNatRadius n) :=
  Iff.rfl

/-- The prescribed family of balls is countable whenever its set of centers
is countable. -/
theorem invNatBallBasis_countable {D : Set X} (hD : D.Countable) :
    (invNatBallBasis D).Countable := by
  let : Countable D := hD.to_subtype
  apply (countable_range fun p : D × ℕ ↦
    ball (p.1 : X) (invNatRadius p.2)).mono
  rintro U ⟨c, hc, n, rfl⟩
  exact ⟨(⟨c, hc⟩, n), rfl⟩

/-- The balls with centers in a dense set and radii `1 / (n + 1)` form a
topological basis.  This version works for pseudometric spaces; no linear
structure is used. -/
theorem invNatBallBasis_isTopologicalBasis {D : Set X} (hD : Dense D) :
    IsTopologicalBasis (invNatBallBasis D) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨c, hc, n, rfl⟩
    exact isOpen_ball
  · intro x U hxU hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
    have hr : 0 < invNatRadius n := invNatRadius_pos n
    obtain ⟨c, hcD, hcx⟩ := hD.exists_mem_open
      (isOpen_ball : IsOpen (ball x (invNatRadius n / 2)))
      ⟨x, by simpa only [mem_ball, dist_self] using (show 0 < invNatRadius n / 2 by positivity)⟩
    refine ⟨ball c (invNatRadius n), ⟨c, hcD, n, rfl⟩, ?_, ?_⟩
    · rw [mem_ball, dist_comm]
      exact hcx.trans (half_lt_self hr)
    · intro y hy
      apply hball
      rw [mem_ball] at hy hcx ⊢
      calc
        dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
        _ < invNatRadius n + invNatRadius n / 2 := add_lt_add hy hcx
        _ < ε := by
          dsimp [invNatRadius] at hn hr ⊢
          linarith

/-- Every frontier belonging to the prescribed ball basis is contained in
its designated metric sphere.  Exact equality is intentionally not assumed:
the inclusion remains valid for subspaces on which the cutting construction
is iterated. -/
theorem frontier_invNatBallBasis_subset_sphere {D : Set X} {U : Set X}
    (hU : U ∈ invNatBallBasis D) :
    ∃ c ∈ D, ∃ n : ℕ,
      U = ball c (invNatRadius n) ∧
        frontier U ⊆ sphere c (invNatRadius n) := by
  rcases hU with ⟨c, hc, n, rfl⟩
  exact ⟨c, hc, n, rfl, frontier_ball_subset_sphere⟩

/-- Every second-countable pseudometric space has a countable ball basis
whose frontiers are controlled by designated metric spheres. -/
theorem exists_countable_ballBasis_frontier_subset_sphere
    [SecondCountableTopology X] :
    ∃ D : Set X,
      D.Countable ∧ Dense D ∧
      (invNatBallBasis D).Countable ∧
      IsTopologicalBasis (invNatBallBasis D) ∧
      ∀ U ∈ invNatBallBasis D,
        ∃ c ∈ D, ∃ n : ℕ,
          U = ball c (invNatRadius n) ∧
            frontier U ⊆ sphere c (invNatRadius n) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  exact ⟨D, hDc, hDd, invNatBallBasis_countable hDc,
    invNatBallBasis_isTopologicalBasis hDd,
    fun _ hU ↦ frontier_invNatBallBasis_subset_sphere hU⟩

end CountableBallBasis

section RealNormedSpace

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space, the frontier control for the countable ball basis
is an equality. -/
theorem frontier_invNatBallBasis_eq_sphere {D : Set E} {U : Set E}
    (hU : U ∈ invNatBallBasis D) :
    ∃ c ∈ D, ∃ n : ℕ,
      U = ball c (invNatRadius n) ∧
        frontier U = sphere c (invNatRadius n) := by
  rcases hU with ⟨c, hc, n, rfl⟩
  exact ⟨c, hc, n, rfl, frontier_ball c (invNatRadius_pos n).ne'⟩

end RealNormedSpace

section GeneralPosition

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The elementary dimension calculation behind the general-position
condition.  An `m`-plane and an `(N-m+1)`-plane whose directions span the
ambient `N`-space have one-dimensional intersection of directions. -/
theorem finrank_inf_eq_one_of_sup_eq_top
    (A B : Submodule ℝ V) (m : ℕ)
    (hm : m ≤ finrank ℝ V)
    (hA : finrank ℝ A = m)
    (hB : finrank ℝ B = finrank ℝ V - m + 1)
    (hsup : A ⊔ B = ⊤) :
    finrank ℝ (A ⊓ B : Submodule ℝ V) = 1 := by
  have hdim := A.finrank_sup_add_finrank_inf_eq B
  rw [hsup, finrank_top, hA, hB] at hdim
  omega

end GeneralPosition

section AffineGeneralPosition

variable {V P : Type*} [AddCommGroup V] [Module ℝ V]
  [AddTorsor V P] [FiniteDimensional ℝ V]

/-- A nonempty affine intersection whose intersection of directions has
finrank one is literally an affine line through any chosen intersection
point. -/
theorem affineInf_eq_affineLine_of_finrank_direction_inf_eq_one
    (A B : AffineSubspace ℝ P) {p : P} (hp : p ∈ A ⊓ B)
    (hfin : finrank ℝ (A.direction ⊓ B.direction : Submodule ℝ V) = 1) :
    ∃ v : V, v ≠ 0 ∧ A ⊓ B = AffineSubspace.mk' p (ℝ ∙ v) := by
  have hne : A.direction ⊓ B.direction ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨v, hv, hv0⟩ := (A.direction ⊓ B.direction).ne_bot_iff.mp hne
  have hspan : A.direction ⊓ B.direction = ℝ ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin hv hv0
  refine ⟨v, hv0, ?_⟩
  rw [← AffineSubspace.mk'_eq hp,
    AffineSubspace.direction_inf_of_mem_inf hp, hspan]

/-- Dimension-data form of
`affineInf_eq_affineLine_of_finrank_direction_inf_eq_one`. -/
theorem affineInf_eq_affineLine_of_generalPosition
    (A B : AffineSubspace ℝ P) {p : P} (hp : p ∈ A ⊓ B) (m : ℕ)
    (hm : m ≤ finrank ℝ V)
    (hA : finrank ℝ A.direction = m)
    (hB : finrank ℝ B.direction = finrank ℝ V - m + 1)
    (hsup : A.direction ⊔ B.direction = ⊤) :
    ∃ v : V, v ≠ 0 ∧ A ⊓ B = AffineSubspace.mk' p (ℝ ∙ v) :=
  affineInf_eq_affineLine_of_finrank_direction_inf_eq_one A B hp
    (finrank_inf_eq_one_of_sup_eq_top A.direction B.direction m hm hA hB hsup)

end AffineGeneralPosition

section SphereLineIntersection

open RealInnerProductSpace
open EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- Once one intersection point is fixed, every further intersection of a
Euclidean sphere with the affine line through that point is either the fixed
point or the canonical second intersection. -/
theorem inter_sphere_subset_pair_of_subset_affineLine
    (s : Sphere P) {p : P} (hp : p ∈ s) (v : V) {L : Set P}
    (hL : L ⊆ (AffineSubspace.mk' p (ℝ ∙ v) : Set P)) :
    L ∩ (s : Set P) ⊆ {p, s.secondInter p v} := by
  rintro x ⟨hxL, hxs⟩
  have hxline := hL hxL
  exact (s.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hp hxline).2 hxs

/-- A Euclidean sphere meets every set contained in an affine line based at
a point of the sphere in a finite set (indeed, in at most two points). -/
theorem finite_inter_sphere_of_subset_affineLine
    (s : Sphere P) {p : P} (hp : p ∈ s) (v : V) {L : Set P}
    (hL : L ⊆ (AffineSubspace.mk' p (ℝ ∙ v) : Set P)) :
    (L ∩ (s : Set P)).Finite :=
  ((finite_singleton (s.secondInter p v)).insert p).subset
    (inter_sphere_subset_pair_of_subset_affineLine s hp v hL)

/-- Cardinal form of `finite_inter_sphere_of_subset_affineLine`: the
intersection contains at most two points. -/
theorem ncard_inter_sphere_le_two_of_subset_affineLine
    (s : Sphere P) {p : P} (hp : p ∈ s) (v : V) {L : Set P}
    (hL : L ⊆ (AffineSubspace.mk' p (ℝ ∙ v) : Set P)) :
    (L ∩ (s : Set P)).ncard ≤ 2 := by
  calc
    (L ∩ (s : Set P)).ncard ≤ ({p, s.secondInter p v} : Set P).ncard :=
      ncard_le_ncard
        (inter_sphere_subset_pair_of_subset_affineLine s hp v hL)
        ((finite_singleton _).insert _)
    _ ≤ 2 := by
      classical
      by_cases h : p = s.secondInter p v
      · have hpMem : p ∈ ({s.secondInter p v} : Set P) := by
          simpa only [mem_singleton_iff] using h
        rw [insert_eq_of_mem hpMem, ncard_singleton]
        omega
      · rw [ncard_pair h]

/-- A metric sphere in a subtype is the trace of the corresponding ambient
metric sphere.  This equality lets terminal spheres living in an affine
subspace be treated by the ambient line--sphere intersection lemma. -/
theorem image_subtype_sphere (A : Set P)
    (s : Sphere A) :
    Subtype.val '' (s : Set A) =
      A ∩ sphere (s.center : P) s.radius := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hxA, hxs⟩
    exact ⟨⟨x, hxA⟩, hxs, rfl⟩

/-- A terminal sphere inside a subspace has finite intersection with any
ambient set whose trace on that subspace is contained in an affine line
based at one point of the terminal sphere. -/
theorem finite_inter_image_subtype_sphere_of_subset_affineLine
    (A : Set P) (s : Sphere A) {p : P}
    (hp : p ∈ Subtype.val '' (s : Set A)) (v : V) {L : Set P}
    (hL : L ∩ A ⊆ (AffineSubspace.mk' p (ℝ ∙ v) : Set P)) :
    (L ∩ (Subtype.val '' (s : Set A))).Finite := by
  let s' : Sphere P := ⟨(s.center : P), s.radius⟩
  have hp' : p ∈ s' := by
    rw [image_subtype_sphere] at hp
    exact hp.2
  apply (finite_inter_sphere_of_subset_affineLine s' hp' v hL).subset
  intro x hx
  rw [image_subtype_sphere] at hx
  exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩

/-- Fully packaged terminal-intersection lemma.  If the direction of an
affine `m`-plane `A` and that of an affine `(N-m+1)`-plane `B` span the
ambient space, then `B` meets every sphere drawn inside `A` in at most two
points (and hence in a finite set). -/
theorem finite_affineSubspace_inter_terminalSphere_of_generalPosition
    [FiniteDimensional ℝ V]
    (A B : AffineSubspace ℝ P) (s : Sphere A) {p : P}
    (hpSphere : p ∈ Subtype.val '' (s : Set A)) (hpB : p ∈ B) (m : ℕ)
    (hm : m ≤ finrank ℝ V)
    (hA : finrank ℝ A.direction = m)
    (hB : finrank ℝ B.direction = finrank ℝ V - m + 1)
    (hsup : A.direction ⊔ B.direction = ⊤) :
    ((B : Set P) ∩ (Subtype.val '' (s : Set A))).Finite := by
  have hpA : p ∈ A := by
    rw [image_subtype_sphere] at hpSphere
    exact hpSphere.1
  have hpInf : p ∈ A ⊓ B := ⟨hpA, hpB⟩
  obtain ⟨v, -, hline⟩ := affineInf_eq_affineLine_of_generalPosition
    A B hpInf m hm hA hB hsup
  apply finite_inter_image_subtype_sphere_of_subset_affineLine
    (A : Set P) s hpSphere v
  intro x hx
  rw [← hline]
  exact ⟨hx.2, hx.1⟩

/-! ## Chord cuts of a parent sphere -/

/-- Polarization identity in the form used for chord cuts.  If `c` and `x`
lie on the sphere of center `o` and radius `R`, and their chordal distance is
`ρ`, then the radial vector of `x` lies in the indicated affine
hyperplane with normal `c -ᵥ o`. -/
theorem inner_vsub_eq_sq_sub_half_sq_of_eq_dist
    {o c x : P} {R ρ : ℝ}
    (hc : dist c o = R) (hx : dist x o = R) (hxc : dist x c = ρ) :
    inner ℝ (x -ᵥ o) (c -ᵥ o) = R ^ 2 - ρ ^ 2 / 2 := by
  have h := norm_sub_sq_real (x -ᵥ o) (c -ᵥ o)
  rw [vsub_sub_vsub_cancel_right x c o,
    ← dist_eq_norm_vsub V x c, hxc,
    ← dist_eq_norm_vsub V x o, hx,
    ← dist_eq_norm_vsub V c o, hc] at h
  nlinarith

/-- The relative metric sphere of chord radius `ρ`, centered at a point
`c` of a parent sphere, lies in a fixed ambient affine hyperplane.  This is
the exact equation used in the Anderson--Keisler cutting hierarchy. -/
theorem image_relativeSphere_subset_chordHyperplane
    (o : P) (R : ℝ) (c : sphere o R) (ρ : ℝ) :
    Subtype.val '' (sphere c ρ : Set (sphere o R)) ⊆
      {x : P | inner ℝ (x -ᵥ o) ((c : P) -ᵥ o) = R ^ 2 - ρ ^ 2 / 2} := by
  rintro x ⟨y, hy, rfl⟩
  apply inner_vsub_eq_sq_sub_half_sq_of_eq_dist
  · exact c.property
  · exact y.property
  · exact hy

/-- If a chord sphere is nonempty, its ambient image is contained in an
affine hyperplane with direction orthogonal to the radial normal
`c -ᵥ o`.  The base point is chosen from the chord sphere, so no arbitrary
choice of a solution to the affine equation is needed. -/
theorem exists_affineHyperplane_containing_image_relativeSphere
    (o : P) (R : ℝ) (c : sphere o R) (ρ : ℝ)
    (hne : (sphere c ρ : Set (sphere o R)).Nonempty) :
    ∃ p : P,
      p ∈ Subtype.val '' (sphere c ρ : Set (sphere o R)) ∧
      Subtype.val '' (sphere c ρ : Set (sphere o R)) ⊆
        (AffineSubspace.mk' p ((ℝ ∙ ((c : P) -ᵥ o))ᗮ) : Set P) := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, ⟨p, hp, rfl⟩, ?_⟩
  intro x hx
  have hxp := image_relativeSphere_subset_chordHyperplane o R c ρ hx
  have hpp := image_relativeSphere_subset_chordHyperplane o R c ρ ⟨p, hp, rfl⟩
  change x -ᵥ (p : P) ∈ (ℝ ∙ ((c : P) -ᵥ o))ᗮ
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [← vsub_sub_vsub_cancel_right x p o, inner_sub_right,
    real_inner_comm (x -ᵥ o) ((c : P) -ᵥ o),
    real_inner_comm ((p : P) -ᵥ o) ((c : P) -ᵥ o), hxp, hpp, sub_self]

/-- A nonempty chord sphere of a Euclidean sphere is itself an ordinary
Euclidean sphere in the chord hyperplane.  The center is the orthogonal
projection of the parent center to the chord hyperplane; choosing its radius
as the distance to one point of the chord avoids any square-root convention.

The equality is stated after mapping both spheres to the original affine
space.  It is therefore directly usable when a recursive metric-sphere cut
has to be reinterpreted as a sphere in a codimension-one affine subspace. -/
theorem exists_affineSphere_image_eq_image_relativeSphere
    [FiniteDimensional ℝ V]
    (o : P) (R : ℝ) (c : sphere o R) (ρ : ℝ)
    (hne : (sphere c ρ : Set (sphere o R)).Nonempty) :
    ∃ (H : AffineSubspace ℝ P) (s : Sphere H),
      H.direction = (ℝ ∙ ((c : P) -ᵥ o))ᗮ ∧
      Subtype.val '' (s : Set H) =
        Subtype.val '' (sphere c ρ : Set (sphere o R)) := by
  obtain ⟨p, hp⟩ := hne
  let H : AffineSubspace ℝ P :=
    AffineSubspace.mk' (p : P) ((ℝ ∙ ((c : P) -ᵥ o))ᗮ)
  have hpH : (p : P) ∈ H := by
    exact AffineSubspace.self_mem_mk' _ _
  let : Nonempty H := ⟨⟨p, hpH⟩⟩
  let q : H := EuclideanGeometry.orthogonalProjection H o
  let s : Sphere H := ⟨q, dist (⟨p, hpH⟩ : H) q⟩
  have hproj : EuclideanGeometry.orthogonalProjection H (c : P) = q := by
    change EuclideanGeometry.orthogonalProjection H (c : P) =
      EuclideanGeometry.orthogonalProjection H o
    rw [EuclideanGeometry.orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]
    rw [show H.direction = (ℝ ∙ ((c : P) -ᵥ o))ᗮ by
      simp only [H, AffineSubspace.direction_mk']]
    change (c : P) -ᵥ o ∈ ((ℝ ∙ ((c : P) -ᵥ o))ᗮ)ᗮ
    exact ((ℝ ∙ ((c : P) -ᵥ o)).le_orthogonal_orthogonal)
      (Submodule.mem_span_singleton_self ((c : P) -ᵥ o))
  refine ⟨H, s, by simp only [H, AffineSubspace.direction_mk'], ?_⟩
  ext x
  constructor
  · rintro ⟨xH, hxHs, rfl⟩
    have hxo : dist (xH : P) o = dist (p : P) o := by
      apply (EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq
        o xH.property hpH).2
      simpa only [q, s, Subtype.dist_eq] using
        (EuclideanGeometry.mem_sphere.mp hxHs)
    have hxc : dist (xH : P) (c : P) = dist (p : P) (c : P) := by
      apply (EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq
        (c : P) xH.property hpH).2
      rw [hproj]
      simpa only [q, s, Subtype.dist_eq] using
        (EuclideanGeometry.mem_sphere.mp hxHs)
    let y : sphere o R := ⟨(xH : P), hxo.trans p.property⟩
    refine ⟨y, ?_, rfl⟩
    exact hxc.trans hp
  · rintro ⟨y, hy, rfl⟩
    have hyH : (y : P) ∈ H := by
      have hyp := image_relativeSphere_subset_chordHyperplane
        o R c ρ ⟨y, hy, rfl⟩
      have hpp := image_relativeSphere_subset_chordHyperplane
        o R c ρ ⟨p, hp, rfl⟩
      change (y : P) -ᵥ (p : P) ∈ (ℝ ∙ ((c : P) -ᵥ o))ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      rw [← vsub_sub_vsub_cancel_right (y : P) (p : P) o, inner_sub_right,
        real_inner_comm ((y : P) -ᵥ o) ((c : P) -ᵥ o),
        real_inner_comm ((p : P) -ᵥ o) ((c : P) -ᵥ o), hyp, hpp, sub_self]
    let yH : H := ⟨(y : P), hyH⟩
    have hdist : dist (yH : P)
        (EuclideanGeometry.orthogonalProjection H o) =
        dist (p : P) (EuclideanGeometry.orthogonalProjection H o) := by
      apply (EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq
        o hyH hpH).1
      exact y.property.trans p.property.symm
    refine ⟨yH, ?_, rfl⟩
    apply EuclideanGeometry.mem_sphere.mpr
    simpa only [s, q, Subtype.dist_eq] using hdist

/-- Total version of
`exists_affineSphere_image_eq_image_relativeSphere`.  An empty relative
sphere is represented by a negative-radius Euclidean sphere in the same
normal hyperplane.  Thus every member of a metric ball basis, including a
degenerate one with empty frontier, has a uniform affine-sphere
reidentification. -/
theorem exists_affineSphere_image_eq_image_relativeSphere_total
    [FiniteDimensional ℝ V]
    (o : P) (R : ℝ) (c : sphere o R) (ρ : ℝ) :
    ∃ (H : AffineSubspace ℝ P) (s : Sphere H),
      H.direction = (ℝ ∙ ((c : P) -ᵥ o))ᗮ ∧
      Subtype.val '' (s : Set H) =
        Subtype.val '' (sphere c ρ : Set (sphere o R)) := by
  by_cases hne : (sphere c ρ : Set (sphere o R)).Nonempty
  · exact exists_affineSphere_image_eq_image_relativeSphere o R c ρ hne
  · let H : AffineSubspace ℝ P :=
      AffineSubspace.mk' o ((ℝ ∙ ((c : P) -ᵥ o))ᗮ)
    have hoH : o ∈ H := AffineSubspace.self_mem_mk' _ _
    let s : Sphere H := ⟨⟨o, hoH⟩, -1⟩
    refine ⟨H, s, by simp only [H, AffineSubspace.direction_mk'], ?_⟩
    have hempty : (sphere c ρ : Set (sphere o R)) = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [hempty, image_empty]
    have hsEmpty : (s : Set H) = ∅ := by
      change sphere (⟨o, hoH⟩ : H) (-1) = ∅
      exact Metric.sphere_eq_empty_of_neg (by norm_num)
    rw [hsEmpty, image_empty]

end SphereLineIntersection

end

end Erdos909
