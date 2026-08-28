import Wikipedia.HopfProblem.ToricCones
import Wikipedia.HopfProblem.ToricSeparation
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Geometry.Convex.Cone.Face.Basic

/-!
# The common-face property of the cusp fan

The integral separating characters of `ToricSeparation` expose the common
faces of the closed cones over the A₂ triangulation.  In particular the
intersection of two maximal cones is exactly the nonnegative span of their
shared primitive rays, as asserted in Lemma 4.2(i) of `tex/s6.tex`.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricFan.Triangle

open ToricSeparation

/-- A primitive ray generator, regarded as a real vector. -/
def realRay (s : Triangle) (j : Fin 3) : RealCoordinates :=
  fun i => (s.rays i j : ℝ)

theorem coordinates_realRay (s t : Triangle) (i j : Fin 3) :
    t.coordinates (s.realRay j) i = (transition s t i j : ℝ) := by
  simp [coordinates, realRay, transition, Matrix.mulVec, Matrix.mul_apply, dotProduct]

theorem realRay_mem_cone (s : Triangle) (j : Fin 3) : s.realRay j ∈ s.cone := by
  intro i
  rw [coordinates_realRay, transition_self]
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem generate_eq_sum (s : Triangle) (c : RealCoordinates) :
    s.generate c = ∑ j, c j • s.realRay j := by
  ext i
  simp [generate, realRay, Matrix.mulVec, dotProduct, mul_comm]

/-- A ray in `s` is shared when its primitive generator also occurs in `t`. -/
def SharedRay (s t : Triangle) (j : Fin 3) : Prop :=
  ∃ k, s.realRay j = t.realRay k

private theorem column_single_of_nonneg (s t : Triangle) (j : Fin 3)
    (hn : ∀ i, 0 ≤ transition s t i j) :
    ∃ k, ∀ i, transition s t i j = if i = k then 1 else 0 := by
  have hsum := transition_heightOne s t j
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.sum_univ_zero, add_zero] at hsum
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have hcases : transition s t 0 j = 1 ∨ transition s t 1 j = 1 ∨
      transition s t 2 j = 1 := by omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega

theorem sharedRay_of_transition_nonneg (s t : Triangle) (j : Fin 3)
    (hn : ∀ i, 0 ≤ transition s t i j) : SharedRay s t j := by
  obtain ⟨k, hk⟩ := column_single_of_nonneg s t j hn
  refine ⟨k, ?_⟩
  ext i
  have h := congrFun (congrFun (transition_covariance s t) i) j
  have he : t.rays i k = s.rays i j := by
    simpa [Matrix.mul_apply, hk] using h
  change (s.rays i j : ℝ) = (t.rays i k : ℝ)
  exact_mod_cast he.symm

/-- The real linear functional corresponding to the integral separator. -/
def separatingForm (s t : Triangle) : RealCoordinates →ₗ[ℝ] ℝ :=
  ∑ i, (character s t i : ℝ) • LinearMap.proj i

theorem separatingForm_apply (s t : Triangle) (x : RealCoordinates) :
    separatingForm s t x = ∑ i, (character s t i : ℝ) * x i := by
  simp [separatingForm]

theorem separatingForm_swap (s t : Triangle) :
    separatingForm t s = -separatingForm s t := by
  apply LinearMap.ext
  intro x
  rw [separatingForm_apply, LinearMap.neg_apply, separatingForm_apply, character_swap]
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem separatingForm_realRay (s t : Triangle) (j : Fin 3) :
    separatingForm s t (s.realRay j) = (exponents s t j : ℝ) := by
  simp [separatingForm_apply, realRay, exponents, Matrix.vecMul, dotProduct]

theorem separatingForm_generate (s t : Triangle) (c : RealCoordinates) :
    separatingForm s t (s.generate c) = ∑ j, (exponents s t j : ℝ) * c j := by
  rw [generate_eq_sum, map_sum]
  simp [separatingForm_realRay, mul_comm]

theorem separatingForm_nonneg (s t : Triangle) {x : RealCoordinates}
    (hx : x ∈ s.cone) : 0 ≤ separatingForm s t x := by
  rw [← generate_coordinates s x, separatingForm_generate]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (by exact_mod_cast exponents_nonneg s t j)
    (hx j)

theorem separatingForm_nonpos (s t : Triangle) {x : RealCoordinates}
    (hx : x ∈ t.cone) : separatingForm s t x ≤ 0 := by
  have h := separatingForm_nonneg t s hx
  rw [separatingForm_swap, LinearMap.neg_apply] at h
  linarith

theorem exponents_zero_iff_sharedRay (s t : Triangle) (j : Fin 3) :
    exponents s t j = 0 ↔ SharedRay s t j := by
  constructor
  · intro hz
    exact sharedRay_of_transition_nonneg s t j
      (transition_nonneg_of_exponent_zero s t j hz)
  · rintro ⟨k, hk⟩
    have h := separatingForm_nonpos s t (realRay_mem_cone t k)
    rw [← hk, separatingForm_realRay] at h
    have hn := exponents_nonneg s t j
    exact le_antisymm (by exact_mod_cast h) hn

/-- The zero-containing cone, in the bundled type used for cone faces. -/
def pointedCone (s : Triangle) : PointedCone ℝ RealCoordinates :=
  s.cone.toPointedCone (zero_mem_cone s)

@[simp] theorem mem_pointedCone (s : Triangle) (x : RealCoordinates) :
    x ∈ s.pointedCone ↔ x ∈ s.cone := Iff.rfl

/-- The common primitive generators, before taking their nonnegative span. -/
def commonRayGenerators (s t : Triangle) : Set RealCoordinates :=
  range s.realRay ∩ range t.realRay

theorem realRay_mem_commonRayGenerators (s t : Triangle) (j : Fin 3) :
    s.realRay j ∈ commonRayGenerators s t ↔ SharedRay s t j := by
  constructor
  · rintro ⟨_, k, hk⟩
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨j, rfl⟩, ⟨k, hk.symm⟩⟩

theorem commonRay_hull_le_left (s t : Triangle) :
    PointedCone.hull ℝ (commonRayGenerators s t) ≤ s.pointedCone := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨j, rfl⟩, _⟩
  exact realRay_mem_cone s j

theorem commonRay_hull_le_right (s t : Triangle) :
    PointedCone.hull ℝ (commonRayGenerators s t) ≤ t.pointedCone := by
  apply Submodule.span_le.mpr
  rintro x ⟨_, ⟨k, rfl⟩⟩
  exact realRay_mem_cone t k

theorem coordinates_eq_zero_of_separatingForm_zero (s t : Triangle)
    {x : RealCoordinates} (hx : x ∈ s.cone) (hz : separatingForm s t x = 0)
    {j : Fin 3} (hj : ¬SharedRay s t j) : s.coordinates x j = 0 := by
  have hsum : ∑ k, (exponents s t k : ℝ) * s.coordinates x k = 0 := by
    rw [← separatingForm_generate, generate_coordinates, hz]
  have he : (exponents s t j : ℝ) * s.coordinates x j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (by exact_mod_cast exponents_nonneg s t k) (hx k))).mp
      hsum j (Finset.mem_univ j)
  rcases mul_eq_zero.mp he with he | hc
  · exact False.elim (hj ((exponents_zero_iff_sharedRay s t j).mp (by exact_mod_cast he)))
  · exact hc

theorem mem_commonRay_hull_of_separatingForm_zero (s t : Triangle)
    {x : RealCoordinates} (hx : x ∈ s.cone) (hz : separatingForm s t x = 0) :
    x ∈ PointedCone.hull ℝ (commonRayGenerators s t) := by
  rw [← generate_coordinates s x, generate_eq_sum]
  apply Submodule.sum_mem
  intro j _
  by_cases hj : SharedRay s t j
  · exact PointedCone.smul_mem _ (hx j)
      (PointedCone.subset_hull ((realRay_mem_commonRayGenerators s t j).mpr hj))
  · rw [coordinates_eq_zero_of_separatingForm_zero s t hx hz hj, zero_smul]
    exact Submodule.zero_mem _

/-- The intersection is cut out inside the first cone by a supporting
integral hyperplane. -/
theorem mem_cone_inter_iff_separatingForm_zero (s t : Triangle) (x : RealCoordinates) :
    x ∈ (s.cone : Set RealCoordinates) ∩ t.cone ↔
      x ∈ s.cone ∧ separatingForm s t x = 0 := by
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨hs, le_antisymm (separatingForm_nonpos s t ht)
      (separatingForm_nonneg s t hs)⟩
  · rintro ⟨hs, hz⟩
    exact ⟨hs, commonRay_hull_le_right s t
      (mem_commonRay_hull_of_separatingForm_zero s t hs hz)⟩

/-- The two cones meet in the nonnegative span of their common rays. -/
theorem cone_inter_eq_commonRay_hull (s t : Triangle) :
    (s.cone : Set RealCoordinates) ∩ t.cone =
      (PointedCone.hull ℝ (commonRayGenerators s t) : Set RealCoordinates) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs, hz⟩ := (mem_cone_inter_iff_separatingForm_zero s t x).mp hx
    exact mem_commonRay_hull_of_separatingForm_zero s t hs hz
  · intro hx
    exact ⟨commonRay_hull_le_left s t hx, commonRay_hull_le_right s t hx⟩

/-- The common face is exposed in the first cone. -/
theorem cone_inter_isExposed_left (s t : Triangle) :
    IsExposed ℝ (s.cone : Set RealCoordinates) ((s.cone : Set RealCoordinates) ∩ t.cone) := by
  intro _
  refine ⟨-(separatingForm s t).toContinuousLinearMap, ?_⟩
  ext x
  rw [mem_cone_inter_iff_separatingForm_zero]
  change (x ∈ s.cone ∧ separatingForm s t x = 0) ↔
    x ∈ s.cone ∧ ∀ y ∈ s.cone, -separatingForm s t y ≤ -separatingForm s t x
  constructor
  · rintro ⟨hx, hz⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h := separatingForm_nonneg s t hy
    rw [hz]
    linarith
  · rintro ⟨hx, hmax⟩
    have h := hmax 0 (zero_mem_cone s)
    rw [map_zero] at h
    exact ⟨hx, le_antisymm (by linarith) (separatingForm_nonneg s t hx)⟩

/-- The same intersection is exposed in the second cone. -/
theorem cone_inter_isExposed_right (s t : Triangle) :
    IsExposed ℝ (t.cone : Set RealCoordinates) ((s.cone : Set RealCoordinates) ∩ t.cone) := by
  simpa only [inter_comm] using cone_inter_isExposed_left t s

/-- The cone-face predicate, in addition to the exposed-face statement. -/
theorem cone_inter_isFaceOf_left (s t : Triangle) :
    (s.pointedCone ⊓ t.pointedCone).IsFaceOf s.pointedCone := by
  refine PointedCone.IsFaceOf.of_mem_of_add_mem_left inf_le_left ?_
  intro x y hx hy hxy
  have hzero := (mem_cone_inter_iff_separatingForm_zero s t (x + y)).mp hxy
  have hxnonneg := separatingForm_nonneg s t hx
  have hynonneg := separatingForm_nonneg s t hy
  rw [map_add] at hzero
  exact (mem_cone_inter_iff_separatingForm_zero s t x).mpr ⟨hx, by linarith [hzero.2]⟩

theorem cone_inter_isFaceOf_right (s t : Triangle) :
    (s.pointedCone ⊓ t.pointedCone).IsFaceOf t.pointedCone := by
  simpa only [inf_comm] using cone_inter_isFaceOf_left t s

/-- All cones of the fan, including its zero cone and lower-dimensional
faces, are obtained by retaining a subset of the rays of a triangle. -/
def rayFace (s : Triangle) (J : Set (Fin 3)) : PointedCone ℝ RealCoordinates :=
  PointedCone.hull ℝ (s.realRay '' J)

theorem rayFace_le (s : Triangle) (J : Set (Fin 3)) : s.rayFace J ≤ s.pointedCone := by
  apply Submodule.span_le.mpr
  rintro x ⟨j, _, rfl⟩
  exact realRay_mem_cone s j

theorem coordinates_eq_zero_of_mem_rayFace (s : Triangle) (J : Set (Fin 3))
    {x : RealCoordinates} (hx : x ∈ s.rayFace J) {i : Fin 3} (hi : i ∉ J) :
    s.coordinates x i = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hij : i ≠ j := by rintro rfl; exact hi hj
      rw [coordinates_realRay, transition_self]
      simp [hij]
  | zero => simp
  | add y z _ _ hy hz => simp [map_add, hy, hz]
  | smul c y _ hy =>
      change s.coordinates ((c : ℝ) • y) i = 0
      simp [hy]

/-- The face on a subset of rays is described by setting the other
nonnegative simplicial coordinates equal to zero. -/
theorem mem_rayFace_iff (s : Triangle) (J : Set (Fin 3)) (x : RealCoordinates) :
    x ∈ s.rayFace J ↔ x ∈ s.cone ∧ ∀ j ∉ J, s.coordinates x j = 0 := by
  constructor
  · intro hx
    exact ⟨rayFace_le s J hx, fun _ hj => coordinates_eq_zero_of_mem_rayFace s J hx hj⟩
  · rintro ⟨hx, hz⟩
    rw [← generate_coordinates s x, generate_eq_sum]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : j ∈ J
    · exact PointedCone.smul_mem _ (hx j) (PointedCone.subset_hull ⟨j, hj, rfl⟩)
    · rw [hz j hj, zero_smul]
      exact Submodule.zero_mem _

/-- Every ray-subset cone is a face of its maximal cone. -/
theorem rayFace_isFaceOf (s : Triangle) (J : Set (Fin 3)) :
    (s.rayFace J).IsFaceOf s.pointedCone := by
  refine PointedCone.IsFaceOf.of_mem_of_add_mem_left (rayFace_le s J) ?_
  intro x y hx hy hxy
  apply (mem_rayFace_iff s J x).mpr
  refine ⟨hx, fun j hj => ?_⟩
  have hz := (mem_rayFace_iff s J (x + y)).mp hxy |>.2 j hj
  simp only [map_add, Pi.add_apply] at hz
  have hxx := hx j
  have hyy := hy j
  linarith

/-- Any two cones of the fan meet in a face of the first cone. -/
theorem rayFace_inter_isFaceOf_left (s t : Triangle) (I J : Set (Fin 3)) :
    (s.rayFace I ⊓ t.rayFace J).IsFaceOf (s.rayFace I) := by
  have h : (s.rayFace I ⊓ t.rayFace J).IsFaceOf s.pointedCone :=
    ((rayFace_isFaceOf s I).inf (rayFace_isFaceOf t J)).trans (cone_inter_isFaceOf_left s t)
  exact (h.isFaceOf_iff_le (rayFace_isFaceOf s I)).mpr inf_le_left

/-- Any two cones of the fan meet in a face of the second cone. -/
theorem rayFace_inter_isFaceOf_right (s t : Triangle) (I J : Set (Fin 3)) :
    (s.rayFace I ⊓ t.rayFace J).IsFaceOf (t.rayFace J) := by
  simpa only [inf_comm] using rayFace_inter_isFaceOf_left t s J I

theorem rayFace_univ (s : Triangle) : s.rayFace univ = s.pointedCone := by
  ext x
  simp [mem_rayFace_iff]

theorem rayFace_empty (s : Triangle) : s.rayFace ∅ = ⊥ := by
  simp [rayFace]

/-- A primitive height-one ray cannot be an interior lattice point of one
of the unimodular faces: membership means it is one of the chosen rays. -/
theorem realRay_mem_rayFace_iff (s t : Triangle) (j : Fin 3) (J : Set (Fin 3)) :
    s.realRay j ∈ t.rayFace J ↔ s.realRay j ∈ t.realRay '' J := by
  constructor
  · intro hx
    have htc : s.realRay j ∈ t.cone := rayFace_le t J hx
    have hn (i : Fin 3) : 0 ≤ transition s t i j := by
      have h := htc i
      rw [coordinates_realRay] at h
      exact_mod_cast h
    obtain ⟨k, hk⟩ := sharedRay_of_transition_nonneg s t j hn
    have hkJ : k ∈ J := by
      by_contra hkJ
      have hz := coordinates_eq_zero_of_mem_rayFace t J hx hkJ
      rw [hk, coordinates_realRay, transition_self] at hz
      norm_num at hz
    exact ⟨k, hkJ, hk.symm⟩
  · intro hx
    exact PointedCone.subset_hull hx

/-- The common-ray description holds for every two cones of the fan,
not only for the maximal ones. -/
theorem rayFace_inter_eq_commonRay_hull (s t : Triangle) (I J : Set (Fin 3)) :
    s.rayFace I ⊓ t.rayFace J =
      PointedCone.hull ℝ ((s.realRay '' I) ∩ (t.realRay '' J)) := by
  apply le_antisymm
  · intro x hx
    have hxcone : x ∈ s.cone := rayFace_le s I hx.1
    have hface : (s.pointedCone ⊓ t.rayFace J).IsFaceOf s.pointedCone :=
      ((PointedCone.IsFaceOf.refl s.pointedCone).inf (rayFace_isFaceOf t J)).trans
        (cone_inter_isFaceOf_left s t)
    have hsum : (∑ j, s.coordinates x j • s.realRay j) ∈ s.pointedCone ⊓ t.rayFace J := by
      rw [← generate_eq_sum, generate_coordinates]
      exact ⟨hxcone, hx.2⟩
    rw [← generate_coordinates s x, generate_eq_sum]
    apply Submodule.sum_mem
    intro j _
    by_cases hjzero : s.coordinates x j = 0
    · rw [hjzero, zero_smul]
      exact Submodule.zero_mem _
    · have hjpos : 0 < s.coordinates x j := lt_of_le_of_ne (hxcone j) (Ne.symm hjzero)
      have hjI : j ∈ I := by
        by_contra hjI
        exact hjzero (coordinates_eq_zero_of_mem_rayFace s I hx.1 hjI)
      have hray := hface.mem_of_sum_smul_mem (fun k => realRay_mem_cone s k)
        hxcone hsum j hjpos
      exact PointedCone.smul_mem _ (hxcone j) (PointedCone.subset_hull
        ⟨⟨j, hjI, rfl⟩, (realRay_mem_rayFace_iff s t j J).mp hray.2⟩)
  · apply Submodule.span_le.mpr
    intro x hx
    exact ⟨PointedCone.subset_hull hx.1, PointedCone.subset_hull hx.2⟩

/-- The intersection is itself one of the specified cones, obtained by
retaining precisely those source rays which also occur in the target face. -/
theorem rayFace_inter_eq_rayFace (s t : Triangle) (I J : Set (Fin 3)) :
    s.rayFace I ⊓ t.rayFace J =
      s.rayFace {j | j ∈ I ∧ s.realRay j ∈ t.realRay '' J} := by
  rw [rayFace_inter_eq_commonRay_hull, rayFace]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, ht⟩
    exact ⟨j, ⟨hj, ht⟩, rfl⟩
  · rintro ⟨j, ⟨hj, ht⟩, rfl⟩
    exact ⟨⟨j, hj, rfl⟩, ht⟩

/-- A sum of the omitted simplicial coordinates exposes any face of a
maximal cone, including the maximal cone and the zero cone. -/
theorem rayFace_isExposed (s : Triangle) (J : Set (Fin 3)) :
    IsExposed ℝ (s.cone : Set RealCoordinates) (s.rayFace J : Set RealCoordinates) := by
  classical
  let l : RealCoordinates →ₗ[ℝ] ℝ :=
    ∑ j ∈ Finset.univ.filter (fun j => j ∉ J), (LinearMap.proj j).comp s.coordinates
  have hl (x : RealCoordinates) : l x =
      ∑ j ∈ Finset.univ.filter (fun j => j ∉ J), s.coordinates x j := by
    simp [l]
  have hn {x : RealCoordinates} (hx : x ∈ s.cone) : 0 ≤ l x := by
    rw [hl]
    exact Finset.sum_nonneg fun j _ => hx j
  have hz {x : RealCoordinates} (hx : x ∈ s.cone) :
      l x = 0 ↔ ∀ j ∉ J, s.coordinates x j = 0 := by
    rw [hl, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hx j)]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro _
  refine ⟨-l.toContinuousLinearMap, ?_⟩
  ext x
  change (x ∈ s.rayFace J) ↔
    x ∈ s.cone ∧ ∀ y ∈ s.cone, -l y ≤ -l x
  rw [mem_rayFace_iff]
  constructor
  · rintro ⟨hx, hcoords⟩
    have hzero := (hz hx).mpr hcoords
    refine ⟨hx, fun y hy => ?_⟩
    rw [hzero]
    linarith [hn hy]
  · rintro ⟨hx, hmax⟩
    have h := hmax 0 (zero_mem_cone s)
    rw [map_zero] at h
    exact ⟨hx, (hz hx).mp (le_antisymm (by linarith) (hn hx))⟩

/-- Every two cones of the fan meet in an exposed face of the first. -/
theorem rayFace_inter_isExposed_left (s t : Triangle) (I J : Set (Fin 3)) :
    IsExposed ℝ (s.rayFace I : Set RealCoordinates)
      ((s.rayFace I ⊓ t.rayFace J : PointedCone ℝ RealCoordinates) : Set RealCoordinates) := by
  rw [rayFace_inter_eq_rayFace]
  apply (rayFace_isExposed s {j | j ∈ I ∧ s.realRay j ∈ t.realRay '' J}).mono
    (rayFace_le s I)
  change s.rayFace {j | j ∈ I ∧ s.realRay j ∈ t.realRay '' J} ≤ s.rayFace I
  rw [← rayFace_inter_eq_rayFace]
  exact inf_le_left

/-- Every two cones of the fan meet in an exposed face of the second. -/
theorem rayFace_inter_isExposed_right (s t : Triangle) (I J : Set (Fin 3)) :
    IsExposed ℝ (t.rayFace J : Set RealCoordinates)
      ((s.rayFace I ⊓ t.rayFace J : PointedCone ℝ RealCoordinates) : Set RealCoordinates) := by
  simpa only [inf_comm] using rayFace_inter_isExposed_left t s J I

end Wikipedia.HopfProblem.ToricFan.Triangle
