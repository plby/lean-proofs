import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegular
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularTorsion
import Wikipedia.HopfProblem.SpecialPeriodsModularTopology

/-!
# The exact exceptional set of the triangle action

Properness gives finite stabilizers.  The reduced-word torsion theorem then
puts each nonidentity stabilizing element in a conjugate cyclic factor.
The explicit Cayley rotations identify its unique fixed point, so the
nonregular set is exactly the union of the two elliptic-center orbits.
It is closed, discrete and countable, and its complement is path connected.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleGeometricAction
  triangleGeometricAction_properlyDiscontinuous triangleGeometricAction_continuous

theorem triangleGenerator₁_ne_one : triangleGenerator₁ ≠ 1 := by
  intro h
  have ho := triangleGenerator₁_order
  simp [h] at ho

theorem triangleGenerator₂_ne_one : triangleGenerator₂ ≠ 1 := by
  intro h
  have ho := triangleGenerator₂_order
  simp [h] at ho

theorem triangle_generator₁_pow_apply (n : ℕ) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₁ ^ n) z =
      Triangle.generatorOneSL ^ n • z := by
  rw [map_pow, triangleGeometricRepresentation_generator₁]
  exact Triangle.generatorOnePerm_pow_apply n z

theorem triangle_generator₂_pow_apply (n : ℕ) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₂ ^ n) z =
      Triangle.generatorTwoSL ^ n • z := by
  rw [map_pow, triangleGeometricRepresentation_generator₂]
  exact Triangle.generatorTwoPerm_pow_apply n z

theorem triangle_generator₁_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₁ ^ n) z = z ↔
      z = Triangle.centerOne := by
  rw [triangle_generator₁_pow_apply]
  exact Triangle.generatorOne_pow_fixed_iff n hn hn' z

theorem triangle_generator₂_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₂ ^ n) z = z ↔
      z = Triangle.centerTwo := by
  rw [triangle_generator₂_pow_apply]
  exact Triangle.generatorTwo_pow_fixed_iff n hn hn' z

private theorem triangle_conjugate_fixed_iff (g h : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation (h * g * h⁻¹) z = z ↔
      triangleGeometricRepresentation g (triangleGeometricRepresentation h⁻¹ z) =
        triangleGeometricRepresentation h⁻¹ z := by
  change (h * g * h⁻¹) • z = z ↔ g • (h⁻¹ • z) = h⁻¹ • z
  constructor
  · intro hz
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun x : ℍ => h⁻¹ • x) hz
  · intro hz
    simpa only [mul_smul, smul_inv_smul] using congrArg (fun x : ℍ => h • x) hz

/-- A conjugate nonidentity order-three rotation fixes exactly the
corresponding translated elliptic center. -/
theorem triangle_conjugate_generator₁_fixed_iff (h : TriangleGroup)
    (n : ℕ) (hn : 0 < n) (hn' : n < 3) (z : ℍ) :
    triangleGeometricRepresentation (h * triangleGenerator₁ ^ n * h⁻¹) z = z ↔
      z = triangleGeometricRepresentation h Triangle.centerOne := by
  rw [triangle_conjugate_fixed_iff, triangle_generator₁_pow_fixed_iff n hn hn']
  change h⁻¹ • z = Triangle.centerOne ↔ z = h • Triangle.centerOne
  exact inv_smul_eq_iff

/-- The corresponding exact fixed-point formula for the order-four factor. -/
theorem triangle_conjugate_generator₂_fixed_iff (h : TriangleGroup)
    (n : ℕ) (hn : 0 < n) (hn' : n < 4) (z : ℍ) :
    triangleGeometricRepresentation (h * triangleGenerator₂ ^ n * h⁻¹) z = z ↔
      z = triangleGeometricRepresentation h Triangle.centerTwo := by
  rw [triangle_conjugate_fixed_iff, triangle_generator₂_pow_fixed_iff n hn hn']
  change h⁻¹ • z = Triangle.centerTwo ↔ z = h • Triangle.centerTwo
  exact inv_smul_eq_iff

theorem triangle_centerOne_not_regular : Triangle.centerOne ∉ triangleRegularLocus := by
  intro h
  rw [mem_triangleRegularLocus_iff] at h
  exact triangleGenerator₁_ne_one (h triangleGenerator₁
    ((triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix))

theorem triangle_centerTwo_not_regular : Triangle.centerTwo ∉ triangleRegularLocus := by
  intro h
  rw [mem_triangleRegularLocus_iff] at h
  exact triangleGenerator₂_ne_one (h triangleGenerator₂
    ((triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix))

/-- The two actual elliptic orbits, in the original upper half-plane. -/
def triangleEllipticSet : Set ℍ :=
  range (fun g : TriangleGroup => triangleGeometricRepresentation g Triangle.centerOne) ∪
    range (fun g : TriangleGroup => triangleGeometricRepresentation g Triangle.centerTwo)

/-- The regular domain is exactly the complement of the two elliptic orbits. -/
theorem triangleRegularLocus_eq_compl_ellipticSet :
    triangleRegularLocus = triangleEllipticSetᶜ := by
  ext z
  constructor
  · intro hz hze
    rcases hze with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact triangle_centerOne_not_regular
        ((triangleRegularLocus_invariant g Triangle.centerOne).mp hz)
    · exact triangle_centerTwo_not_regular
        ((triangleRegularLocus_invariant g Triangle.centerTwo).mp hz)
  · intro hz g hg
    by_contra hgne
    obtain ⟨h, n, hn, hn', hgh⟩ | ⟨h, n, hn, hn', hgh⟩ :=
      triangle_nontrivial_isOfFinOrder_eq_conjugate_generator_power g
        (triangle_isOfFinOrder_of_fixed g z hg) hgne
    · rw [hgh] at hg
      exact hz (Or.inl ⟨h, ((triangle_conjugate_generator₁_fixed_iff h n hn hn' z).mp hg).symm⟩)
    · rw [hgh] at hg
      exact hz (Or.inr ⟨h, ((triangle_conjugate_generator₂_fixed_iff h n hn hn' z).mp hg).symm⟩)

/-- Proper discontinuity makes every compact part of an orbit finite. -/
theorem triangle_orbit_inter_compact_finite (a : ℍ) {K : Set ℍ} (hK : IsCompact K) :
    (range (fun g : TriangleGroup => triangleGeometricRepresentation g a) ∩ K).Finite := by
  have hf : {g : TriangleGroup | triangleGeometricRepresentation g a ∈ K}.Finite := by
    simpa only [image_singleton, singleton_inter_nonempty, triangleGeometricAction_smul] using
      (finite_disjoint_inter_image (Γ := TriangleGroup) (isCompact_singleton (x := a)) hK)
  convert hf.image (fun g : TriangleGroup => triangleGeometricRepresentation g a) using 1
  ext z
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, hg⟩

theorem triangleEllipticSet_inter_compact_finite {K : Set ℍ} (hK : IsCompact K) :
    (triangleEllipticSet ∩ K).Finite := by
  rw [triangleEllipticSet, union_inter_distrib_right]
  exact (triangle_orbit_inter_compact_finite Triangle.centerOne hK).union
    (triangle_orbit_inter_compact_finite Triangle.centerTwo hK)

/-- The deleted elliptic points have no accumulation point in the
upper half-plane, including at regular points. -/
theorem triangleEllipticSet_closed_discrete :
    IsClosed triangleEllipticSet ∧ IsDiscrete triangleEllipticSet := by
  rw [isClosed_and_discrete_iff]
  intro z
  obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
  have hf := triangleEllipticSet_inter_compact_finite hK
  have hf' : ((triangleEllipticSet ∩ K) ∩ ({z} : Set ℍ)ᶜ).Finite :=
    hf.subset inter_subset_left
  have hU : ((triangleEllipticSet ∩ K) ∩ ({z} : Set ℍ)ᶜ)ᶜ ∈ 𝓝 z :=
    hf'.isClosed.isOpen_compl.mem_nhds (by simp)
  rw [disjoint_principal_right]
  filter_upwards [nhdsWithin_le_nhds hKz, nhdsWithin_le_nhds hU,
    self_mem_nhdsWithin] with y hyK hyU hyz
  intro hyE
  exact hyU ⟨⟨hyE, hyK⟩, hyz⟩

theorem triangleEllipticSet_isClosed : IsClosed triangleEllipticSet :=
  triangleEllipticSet_closed_discrete.1

theorem triangleEllipticSet_isDiscrete : IsDiscrete triangleEllipticSet :=
  triangleEllipticSet_closed_discrete.2

theorem triangleEllipticSet_countable : triangleEllipticSet.Countable :=
  (HereditarilyLindelofSpace.isLindelof triangleEllipticSet).countable_of_isDiscrete
    triangleEllipticSet_isDiscrete

/-- Deleting the two discrete elliptic orbits leaves a path-connected domain. -/
theorem triangleRegularLocus_isPathConnected : IsPathConnected triangleRegularLocus := by
  rw [triangleRegularLocus_eq_compl_ellipticSet]
  exact upperHalfPlane_compl_isPathConnected_of_countable triangleEllipticSet_countable

instance triangleRegularPoint_pathConnected : PathConnectedSpace TriangleRegularPoint :=
  isPathConnected_iff_pathConnectedSpace.mp triangleRegularLocus_isPathConnected

instance triangleRegularQuotient_pathConnected : PathConnectedSpace TriangleRegularQuotient :=
  triangleRegularProject_surjective.pathConnectedSpace triangleRegularProject_covering.continuous

end Wikipedia.HopfProblem.SpecialPeriods
