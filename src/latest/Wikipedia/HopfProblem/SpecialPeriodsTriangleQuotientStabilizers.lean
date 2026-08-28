import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBasic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularCentralizersTriangle

/-!
# Exact elliptic stabilizers in the triangle group

Real determinant-one transformations fixing the same upper-half-plane point
are simultaneous rotations in its centered Cayley coordinate.  They commute.
Faithfulness transfers this fact to the actual free product, whose proved
factor-centralizer theorem then identifies the two elliptic stabilizers
exactly.  In particular the two distinguished elliptic orbits are distinct.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleGeometricAction

namespace Triangle

/-- Transformations fixing the same point are simultaneous Cayley rotations. -/
theorem realSLPermutation_commute_of_fixed (A B : SL(2, ℝ)) (a : ℍ)
    (hA : A • a = a) (hB : B • a = a) :
    Commute (realSLPermutation A) (realSLPermutation B) := by
  apply Equiv.ext
  intro z
  apply (cayleyBiholomorph a).injective
  apply Subtype.ext
  change cayleyCoordinate a (A • (B • z)) = cayleyCoordinate a (B • (A • z))
  rw [cayleyCoordinate_smul A a _ hA, cayleyCoordinate_smul B a _ hB,
    cayleyCoordinate_smul B a _ hB, cayleyCoordinate_smul A a _ hA]
  ring

end Triangle

/-- Common fixed points force actual abstract triangle elements to commute. -/
theorem triangle_commute_of_common_fixed (g h : TriangleGroup) (z : ℍ)
    (hg : triangleGeometricRepresentation g z = z)
    (hh : triangleGeometricRepresentation h z = z) : Commute g h := by
  apply triangleGeometricRepresentation_injective
  rw [map_mul, map_mul]
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_has_SL_lift g
  obtain ⟨B, hB⟩ := triangleGeometricRepresentation_has_SL_lift h
  have ha : A • z = z := (congrArg (fun f : Equiv.Perm ℍ => f z) hA).trans hg
  have hb : B • z = z := (congrArg (fun f : Equiv.Perm ℍ => f z) hB).trans hh
  simpa only [hA, hB] using (Triangle.realSLPermutation_commute_of_fixed A B z ha hb).eq

/-- The order-three center has exactly its three cyclic stabilizer elements. -/
theorem triangle_fixed_centerOne_iff (g : TriangleGroup) :
    triangleGeometricRepresentation g Triangle.centerOne = Triangle.centerOne ↔
      ∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n := by
  constructor
  · intro hg
    apply triangleGenerator₁_commute_eq_pow g
    exact triangle_commute_of_common_fixed _ _ Triangle.centerOne
      ((triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix) hg
  · rintro ⟨n, hn, rfl⟩
    clear hn
    rw [triangle_generator₁_pow_apply]
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', mul_smul, ih, Triangle.generatorOne_fix]

/-- The order-four center has exactly its four cyclic stabilizer elements. -/
theorem triangle_fixed_centerTwo_iff (g : TriangleGroup) :
    triangleGeometricRepresentation g Triangle.centerTwo = Triangle.centerTwo ↔
      ∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n := by
  constructor
  · intro hg
    apply triangleGenerator₂_commute_eq_pow g
    exact triangle_commute_of_common_fixed _ _ Triangle.centerTwo
      ((triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix) hg
  · rintro ⟨n, hn, rfl⟩
    clear hn
    rw [triangle_generator₂_pow_apply]
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', mul_smul, ih, Triangle.generatorTwo_fix]

theorem triangle_stabilizer_centerOne :
    MulAction.stabilizer TriangleGroup Triangle.centerOne =
      Subgroup.zpowers triangleGenerator₁ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, _, rfl⟩ := (triangle_fixed_centerOne_iff g).mp hg
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact (triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix

theorem triangle_stabilizer_centerTwo :
    MulAction.stabilizer TriangleGroup Triangle.centerTwo =
      Subgroup.zpowers triangleGenerator₂ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, _, rfl⟩ := (triangle_fixed_centerTwo_iff g).mp hg
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact (triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix

/-- The order-three and order-four centers are in different actual orbits. -/
theorem triangleOrbitCenterOne_ne_centerTwo : triangleOrbitCenterOne ≠ triangleOrbitCenterTwo := by
  intro he
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp he.symm
  have hfix : triangleGeometricRepresentation (g * triangleGenerator₁ * g⁻¹)
      Triangle.centerTwo = Triangle.centerTwo := by
    simpa only [pow_one] using
      (triangle_conjugate_generator₁_fixed_iff g 1 (by norm_num) (by norm_num)
        Triangle.centerTwo).mpr hg.symm
  obtain ⟨n, _, hn⟩ := (triangle_fixed_centerTwo_iff _).mp hfix
  have ho : orderOf (g * triangleGenerator₁ * g⁻¹) = 3 := by
    change orderOf ((MulAut.conj g) triangleGenerator₁) = 3
    exact (orderOf_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective triangleGenerator₁).trans triangleGenerator₁_order
  have hd := orderOf_pow_dvd (x := triangleGenerator₂) n
  rw [← hn, ho, triangleGenerator₂_order] at hd
  norm_num at hd

end Wikipedia.HopfProblem.SpecialPeriods
