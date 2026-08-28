import Wikipedia.NoExoticSixSphere.RoundDiskBoundaryParametrization
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The actual round-disk quotient is a reduced suspension quotient

For a map collapsing exactly the disk boundary, the boundary-segment
evaluation collapses exactly the two endpoint slices and the chosen
basepoint line. All other fibers are singletons, and the map is onto.
These are statements about the original continuous maps and their actual
fibers, not an assumed suspension equivalence.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.RoundDiskSuspensionQuotient

open RoundDiskBoundarySegments

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y]
  (f : C(Disk (E := E), Y)) (z : Y)
  (hbase : ∀ x, f x = z ↔ x.val ∈ sphere (0 : E) 1)
  (hfiber : ∀ x y, f x = f y → f x = z ∨ x = y)
  (hsurj : Function.Surjective f)

def evaluation (b : Boundary (E := E)) : C(unitInterval × Boundary (E := E), Y) :=
  f.comp (point b)

def exceptional (b : Boundary (E := E)) : Set (unitInterval × Boundary (E := E)) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = b}

include hbase in
theorem evaluation_eq_base_iff (b : Boundary (E := E)) (p : unitInterval × Boundary (E := E)) :
    evaluation f b p = z ↔ p ∈ exceptional b := by
  change f (point b p) = z ↔ _
  rw [hbase, point_mem_sphere_iff]
  rfl

include hbase hfiber in
theorem evaluation_eq_iff (b : Boundary (E := E))
    (p q : unitInterval × Boundary (E := E)) :
    evaluation f b p = evaluation f b q ↔
      p = q ∨ p ∈ exceptional b ∧ q ∈ exceptional b := by
  constructor
  · intro he
    by_cases hp : p ∈ exceptional b
    · exact Or.inr ⟨hp, (evaluation_eq_base_iff f z hbase b q).mp
        (he.symm.trans ((evaluation_eq_base_iff f z hbase b p).mpr hp))⟩
    · rcases hfiber (point b p) (point b q) he with hz | heq
      · exact False.elim (hp ((evaluation_eq_base_iff f z hbase b p).mp hz))
      · have ht₀ : p.1 ≠ 0 := fun h ↦ hp (Or.inl h)
        have ht₁ : p.1 ≠ 1 := fun h ↦ hp (Or.inr (Or.inl h))
        have hs : p.2 ≠ b := fun h ↦ hp (Or.inr (Or.inr h))
        have h₀ : 0 < (p.1 : ℝ) :=
          lt_of_le_of_ne p.1.property.1 (fun h ↦ ht₀ (Subtype.ext h.symm))
        have h₁ : (p.1 : ℝ) < 1 :=
          lt_of_le_of_ne p.1.property.2 (fun h ↦ ht₁ (Subtype.ext h))
        obtain ⟨ht, hs⟩ := point_injective_interior b p.2 q.2 p.1 q.1 h₀ h₁ hs heq
        exact Or.inl (Prod.ext ht hs)
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · exact ((evaluation_eq_base_iff f z hbase b p).mpr hp).trans
        ((evaluation_eq_base_iff f z hbase b q).mpr hq).symm

include hbase hsurj in
theorem evaluation_surjective (b : Boundary (E := E)) :
    Function.Surjective (evaluation f b) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  by_cases hx : x.val ∈ sphere (0 : E) 1
  · refine ⟨(0, b), ?_⟩
    exact ((evaluation_eq_base_iff f z hbase b (0, b)).mpr (Or.inl rfl)).trans
      ((hbase x).mpr hx).symm
  · have hball : x.val ∈ ball (0 : E) 1 := by
      have hle := mem_closedBall.mp x.property
      have hne : dist x.val 0 ≠ 1 := fun h ↦ hx (mem_sphere.mpr h)
      exact lt_of_le_of_ne hle hne
    obtain ⟨t, s, _, _, _, he⟩ := exists_point_of_mem_ball b hball
    refine ⟨(t, s), congrArg f (Subtype.ext he)⟩

variable [FiniteDimensional ℝ E] [T2Space Y]

include hbase hsurj in
theorem evaluation_isQuotientMap (b : Boundary (E := E)) :
    IsQuotientMap (evaluation f b) :=
  IsQuotientMap.of_surjective_continuous (evaluation_surjective f z hbase hsurj b)
    (evaluation f b).continuous

end NoExoticSixSphere.RoundDiskSuspensionQuotient
