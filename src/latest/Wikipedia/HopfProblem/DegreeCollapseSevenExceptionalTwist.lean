import Wikipedia.HopfProblem.DegreeCollapseSevenPrimitiveFreeTwist

/-!
# Select the actual even twist in the exceptional case

The coefficient is selected on the fixed original exterior. The genuine
shrunk products preserve its meridian and section under the constructed
radial homology equivalence. The actual new surgery half therefore contains
an explicitly primitive free class with one-quarter finite torsion, or has
the old finite cardinality and contains an exact order-four class.
This is a first surgery, not yet a decreasing
sequence or a proof that the next filling satisfies the iteration inputs.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris SphereHomology
open FramedAttachingProduct UnitSurgery ExteriorTwist

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  {A : FramedAttachingProduct e a f} (hA : A.radius = 2) (T : TimeData A)
  [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

theorem exists_shrunk_twist_with_primitive_free_or_order_four (v s : Sphere 3)
    (hfamily : ∀ j : ℤ, Nonempty (ShrunkEvenTwist A v j))
    (h2 : ∀ x : SingularHomology (OldPositiveHalf A T) 3, (2 : ℤ) • x = 0)
    (hc : singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) ≠ 0)
    (hn : ∃ x, meridianCharacter A hA T s x ≠ 0)
    (hz : meridianCharacter A hA T s
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
        (unitSphereTopClass 2)) = 0) :
    ∃ (j : ℤ) (Q : ShrunkEvenTwist A v j),
      (∃ x : SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3,
        ∃ σ : SingularHomology
          (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3 →+ ℤ,
          σ x = 1 ∧ Finite σ.ker ∧ (∀ y : σ.ker, (2 : ℤ) • y = 0) ∧
            4 * Nat.card σ.ker = Nat.card (SingularHomology (OldPositiveHalf A T) 3)) ∨
      (Finite (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
       Nat.card (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) =
          Nat.card (SingularHomology (OldPositiveHalf A T) 3) ∧
       ∃ x : SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3,
          (4 : ℤ) • x = 0 ∧ (2 : ℤ) • x ≠ 0) := by
  obtain ⟨h, hh⟩ := exists_half_meridian_of_exponent_two A hA T s h2 hn
  obtain ⟨j, hj⟩ := exists_even_twist_double_section A hA T v s h2 hz
  obtain ⟨Q⟩ := hfamily j
  let : Subsingleton (SingularHomology (OldPositiveHalf Q.untwisted (Q.timeData hA T)) 4) :=
    inferInstanceAs (Subsingleton (SingularHomology (OldPositiveHalf A T) 4))
  let : Finite (SingularHomology (OldPositiveHalf Q.untwisted (Q.timeData hA T)) 3) :=
    inferInstanceAs (Finite (SingularHomology (OldPositiveHalf A T) 3))
  let E : SingularHomology (HalfExterior Q.untwisted Q.untwisted_radius (Q.timeData hA T)) 3
      ≃ₗ[ℤ] SingularHomology (HalfExterior A hA T) 3 :=
    scaledExteriorHomologyEquiv A hA Q.untwisted Q.untwisted_radius
      Q.scale Q.scale_pos Q.scale_le_one Q.scaled_tube T
  have hEμ : E (halfMeridianClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) s) =
      halfMeridianClass A hA T s :=
    scaledExterior_meridian_class A hA Q.untwisted Q.untwisted_radius
      Q.scale Q.scale_pos Q.scale_le_one Q.scaled_tube T s
  have hEα : E (halfSectionClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) v) =
      halfSectionClass A hA T v :=
    scaledExterior_section_class A hA Q.untwisted Q.untwisted_radius
      Q.scale Q.scale_pos Q.scale_le_one Q.scaled_tube T v
  have hh' : (2 : ℤ) • E.symm h =
      halfMeridianClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) s := by
    apply E.injective
    rw [map_zsmul, E.apply_symm_apply, hEμ]
    exact hh
  let x := halfTwistedNewMap Q.untwisted Q.untwisted_radius (Q.timeData hA T)
    Q.twisted Q.twisted_radius Q.family Q.twisted_tube (E.symm h)
  have hc' : singularHomologyMap
      (halfBoundaryPair Q.untwisted Q.untwisted_radius (Q.timeData hA T)).attachingSphere 3
        (unitSphereTopClass 2) ≠ 0 := by
    change singularHomologyMap
      (halfBoundaryPair Q.untwisted Q.untwisted_radius
        (scaledTimeData A hA Q.untwisted Q.untwisted_radius
          Q.scale Q.scale_pos Q.scale_le_one Q.scaled_tube T)).attachingSphere 3
            (unitSphereTopClass 2) ≠ 0
    rw [scaled_attachingSphere]
    exact hc
  refine ⟨j, Q, ?_⟩
  rcases hj with hj | hj
  · left
    have hβ : (2 : ℤ) •
        (halfSectionClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) v +
          (2 * j) • halfMeridianClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) s) =
            0 := by
      apply E.injective
      rw [map_zsmul, map_add, map_zsmul, hEα, hEμ, map_zero]
      exact hj
    exact ⟨x, halfTwist_primitive_free_part Q.untwisted Q.untwisted_radius (Q.timeData hA T)
      Q.twisted Q.twisted_radius Q.family Q.twisted_tube v s (2 * j)
      Q.family_multiplier h2 (E.symm h) hh' hc' hβ⟩
  · right
    have hβ : (2 : ℤ) •
        (halfSectionClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) v +
          (2 * j) • halfMeridianClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) s) =
        (2 : ℤ) • halfMeridianClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) s := by
      apply E.injective
      rw [map_zsmul, map_add, map_zsmul, hEα, hEμ, map_zsmul, hEμ]
      exact hj
    obtain ⟨hfinite, hcard⟩ := halfTwist_card_eq Q.untwisted Q.untwisted_radius (Q.timeData hA T)
      Q.twisted Q.twisted_radius Q.family Q.twisted_tube v s (2 * j) Q.family_multiplier hβ
    exact ⟨hfinite, hcard, x,
      halfTwist_order_four Q.untwisted Q.untwisted_radius (Q.timeData hA T)
        Q.twisted Q.twisted_radius Q.family Q.twisted_tube v s (2 * j)
          Q.family_multiplier (E.symm h) hh' hc' hβ⟩

theorem exists_shrunk_twist_with_infinite_or_order_four (v s : Sphere 3)
    (hfamily : ∀ j : ℤ, Nonempty (ShrunkEvenTwist A v j))
    (h2 : ∀ x : SingularHomology (OldPositiveHalf A T) 3, (2 : ℤ) • x = 0)
    (hc : singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) ≠ 0)
    (hn : ∃ x, meridianCharacter A hA T s x ≠ 0)
    (hz : meridianCharacter A hA T s
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
        (unitSphereTopClass 2)) = 0) :
    ∃ (j : ℤ) (Q : ShrunkEvenTwist A v j),
      (∃ x : SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3,
          Injective (fun n : ℤ ↦ n • x)) ∨
      (Finite (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
       Nat.card (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) =
          Nat.card (SingularHomology (OldPositiveHalf A T) 3) ∧
       ∃ x : SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3,
          (4 : ℤ) • x = 0 ∧ (2 : ℤ) • x ≠ 0) := by
  obtain ⟨j, Q, hout⟩ := exists_shrunk_twist_with_primitive_free_or_order_four
    hA T v s hfamily h2 hc hn hz
  refine ⟨j, Q, ?_⟩
  rcases hout with ⟨x, σ, hx, _⟩ | hout
  · exact Or.inl ⟨x, IntegerSplit.coefficient_injective σ x hx⟩
  · exact Or.inr hout

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
