import Wikipedia.HopfProblem.DegreeCollapseSevenTwistedExteriorPresentation
import Wikipedia.HopfProblem.DegreeCollapseEvenTorsionRemainder

/-!
# A strict torsion decrease for the actual twisted surgery half

The cyclic-index calculation is applied to the genuine common exterior
homology and the actual old/new quotient equivalences. Fourth-homology
vanishing of the old half supplies the infinite-order meridian. A nonzero
smaller relation coefficient then proves that the new third homology is
finite with strictly smaller cardinality. All hypotheses are retained.
-/

noncomputable section

open Function AddSubgroup
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization OrthogonalPaths
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology CyclicSurgeryIndex

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

theorem halfOld_card (s : Sphere 3) :
    Nat.card (SingularHomology (OldPositiveHalf A T) 3) =
      (zmultiples (halfMeridianClass A hA T s)).index := by
  calc
    _ = Nat.card (SingularHomology (HalfExterior A hA T) 3 ⧸
        LinearMap.range (singularHomologyMap (halfMeridianMap A hA T s) 3)) :=
      (Nat.card_congr (halfExteriorOldQuotientEquiv A hA T s).toEquiv).symm
    _ = Nat.card (SingularHomology (HalfExterior A hA T) 3 ⧸
        Submodule.span ℤ {halfMeridianClass A hA T s}) := by
      rw [sphere_linear_range]
      rfl
    _ = _ := quotient_span_card _

theorem halfMeridian_coefficient_injective
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)] (s : Sphere 3) :
    Injective (fun k : ℤ ↦ k • halfMeridianClass A hA T s) := by
  intro k l h
  have hs : k • unitSphereTopClass 2 = l • unitSphereTopClass 2 :=
    halfMeridian_injective A hA T s (by simpa [halfMeridianClass] using h)
  have he := congrArg (unitSphereHomologyTopEquiv 2) hs
  simpa using he

variable (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (ρ : C(Sphere 3, OrthogonalOperators 4))
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))

theorem halfTwistedNew_card (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3, singularHomologyMap (column v ρ) 3 c = j • c) :
    Nat.card (SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3) =
      (zmultiples (halfSectionClass A hA T v + j • halfMeridianClass A hA T s)).index := by
  calc
    _ = Nat.card (SingularHomology (HalfExterior A hA T) 3 ⧸
        Submodule.span ℤ {halfSectionClass A hA T v + j • halfMeridianClass A hA T s}) :=
      (Nat.card_congr (halfTwistedNewQuotientEquiv A hA T B hB ρ ht v s j hρ).toEquiv).symm
    _ = _ := quotient_span_card _

variable [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]

theorem halfTwist_card_relation (v s : Sphere 3) (l l' j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3, singularHomologyMap (column v ρ) 3 c = j • c)
    (hrel : l • halfSectionClass A hA T v + l' • halfMeridianClass A hA T s = 0)
    (hn : l' - l * j ≠ 0) :
    l.natAbs * Nat.card (SingularHomology
      (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3) =
        (l' - l * j).natAbs * Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  rw [halfTwistedNew_card A hA T B hB ρ ht v s j hρ, halfOld_card A hA T s]
  exact relation_index _ _ (halfMeridian_coefficient_injective A hA T s) l (l' - l * j) hn
    (twisted_meridian_relation A hA T v s l l' j hrel)

theorem halfTwist_strict_decrease [Finite (SingularHomology (OldPositiveHalf A T) 3)]
    (v s : Sphere 3) (l l' j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3, singularHomologyMap (column v ρ) 3 c = j • c)
    (hrel : l • halfSectionClass A hA T v + l' • halfMeridianClass A hA T s = 0)
    (hn : l' - l * j ≠ 0) (hsmall : (l' - l * j).natAbs < l.natAbs) :
    Finite (SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3) ∧
      Nat.card (SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3) <
        Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  have hfinite : (zmultiples (halfMeridianClass A hA T s)).index ≠ 0 := by
    rw [← halfOld_card A hA T s]
    exact Nat.card_pos.ne'
  have hi := strict_index_decrease _ _ (halfMeridian_coefficient_injective A hA T s)
    l (l' - l * j) hn hsmall (twisted_meridian_relation A hA T v s l l' j hrel) hfinite
  have hc := halfTwistedNew_card A hA T B hB ρ ht v s j hρ
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hc]
    exact hi.1
  · rw [hc, halfOld_card A hA T s]
    exact hi.2

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist
