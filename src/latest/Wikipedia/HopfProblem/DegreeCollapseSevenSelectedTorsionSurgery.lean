import Wikipedia.HopfProblem.DegreeCollapseSevenShrunkEvenTwists

/-!
# Select a genuine decreasing surgery from a fixed nondivisible relation

Choose the even coefficient from the original half-exterior relation first.
The constructed family then supplies actual smaller-radius products, full
framing, and the prescribed even twist. Radius comparison retains the same
relation, so the actual twisted half has strictly smaller finite third
homology. Fourth-homology vanishing and nondivisibility remain explicit.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris FramedAttachingProduct UnitSurgery ExteriorTwist

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [T2Space M] [IsManifold (𝓡 7) ∞ M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  {A : FramedAttachingProduct e a f} {v : Sphere 3} {j : ℤ}

theorem ShrunkEvenTwist.strict_decrease (Q : ShrunkEvenTwist A v j)
    (hA : A.radius = 2) (T : TimeData A)
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
    [Finite (SingularHomology (OldPositiveHalf A T) 3)]
    (s : Sphere 3) (l p : ℤ)
    (hrel : l • halfSectionClass A hA T v + p • halfMeridianClass A hA T s = 0)
    (hn : p - l * (2 * j) ≠ 0) (hsmall : (p - l * (2 * j)).natAbs < l.natAbs) :
    Finite (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
      Nat.card (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) <
          Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  let : Subsingleton (SingularHomology (OldPositiveHalf Q.untwisted (Q.timeData hA T)) 4) :=
    inferInstanceAs (Subsingleton (SingularHomology (OldPositiveHalf A T) 4))
  let : Finite (SingularHomology (OldPositiveHalf Q.untwisted (Q.timeData hA T)) 3) :=
    inferInstanceAs (Finite (SingularHomology (OldPositiveHalf A T) 3))
  exact halfTwist_strict_decrease Q.untwisted Q.untwisted_radius (Q.timeData hA T)
    Q.twisted Q.twisted_radius Q.family Q.twisted_tube v s l p (2 * j)
      Q.family_multiplier (Q.preserved_relation hA T s l p hrel) hn hsmall

theorem exists_strict_shrunk_twist (hA : A.radius = 2) (T : TimeData A)
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
    [Finite (SingularHomology (OldPositiveHalf A T) 3)]
    (hfamily : ∀ j : ℤ, Nonempty (ShrunkEvenTwist A v j))
    (s : Sphere 3) (l p : ℤ) (hl : 0 < l) (hp : ¬ l ∣ p)
    (hrel : l • halfSectionClass A hA T v + p • halfMeridianClass A hA T s = 0) :
    ∃ (j : ℤ) (Q : ShrunkEvenTwist A v j),
      Finite (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
        Nat.card (SingularHomology
          (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) <
            Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  obtain ⟨j, hne, hsmall⟩ := CyclicSurgeryIndex.strict_even_remainder l p hl hp
  obtain ⟨Q⟩ := hfamily j
  have he : p - l * (2 * j) = p - 2 * l * j := by ring
  refine ⟨j, Q, Q.strict_decrease hA T s l p hrel ?_ ?_⟩
  · rw [he]
    exact hne
  · rw [he]
    exact hsmall

/-- The positive reference product and all geometric twist choices are constructed.
Only the homological vanishing, finiteness and nondivisible relation remain as premises. -/
theorem exists_positive_reference_with_torsion_reduction (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s, 0 < t (f s)) (v : Sphere 3) :
    ∃ (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A),
      T.time = t ∧
      ∀ (_h4 : Subsingleton (SingularHomology (OldPositiveHalf A T) 4))
        (_h3 : Finite (SingularHomology (OldPositiveHalf A T) 3))
        (s : Sphere 3) (l p : ℤ), 0 < l → ¬ l ∣ p →
        l • halfSectionClass A hA T v + p • halfMeridianClass A hA T s = 0 →
        ∃ (j : ℤ) (Q : ShrunkEvenTwist A v j),
          Finite (SingularHomology
            (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
            Nat.card (SingularHomology
              (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) <
                Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  obtain ⟨A, hA, T, hT, hfamily⟩ :=
    exists_positive_even_twist_family e a R f hf hi hd t ht hreg hpos v
  refine ⟨A, hA, T, hT, ?_⟩
  intro h4 h3 s l p hl hp hrel
  let : Subsingleton (SingularHomology (OldPositiveHalf A T) 4) := h4
  let : Finite (SingularHomology (OldPositiveHalf A T) 3) := h3
  exact exists_strict_shrunk_twist hA T hfamily s l p hl hp hrel

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
