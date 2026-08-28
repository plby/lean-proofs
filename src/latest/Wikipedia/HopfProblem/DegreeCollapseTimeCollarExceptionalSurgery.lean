import Wikipedia.HopfProblem.DegreeCollapseSevenNextReduction
import Wikipedia.HopfProblem.DegreeCollapseSevenPrimitiveSuccessor
import Wikipedia.HopfProblem.DegreeCollapseSevenExceptionalTwist

/-!
# The actual exceptional surgery and both successors for any preserved collar

The original half pairing is nondegenerate without a reflected-double
presentation. Its actual meridian comparison supplies the character
inputs for the exceptional twist. Both resulting native targets then
have the previously constructed actual successors. This is the general
collared reduction trichotomy needed by geometric iteration.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open NoExoticSixSphere GLOrthonormalization SevenSurgery
open SingularMayerVietoris SphereHomology
open FramedAttachingProduct UnitSurgery ExteriorTwist

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

def HasExceptionalSurgery (t : M → ℝ) (v : Sphere 3) : Prop :=
  ∃ (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
    (T : TimeData A) (_hT : T.time = t) (j : ℤ) (Q : ShrunkEvenTwist A v j),
    SimplyConnectedSpace
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) ∧
    Subsingleton (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 2) ∧
    ((∃ x : SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3,
      ∃ σ : SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3 →+ ℤ,
        σ x = 1 ∧ Finite σ.ker ∧ (∀ y : σ.ker, (2 : ℤ) • y = 0) ∧
        4 * Nat.card σ.ker = Nat.card (SingularHomology (NonnegativeHalf t) 3) ∧
        (letI := targetChartedSpace Q.twisted Q.twisted_radius;
         letI := target_isManifold Q.twisted Q.twisted_radius;
         letI := compactSpace_target Q.twisted Q.twisted_radius;
         HasPrimitiveReduction (inducedEmbedding Q.twisted Q.twisted_radius)
           (normalFraming Q.twisted Q.twisted_radius)
           (timeFunction Q.twisted Q.twisted_radius (Q.twistedTimeData hA T))
           (Nat.card σ.ker))) ∨
    (Finite (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
     Subsingleton (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 4) ∧
     Nat.card (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) =
       Nat.card (SingularHomology (NonnegativeHalf t) 3) ∧
     (∃ x : SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3,
        (4 : ℤ) • x = 0 ∧ (2 : ℤ) • x ≠ 0) ∧
     ∀ w : Sphere 3,
       letI := targetChartedSpace Q.twisted Q.twisted_radius;
       letI := target_isManifold Q.twisted Q.twisted_radius;
       letI := compactSpace_target Q.twisted Q.twisted_radius;
       HasStrictReduction (inducedEmbedding Q.twisted Q.twisted_radius)
         (normalFraming Q.twisted Q.twisted_radius)
         (timeFunction Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) w))

variable {B : Type} [TopologicalSpace B] {t : M → ℝ} (C : TimeCollar t B)
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]
  [SimplyConnectedSpace (NonnegativeHalf t)]
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]
  (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))

include ht hreg in
theorem exceptionalSurgery_of_zero_diagonal
    (c : SingularHomology (NonnegativeHalf t) 3) (hc : c ≠ 0)
    (hd : ∀ x : SingularHomology (NonnegativeHalf t) 3, C.halfLinking (E := Vector 7) x x = 0)
    (v : Sphere 3) : HasExceptionalSurgery e a t v := by
  classical
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := Vector 7) M
  let : Subsingleton (SingularHomology (NonnegativeHalf t) 2) := C.half_homology_subsingleton 2
  let : Subsingleton (SingularHomology (NonnegativeHalf t) 4) := C.half_homology_subsingleton 4
  let : Finite (SingularHomology (NonnegativeHalf t) 3) := C.half_homology_finite 3
  obtain ⟨f, hf, hi, hdf, hpos, hclass⟩ := C.exists_positive_homology_core e a c
  obtain ⟨R⟩ := EuclideanEmbedding.nonempty_tubularRetraction e a
  obtain ⟨A, hA, T, hT, hfamily⟩ := exists_positive_even_twist_family
    e a R f hf hi hdf t ht hreg hpos v
  subst t
  have hcore : (closedBoundaryPair A hA).attachingSphere = f := by
    apply ContinuousMap.ext
    intro s
    exact A.tube_core s
  have hclosed : singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3
      (unitSphereTopClass 2) = singularHomologyMap (halfInclusion T.time) 3 c := by
    rw [hcore]
    exact hclass
  have hc' : singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) = c := by
    apply C.halfInclusion_homology_injective 3
    change singularHomologyMap (halfToClosed A T) 3
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)) = _
    rw [halfToClosed_attachingClass]
    exact hclosed
  obtain ⟨k, hk, he⟩ := collaredMeridianCharacter_linking A hA T C v
  have hpair (b : SingularHomology (NonnegativeHalf T.time) 3) :
      k • C.halfLinking (E := Vector 7) c b = meridianCharacter A hA T v b := by
    have hb := he b
    rw [hclosed] at hb
    exact hb
  have hn : ∃ b, meridianCharacter A hA T v b ≠ 0 := by
    obtain ⟨b, hb⟩ : ∃ b, C.halfLinking (E := Vector 7) c b ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (C.halfLinking_left_nondegenerate (E := Vector 7) c h)
    refine ⟨b, ?_⟩
    rw [← hpair]
    rcases Int.isUnit_iff.mp hk with rfl | rfl
    · simpa only [one_smul] using hb
    · simpa only [neg_one_smul, neg_ne_zero] using hb
  have hz : meridianCharacter A hA T v
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
        (unitSphereTopClass 2)) = 0 := by
    rw [hc', ← hpair, hd c, smul_zero]
  have h2 : ∀ x : SingularHomology (OldPositiveHalf A T) 3, (2 : ℤ) • x = 0 := by
    intro x
    simpa only [two_zsmul] using C.half_add_self_eq_zero_of_zero_diagonal (E := Vector 7) hd x
  have hcn : singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) ≠ 0 := by rw [hc']; exact hc
  obtain ⟨j, Q, hout⟩ := exists_shrunk_twist_with_primitive_free_or_order_four
    hA T v v hfamily h2 hcn hn hz
  let : SimplyConnectedSpace (OldPositiveHalf Q.twisted (Q.twistedTimeData hA T)) :=
    inferInstanceAs (SimplyConnectedSpace (NonnegativeHalf T.time))
  have hinv := Q.low_connectivity hA T
  refine ⟨f, A, hA, T, rfl, j, Q, hinv.1, hinv.2, ?_⟩
  rcases hout with ⟨x, σ, hx, hfinite, htwo, hcard⟩ | ⟨hfinite, hcard, x, hx4, hx2⟩
  · left
    let : Finite σ.ker := hfinite
    exact ⟨x, σ, hx, hfinite, htwo, hcard,
      primitive_reduction_after_free_coordinate Q.twisted Q.twisted_radius
        (Q.twistedTimeData hA T) C σ x hx htwo⟩
  · right
    let : Finite (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) := hfinite
    exact ⟨hfinite, Q.fourth_homology_of_finite hA T, hcard, ⟨x, hx4, hx2⟩,
      fun w ↦ strict_reduction_after_double_ne_zero Q.twisted Q.twisted_radius
        (Q.twistedTimeData hA T) C x hx2 w⟩

include C ht hreg in
theorem torsion_surgery_or_zero (v : Sphere 3) :
    HasStrictReduction e a t v ∨ HasExceptionalSurgery e a t v ∨
      Subsingleton (SingularHomology (NonnegativeHalf t) 3) := by
  classical
  by_cases hd : ∀ x : SingularHomology (NonnegativeHalf t) 3,
      C.halfLinking (E := Vector 7) x x = 0
  · right
    by_cases hz : Subsingleton (SingularHomology (NonnegativeHalf t) 3)
    · exact Or.inr hz
    · let : Nontrivial (SingularHomology (NonnegativeHalf t) 3) :=
        not_subsingleton_iff_nontrivial.mp hz
      obtain ⟨c, hc⟩ := exists_ne (0 : SingularHomology (NonnegativeHalf t) 3)
      exact Or.inl (C.exceptionalSurgery_of_zero_diagonal e a ht hreg c hc hd v)
  · obtain ⟨c, hc⟩ := not_forall.mp hd
    exact Or.inl (C.strictReduction_of_diagonal e a ht hreg c hc v)

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
