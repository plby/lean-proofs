import Wikipedia.NoExoticSixSphere.CompactSupportDirectedOpenCover
import Wikipedia.NoExoticSixSphere.CompactSupportDualityGluing

/-!
# Directed-open-union closure for the original compact-support cap

Actual compact-support and singular-homology representatives lift to
cover members. The compact carrier of a bounding chain detects zero
in a larger member, where the original cap is injective. Thus the
actual cap bijections and above-dimension vanishing pass to the union.
No homology inclusion is assumed injective, and no replacement groups
or arbitrary comparison maps are introduced.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMap

open CompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  {ι : Type*} [Nonempty ι] (U : ι → Set M) [∀ i, ChartedSpace E (U i)]
  (hU : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
  (hcover : ⋃ i, U i = Set.univ)

include hU hdir hcover

/-- Injective actual caps on the directed cover detect zero in the original ambient group. -/
theorem eq_zero_of_directed_cap_zero (p q : ℕ) (h : p + q = n + 3)
    (hD : ∀ i, Function.Injective (dualityMap (E := E) n (U i) p q h))
    (a : Cohomology M p) (ha : dualityMap (E := E) n M p q h a = 0) : a = 0 := by
  obtain ⟨i, b, rfl⟩ := exists_directed_cover_representative U hU hdir hcover p a
  have hi : modHomologyMap 2 (subtypeInclusion (U i)) q
      (dualityMap (E := E) n (U i) p q h b) = 0 :=
    (dualityMap_openInclusion (E := E) n (U i) (hU i) p q h b).symm.trans ha
  obtain ⟨j, hij, hj⟩ := DirectedOpenCover.homology_eventually_zero U hU hdir hcover
    (ModuleCat.of ℤ (ZMod 2)) i q (dualityMap (E := E) n (U i) p q h b) hi
  let f := subsetInclusion hij
  let hf := subsetInclusion_isOpenEmbedding hij (hU i)
  have hb : openMap f hf p b = 0 := hD j
    ((dualityMap_openEmbedding (E := E) n f hf p q h b).trans
      (hj.trans (dualityMap (E := E) n (U j) p q h).map_zero.symm))
  exact (inclusion_subsetInclusion hij (hU i) (hU j) p b).symm.trans
    ((congrArg (inclusion (U j) (hU j) p) hb).trans (inclusion (U j) (hU j) p).map_zero)

/-- Original cap bijectivity passes from all members of a directed open cover to its union. -/
theorem bijective_of_directed_cover (p q : ℕ) (h : p + q = n + 3)
    (hD : ∀ i, Function.Bijective (dualityMap (E := E) n (U i) p q h)) :
    Function.Bijective (dualityMap (E := E) n M p q h) := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply eq_zero_of_directed_cap_zero (E := E) n U hU hdir hcover p q h (fun i => (hD i).1)
    exact ((dualityMap (E := E) n M p q h).map_sub a b).trans (sub_eq_zero.mpr hab)
  · intro a
    obtain ⟨i, b, hb⟩ := DirectedOpenCover.exists_homology_class U hU hdir hcover
      (ModuleCat.of ℤ (ZMod 2)) q a
    obtain ⟨c, hc⟩ := (hD i).2 b
    refine ⟨inclusion (U i) (hU i) p c, ?_⟩
    exact (dualityMap_openInclusion (E := E) n (U i) (hU i) p q h c).trans
      ((congrArg (modHomologyMap 2 (subtypeInclusion (U i)) q) hc).trans hb)

/-- The complete actual cap-duality property is closed under directed open covers. -/
theorem Duality.of_directed_cover (hD : ∀ i, Duality (E := E) n (U i)) :
    Duality (E := E) n M :=
  ⟨fun p q h => bijective_of_directed_cover (E := E) n U hU hdir hcover p q h
      (fun i => (hD i).1 p q h),
    fun p hp => subsingleton_of_directed_cover U hU hdir hcover p (fun i => (hD i).2 p hp)⟩

end NoExoticSixSphere.CompactSupportCapMap
