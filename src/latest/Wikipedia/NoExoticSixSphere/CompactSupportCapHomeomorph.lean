import Wikipedia.NoExoticSixSphere.CompactSupportHomeomorph
import Wikipedia.NoExoticSixSphere.CompactSupportCapOpenEmbedding

/-!
# Bijectivity of the actual compact-support cap is preserved by homeomorphisms

Both vertical maps use the constructed mod-two fundamental classes on
the original charted spaces. The homeomorphism acts through its original
homology map and original compact-support extension, and their checked
cap square transports bijectivity.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  [ChartedSpace E X] [ChartedSpace E Y]

/-- The cap of the original target manifold is bijective if that of a homeomorphic source is. -/
theorem bijective_of_homeomorph (e : X ≃ₜ Y) (p q : ℕ) (h : p + q = n + 3)
    (hD : Function.Bijective (dualityMap (E := E) n X p q h)) :
    Function.Bijective (dualityMap (E := E) n Y p q h) := by
  let C := CompactSupportCohomology.homeomorphEquiv e p
  let H := modHomologyHomeomorphEquiv 2 e q
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := C.surjective a
    obtain ⟨b, rfl⟩ := C.surjective b
    apply congrArg C
    apply hD.1
    apply H.injective
    exact (dualityMap_openEmbedding (E := E) n (e : C(X, Y)) e.isOpenEmbedding p q h a).symm
      |>.trans (hab.trans
        (dualityMap_openEmbedding (E := E) n (e : C(X, Y)) e.isOpenEmbedding p q h b))
  · intro b
    obtain ⟨a, ha⟩ := hD.2 (H.symm b)
    refine ⟨C a, ?_⟩
    exact (dualityMap_openEmbedding (E := E) n (e : C(X, Y)) e.isOpenEmbedding p q h a).trans
      ((congrArg H ha).trans (H.apply_symm_apply b))

/-- Homeomorphism invariance concerns the actual cap maps, not just abstractly equal ranks. -/
theorem bijective_iff_homeomorph (e : X ≃ₜ Y) (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (dualityMap (E := E) n X p q h) ↔
      Function.Bijective (dualityMap (E := E) n Y p q h) :=
  ⟨bijective_of_homeomorph (E := E) n e p q h,
    bijective_of_homeomorph (E := E) n e.symm p q h⟩

end NoExoticSixSphere.CompactSupportCapMap
