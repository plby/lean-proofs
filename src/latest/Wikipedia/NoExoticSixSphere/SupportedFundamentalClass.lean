import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology
import Wikipedia.NoExoticSixSphere.ModTwoLocalClassUniqueness

/-!
# Construction from the actual evaluation isomorphisms

On a nonempty support whose original point evaluations are bijective, a
class is constructed by lifting the canonical value at one point. It is
nonzero at every point, hence fundamental everywhere, and unique. This
criterion does not assert bijectivity for arbitrary supports.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace E M]

/-- Lifting one nonzero local value gives the unique fundamental relative class,
provided every original evaluation is bijective. -/
theorem existsUnique_fundamentalClass_of_evaluate_bijective (K : Set M) (hK : K.Nonempty)
    (h : ∀ (x : M) (hx : x ∈ K),
      Function.Bijective (evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3))) :
    ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3),
      IsFundamentalOn (E := E) n K c := by
  obtain ⟨x, hx⟩ := hK
  obtain ⟨c, hc⟩ := (h x hx).surjective (ModTwoLocalClass.manifoldClass (E := E) n x)
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, map_zero] at hc
    exact ModTwoLocalClass.manifoldClass_ne_zero (E := E) n x hc.symm
  have hfund : IsFundamentalOn (E := E) n K c := by
    intro y hy
    apply ModTwoLocalClass.eq_manifoldClass_of_ne_zero (E := E) n y
    intro hz
    exact hc0 ((h y hy).injective (hz.trans (map_zero _).symm))
  refine ⟨c, hfund, ?_⟩
  intro d hd
  exact (h x hx).injective ((hd x hx).trans hc.symm)

end NoExoticSixSphere.SupportedRelativeHomology
