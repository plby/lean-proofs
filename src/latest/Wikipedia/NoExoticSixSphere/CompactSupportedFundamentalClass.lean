import Wikipedia.NoExoticSixSphere.ManifoldFundamentalClass

/-!
# Compatible fundamental classes for all compact supports

Existence and uniqueness were proved for every compact subset of the
original manifold. We choose those actual classes and prove their
compatibility under the original support restriction maps.
-/

noncomputable section

namespace NoExoticSixSphere.CompactSupportedFundamentalClass

open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- The constructed actual fundamental class on this compact support. -/
def fundamentalClass (K : Set M) (hK : IsCompact K) :
    Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3) :=
  Classical.choose (compactManifold_existsUnique_fundamentalClass (E := E) n K hK)

theorem isFundamentalOn (K : Set M) (hK : IsCompact K) :
    IsFundamentalOn (E := E) n K (fundamentalClass (E := E) n K hK) :=
  (Classical.choose_spec
    (compactManifold_existsUnique_fundamentalClass (E := E) n K hK)).1

theorem unique (K : Set M) (hK : IsCompact K)
    (a : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3))
    (ha : IsFundamentalOn (E := E) n K a) : a = fundamentalClass (E := E) n K hK :=
  (Classical.choose_spec
    (compactManifold_existsUnique_fundamentalClass (E := E) n K hK)).2 a ha

/-- Original restriction sends the larger compact fundamental class to the smaller one. -/
theorem restrict_fundamentalClass {K L : Set M} (h : K ⊆ L)
    (hK : IsCompact K) (hL : IsCompact L) :
    restrict (ModuleCat.of ℤ (ZMod 2)) h (n + 3) (fundamentalClass (E := E) n L hL) =
      fundamentalClass (E := E) n K hK :=
  unique (E := E) n K hK _ ((isFundamentalOn (E := E) n L hL).restrict n h)

/-- On a compact manifold these are the original projections of the global class. -/
theorem fromAbsolute_fundamentalClass [CompactSpace M] (K : Set M) (hK : IsCompact K) :
    fromAbsolute (ModuleCat.of ℤ (ZMod 2)) K (n + 3)
        (ManifoldFundamentalClass.fundamentalClass (E := E) n M) =
      fundamentalClass (E := E) n K hK :=
  unique (E := E) n K hK _
    (ManifoldFundamentalClass.fromAbsolute_isFundamentalOn (E := E) n M K)

end NoExoticSixSphere.CompactSupportedFundamentalClass
