import Wikipedia.NoExoticSixSphere.CompactEuclideanFundamentalClass
import Wikipedia.NoExoticSixSphere.CompactEuclideanSupportVanishing
import Wikipedia.NoExoticSixSphere.SupportedLocalZeroNeighborhood

/-!
# Detection and uniqueness on arbitrary compact Euclidean supports

Lift the actual class to a finite-convex support neighborhood. If its
evaluations vanish on the original compact set, the genuine local
boundary witnesses make those evaluations vanish on a neighborhood.
A smaller finite-convex support lies in that neighborhood. Its proved
detection theorem makes the restricted class zero, and the original
restriction map carries this zero back to the starting compact support.
-/

noncomputable section

open CategoryTheory Set

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Zero point evaluations detect zero on every actual compact Euclidean support. -/
theorem compactEuclidean_eq_zero (K : Set E) (hK : IsCompact K)
    (a : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3))
    (ha : ∀ (x : E) (hx : x ∈ K), evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) a = 0) :
    a = 0 := by
  let A := ModuleCat.of ℤ (ZMod 2)
  obtain ⟨U, hU, hKU, hlift⟩ := exists_lift_neighborhood A K (n + 3) a
  obtain ⟨L, _, hKintL, hLU⟩ := exists_finiteConvex_support_neighborhood n K U hK hU hKU
  have hKL : K ⊆ L := hKintL.trans interior_subset
  obtain ⟨b, hb⟩ := hlift L hLU hKL
  have hbzero : ∀ (x : E) (hx : x ∈ K), evaluate A L x (hKL hx) (n + 3) b = 0 := by
    intro x hx
    have he := LinearMap.congr_fun (evaluate_restrict A hKL x hx (n + 3)) b
    exact he.symm.trans ((congrArg (evaluate A K x hx (n + 3)) hb).trans (ha x hx))
  obtain ⟨V, hV, hKV, hVzero⟩ := exists_open_zero_evaluations A hKL (n + 3) b hbzero
  obtain ⟨N, hN, hKintN, hNVL⟩ := exists_finiteConvex_support_neighborhood n K
    (V ∩ interior L) hK (hV.inter isOpen_interior) (fun x hx => ⟨hKV hx, hKintL hx⟩)
  have hKN : K ⊆ N := hKintN.trans interior_subset
  have hNL : N ⊆ L := fun x hx => interior_subset (hNVL hx).2
  have hNzero : restrict A hNL (n + 3) b = 0 := by
    apply hN.detected
    intro x hx
    have he := LinearMap.congr_fun (evaluate_restrict A hNL x hx (n + 3)) b
    exact (he.trans (hVzero x (hNL hx) (hNVL hx).1)).trans (map_zero _).symm
  have he : restrict A hKN (n + 3) (restrict A hNL (n + 3) b) = a :=
    (LinearMap.congr_fun (restrict_trans A hKN hNL (n + 3)) b).symm.trans hb
  exact he.symm.trans ((congrArg (restrict A hKN (n + 3)) hNzero).trans (map_zero _))

/-- Equal original point evaluations detect equal original compactly supported classes. -/
theorem compactEuclidean_detected (K : Set E) (hK : IsCompact K)
    (a b : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3))
    (hab : ∀ (x : E) (hx : x ∈ K),
      evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) a =
        evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) b) : a = b := by
  apply sub_eq_zero.mp
  apply compactEuclidean_eq_zero n K hK (a - b)
  intro x hx
  rw [map_sub, hab x hx, sub_self]

/-- Every compact Euclidean support has all the proved support properties. -/
theorem compactEuclidean_fundamentalSupport (K : Set E) (hK : IsCompact K) :
    CompactFundamentalSupport (E := E) n K where
  compact := hK
  above k hk := compactEuclidean_above_subsingleton n K hK k hk
  detected a b hab := compactEuclidean_detected n K hK a b hab
  fundamental := compactEuclidean_exists_fundamentalClass n K hK

/-- The fundamental relative class of an arbitrary compact Euclidean support is unique. -/
theorem compactEuclidean_existsUnique_fundamentalClass (K : Set E) (hK : IsCompact K) :
    ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3), IsFundamentalOn (E := E) n K c :=
  CompactFundamentalSupport.existsUnique n (compactEuclidean_fundamentalSupport n K hK)

end NoExoticSixSphere.SupportedRelativeHomology
