import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFineAcyclic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmooth

/-!
# Actual smooth-function acyclicity on noncompact manifolds

A genuine smooth partition of unity supplies the locally finite closed
supports and the literal local finite-sum identity.  This proves local
fineness of the actual smooth complex-function sheaf.  The genuine Ext
vanishing theorem therefore applies on finite-dimensional Hausdorff
sigma-compact real smooth manifolds, including the noncompact complex
line and native complex affine plane.  Holomorphic functions are not
asserted to form a fine sheaf.
-/

noncomputable section

open Set Function TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type}

/-- Any finite list containing all nonzero terms gives the actual
partition sum at the selected point. -/
theorem partition_finset_sum (ρ : SmoothPartitionOfUnity ι I M univ)
    (x : M) (s : Finset ι) (hs : ∀ i ∉ s, ρ i x = 0) :
    s.sum (fun i => ρ i x) = 1 := by
  classical
  have hsupport : support (fun i => ρ i x) ⊆ (s : Set ι) := by
    intro i hi
    by_contra hn
    exact hi (hs i hn)
  exact (finsum_eq_sum_of_support_subset _ hsupport).symm.trans (ρ.sum_eq_one (mem_univ x))

/-- The same actual finite-sum identity for the complex-valued smooth multipliers. -/
theorem complexify_partition_finset_sum (ρ : SmoothPartitionOfUnity ι I M univ)
    (x : M) (s : Finset ι) (hs : ∀ i ∉ s, ρ i x = 0) :
    s.sum (fun i => complexify I M (ρ i)) x = 1 := by
  change (ContMDiffMap.evalRingHom x : GlobalFunction I M →+* ℂ)
    (s.sum (fun i => complexify I M (ρ i))) = 1
  rw [map_sum]
  change s.sum (fun i => (ρ i x : ℂ)) = 1
  exact_mod_cast partition_finset_sum I M ρ x s hs

/-- A genuine arbitrary-index smooth partition supplies the full actual
locally finite decomposition of the smooth-function sheaf. -/
def locallyFinitePartitionDecomposition {U : ι → Opens M}
    (ρ : SmoothPartitionOfUnity ι I M univ)
    (hρ : ρ.IsSubordinate (fun i => (U i : Set M))) :
    LocallyFiniteDecomposition (additiveSheaf I M) U where
  operator i := multiplier I M (complexify I M (ρ i))
  support i := tsupport (ρ i)
  support_closed _ := isClosed_closure
  subordinate := hρ
  zeroOutside i := by
    intro V hV
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ContMDiffMap.ext
    intro x
    have hzero : ρ i (x : M) = 0 :=
      notMem_support.mp (fun hx => hV x.property (subset_tsupport (ρ i) hx))
    change (ρ i (x : M) : ℂ) * f x = 0
    rw [hzero, Complex.ofReal_zero, zero_mul]
  locallyFinite := ρ.locallyFinite.closure
  localTotal V s hs := by
    intro W hWV
    have hm : s.sum (fun i => multiplier I M (complexify I M (ρ i))) =
        multiplier I M (s.sum (fun i => complexify I M (ρ i))) :=
      (map_sum (multiplierRingHom I M) (fun i => complexify I M (ρ i)) s).symm
    change (s.sum (fun i => multiplier I M (complexify I M (ρ i))) -
      𝟙 (additiveSheaf I M)).hom.app (op W) = 0
    rw [hm]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ContMDiffMap.ext
    intro x
    have hzero (i : ι) (hi : i ∉ s) : ρ i (x : M) = 0 :=
      notMem_support.mp (fun hx => Set.disjoint_left.mp (hs i hi)
        (hWV x.property) (subset_tsupport (ρ i) hx))
    change s.sum (fun i => complexify I M (ρ i)) (x : M) * f x - f x = 0
    rw [complexify_partition_finset_sum I M ρ (x : M) s hzero, one_mul, sub_self]

/-- The actual smooth complex-function sheaf is locally fine on every
finite-dimensional Hausdorff sigma-compact smooth real manifold. -/
theorem locallyFine [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] : LocallyFine (additiveSheaf I M) := by
  intro ι U hU
  have hcover : (univ : Set M) ⊆ ⋃ i, (U i : Set M) := by
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i => (U i : Set M)) (fun i => (U i).isOpen) hcover
  exact ⟨locallyFinitePartitionDecomposition I M ρ hρ⟩

/-- Genuine positive-degree Ext cohomology of this actual smooth sheaf
vanishes, without requiring the manifold to be compact. -/
theorem higher_subsingleton [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (additiveSheaf I M) (n + 1)) :=
  (locallyFine I M).higher_subsingleton (scalarEnd I M) n

/-- Actual smooth complex-valued functions on the noncompact complex
line have zero genuine cohomology in every positive degree. -/
theorem complexLine_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (additiveSheaf 𝓘(ℝ, ℂ) ℂ) (n + 1)) :=
  higher_subsingleton 𝓘(ℝ, ℂ) ℂ n

/-- Actual smooth complex-valued functions on the noncompact native
complex affine plane have zero genuine cohomology in every positive degree. -/
theorem complexPlane_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (additiveSheaf 𝓘(ℝ, Fin 2 → ℂ) (Fin 2 → ℂ)) (n + 1)) :=
  higher_subsingleton 𝓘(ℝ, Fin 2 → ℂ) (Fin 2 → ℂ) n

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions
