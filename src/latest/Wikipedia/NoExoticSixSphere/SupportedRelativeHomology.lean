import Wikipedia.NoExoticSixSphere.RelativeModExcision
import Wikipedia.NoExoticSixSphere.ModTwoLocalClass

/-!
# Relative homology supported in an actual subset

The group supported in `K` is the original relative homology `H(M, M \ K)`.
Restriction to a smaller subset and evaluation at a point are induced by
the actual identity maps of pairs. These are the maps needed to formulate
and assemble a fundamental class; no global class is assumed here.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

/-- The native relative complex of the complement of the specified support. -/
abbrev Complex (A : ModuleCat.{0} ℤ) (K : Set M) := RelativeCoefficients.complex A Kᶜ

/-- Its actual relative homology, not a module prescribed by the subset's dimension. -/
abbrev Homology (A : ModuleCat.{0} ℤ) (K : Set M) (n : ℕ) := (Complex A K).homology n

/-- Restrict support along the original identity map of pairs. -/
def restrictChain (A : ModuleCat.{0} ℤ) {K L : Set M} (h : K ⊆ L) :
    Complex A L ⟶ Complex A K :=
  RelativeCoefficients.mapChain A (ContinuousMap.id M)
    (show Set.MapsTo (ContinuousMap.id M) Lᶜ Kᶜ from fun _ hy hx => hy (h hx))

theorem restrictChain_refl (A : ModuleCat.{0} ℤ) (K : Set M) :
    restrictChain A (Set.Subset.refl K) = 𝟙 (Complex A K) :=
  RelativeCoefficients.mapChain_id A Kᶜ

theorem restrictChain_trans (A : ModuleCat.{0} ℤ) {K L N : Set M}
    (hKL : K ⊆ L) (hLN : L ⊆ N) :
    restrictChain A (hKL.trans hLN) = restrictChain A hLN ≫ restrictChain A hKL := by
  exact RelativeCoefficients.mapChain_comp A (ContinuousMap.id M) _ (ContinuousMap.id M) _

/-- The actual restriction homomorphism on supported relative homology. -/
abbrev restrict (A : ModuleCat.{0} ℤ) {K L : Set M} (h : K ⊆ L) (n : ℕ) :
    Homology A L n →ₗ[ℤ] Homology A K n := homologyLinearMap (restrictChain A h) n

theorem restrict_refl (A : ModuleCat.{0} ℤ) (K : Set M) (n : ℕ) :
    restrict A (Set.Subset.refl K) n = LinearMap.id := by
  change homologyLinearMap _ n = _
  rw [restrictChain_refl]
  exact congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_id (Complex A K) n)

theorem restrict_trans (A : ModuleCat.{0} ℤ) {K L N : Set M}
    (hKL : K ⊆ L) (hLN : L ⊆ N) (n : ℕ) :
    restrict A (hKL.trans hLN) n = (restrict A hKL n).comp (restrict A hLN n) := by
  change homologyLinearMap _ n = _
  rw [restrictChain_trans, homologyLinearMap_comp]

/-- Evaluation at a point is restriction to its singleton support. -/
def evaluate (A : ModuleCat.{0} ℤ) (K : Set M) (x : M) (hx : x ∈ K) (n : ℕ) :
    Homology A K n →ₗ[ℤ] (RelativeCoefficients.complex A ({x}ᶜ : Set M)).homology n :=
  restrict A (Set.singleton_subset_iff.mpr hx) n

/-- Support restriction preserves the actual local evaluation map. -/
theorem evaluate_restrict (A : ModuleCat.{0} ℤ) {K L : Set M} (h : K ⊆ L)
    (x : M) (hx : x ∈ K) (n : ℕ) :
    (evaluate A K x hx n).comp (restrict A h n) = evaluate A L x (h hx) n :=
  (restrict_trans A (Set.singleton_subset_iff.mpr hx) h n).symm

/-- Coefficient change acts on the same actual support complement. -/
abbrev change (A B : ModuleCat.{0} ℤ) (r : A ⟶ B) (K : Set M) (n : ℕ) :
    Homology A K n →ₗ[ℤ] Homology B K n :=
  homologyLinearMap (RelativeCoefficients.change r Kᶜ) n

theorem restrict_change (A B : ModuleCat.{0} ℤ) (r : A ⟶ B)
    {K L : Set M} (h : K ⊆ L) (n : ℕ) :
    (restrict B h n).comp (change A B r L n) =
      (change A B r K n).comp (restrict A h n) := by
  have he := congrArg (fun k => homologyLinearMap k n)
    (RelativeCoefficients.change_mapChain r (ContinuousMap.id M)
      (show Set.MapsTo (ContinuousMap.id M) Lᶜ Kᶜ from fun _ hy hx => hy (h hx)))
  simp only [homologyLinearMap_comp] at he
  exact he

theorem evaluate_change (A B : ModuleCat.{0} ℤ) (r : A ⟶ B) (K : Set M)
    (x : M) (hx : x ∈ K) (n : ℕ) :
    (evaluate B K x hx n).comp (change A B r K n) =
      (change A B r {x} n).comp (evaluate A K x hx n) :=
  restrict_change A B r (Set.singleton_subset_iff.mpr hx) n

end NoExoticSixSphere.SupportedRelativeHomology

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace E M]

/-- An actual relative class is fundamental on `K` when its original local evaluations
are the constructed nonzero local classes. Existence is not included in this definition. -/
def IsFundamentalOn (K : Set M) (c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3)) : Prop :=
  ∀ (x : M) (hx : x ∈ K), evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) c =
    ModTwoLocalClass.manifoldClass (E := E) n x

/-- The original restriction of a fundamental relative class is fundamental on a smaller set. -/
theorem IsFundamentalOn.restrict {K L : Set M} (h : K ⊆ L)
    {c : Homology (ModuleCat.of ℤ (ZMod 2)) L (n + 3)} (hc : IsFundamentalOn (E := E) n L c) :
    IsFundamentalOn (E := E) n K (restrict (ModuleCat.of ℤ (ZMod 2)) h (n + 3) c) := by
  intro x hx
  have he := LinearMap.congr_fun
    (evaluate_restrict (ModuleCat.of ℤ (ZMod 2)) h x hx (n + 3)) c
  exact he.trans (hc x (h hx))

/-- A fundamental relative class on a nonempty actual support cannot be zero. -/
theorem IsFundamentalOn.ne_zero {K : Set M}
    {c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3)} (hc : IsFundamentalOn (E := E) n K c)
    (hK : K.Nonempty) : c ≠ 0 := by
  obtain ⟨x, hx⟩ := hK
  intro he
  have h := hc x hx
  rw [he, map_zero] at h
  exact ModTwoLocalClass.manifoldClass_ne_zero (E := E) n x h.symm

end NoExoticSixSphere.SupportedRelativeHomology
