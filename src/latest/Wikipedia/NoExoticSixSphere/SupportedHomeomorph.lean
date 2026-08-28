import Wikipedia.NoExoticSixSphere.RelativeCoefficientHomeomorph
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology
import Wikipedia.NoExoticSixSphere.ModTwoLocalClassUniqueness

/-!
# Supported classes under actual homeomorphisms

Homeomorphisms carrying one specified support to another give isomorphisms
of the actual supported relative groups. Their original point-evaluation
squares commute. Thus they carry mod-two fundamental relative classes to
fundamental relative classes without an orientation choice.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem homeomorph_complement_mapsTo (h : X ≃ₜ Y) {K : Set X} {L : Set Y}
    (hK : ∀ x, x ∈ K ↔ h x ∈ L) : Set.MapsTo h Kᶜ Lᶜ :=
  fun x hx hy => hx ((hK x).mpr hy)

theorem homeomorph_complement_symm_mapsTo (h : X ≃ₜ Y) {K : Set X} {L : Set Y}
    (hK : ∀ x, x ∈ K ↔ h x ∈ L) : Set.MapsTo h.symm Lᶜ Kᶜ := by
  intro y hy hx
  apply hy
  simpa only [h.apply_symm_apply] using (hK (h.symm y)).mp hx

/-- The native supported homology isomorphism induced by the supplied homeomorphism. -/
def homeomorphEquiv (A : ModuleCat.{0} ℤ) (h : X ≃ₜ Y) {K : Set X} {L : Set Y}
    (hK : ∀ x, x ∈ K ↔ h x ∈ L) (n : ℕ) : Homology A K n ≃ₗ[ℤ] Homology A L n :=
  RelativeCoefficients.homeomorphEquiv A h (homeomorph_complement_mapsTo h hK)
    (homeomorph_complement_symm_mapsTo h hK) n

/-- The actual chain-level evaluation square commutes. -/
theorem homeomorph_evaluation_chain (A : ModuleCat.{0} ℤ) (h : X ≃ₜ Y)
    {K : Set X} {L : Set Y} (hK : ∀ x, x ∈ K ↔ h x ∈ L) (x : X) (hx : x ∈ K) :
    RelativeCoefficients.mapChain A (h : C(X, Y)) (homeomorph_complement_mapsTo h hK) ≫
        restrictChain A (Set.singleton_subset_iff.mpr ((hK x).mp hx)) =
      restrictChain A (Set.singleton_subset_iff.mpr hx) ≫
        RelativeCoefficients.mapChain A (h : C(X, Y))
          (RelativeCoefficients.point_complement_mapsTo h x) := by
  change RelativeCoefficients.mapChain A (h : C(X, Y)) _ ≫
      RelativeCoefficients.mapChain A (ContinuousMap.id Y) _ =
    RelativeCoefficients.mapChain A (ContinuousMap.id X) _ ≫
      RelativeCoefficients.mapChain A (h : C(X, Y)) _
  rw [← RelativeCoefficients.mapChain_comp, ← RelativeCoefficients.mapChain_comp]
  rfl

/-- Point evaluation commutes with the actual supported homeomorphism isomorphism. -/
theorem evaluate_homeomorphEquiv (A : ModuleCat.{0} ℤ) (h : X ≃ₜ Y)
    {K : Set X} {L : Set Y} (hK : ∀ x, x ∈ K ↔ h x ∈ L) (x : X) (hx : x ∈ K) (n : ℕ) :
    (evaluate A L (h x) ((hK x).mp hx) n).comp (homeomorphEquiv A h hK n).toLinearMap =
      (RelativeCoefficients.localHomeomorphEquiv A h x n).toLinearMap.comp
        (evaluate A K x hx n) := by
  have he := congrArg (fun k => homologyLinearMap k n)
    (homeomorph_evaluation_chain A h hK x hx)
  simp only [homologyLinearMap_comp] at he
  exact he

end NoExoticSixSphere.SupportedRelativeHomology

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]
  [ChartedSpace E X] [ChartedSpace E Y]

/-- Every actual local homeomorphism isomorphism preserves the canonical mod-two class. -/
theorem localHomeomorphEquiv_manifoldClass (h : X ≃ₜ Y) (x : X) :
    RelativeCoefficients.localHomeomorphEquiv (ModuleCat.of ℤ (ZMod 2)) h x (n + 3)
        (ModTwoLocalClass.manifoldClass (E := E) n x) =
      ModTwoLocalClass.manifoldClass (E := E) n (h x) :=
  ModTwoLocalClass.injective_map_manifoldClass (E := E) n x (h x)
    (RelativeCoefficients.localHomeomorphEquiv (ModuleCat.of ℤ (ZMod 2)) h x (n + 3)).toLinearMap
    (RelativeCoefficients.localHomeomorphEquiv (ModuleCat.of ℤ (ZMod 2)) h x (n + 3)).injective

/-- A homeomorphism of actual supports transports a fundamental relative class. -/
theorem IsFundamentalOn.homeomorph (h : X ≃ₜ Y) {K : Set X} {L : Set Y}
    (hK : ∀ x, x ∈ K ↔ h x ∈ L)
    {c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3)} (hc : IsFundamentalOn (E := E) n K c) :
    IsFundamentalOn (E := E) n L (homeomorphEquiv (ModuleCat.of ℤ (ZMod 2)) h hK (n + 3) c) := by
  intro y hy
  obtain ⟨x, rfl⟩ := h.surjective y
  have hx := (hK x).mpr hy
  have he := LinearMap.congr_fun
    (evaluate_homeomorphEquiv (ModuleCat.of ℤ (ZMod 2)) h hK x hx (n + 3)) c
  exact he.trans ((congrArg
    (RelativeCoefficients.localHomeomorphEquiv (ModuleCat.of ℤ (ZMod 2)) h x (n + 3))
    (hc x hx)).trans (localHomeomorphEquiv_manifoldClass (E := E) n h x))

end NoExoticSixSphere.SupportedRelativeHomology
