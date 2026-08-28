import Wikipedia.NoExoticSixSphere.SphereSuspensionArfTransport
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension
import Wikipedia.NoExoticSixSphere.TwoConnectedCoefficientReduction
import Wikipedia.NoExoticSixSphere.SphereHomologyGroups

/-!
# Finite suspension preserves the original regular-fiber Arf invariant

Construct a globally smooth representative at every finite stage. Its
regular fiber retains the native atlas, the actual iterated equatorial
inclusion, and the original defining-equation Arf invariant. Connectivity
is transported along the actual fiber diffeomorphism, not assumed for
the newly constructed fiber.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization RegularSphereFiber

theorem piTwo_subsingleton_of_homeomorph {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [SimplyConnectedSpace X]
    (D : X ≃ₜ Y) (x : X) [Subsingleton (π_ 2 X x)] (y : Y) :
    Subsingleton (π_ 2 Y y) := by
  let : SimplyConnectedSpace Y := D.symm.toHomotopyEquiv.simplyConnectedSpace
  let := TwoConnectedCoefficients.secondHomology_subsingleton x
  let : Subsingleton (SingularHomology Y 2) :=
    (homeomorphHomologyEquiv D.symm 2).injective.subsingleton
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv y).injective.subsingleton

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (hd : m = n + 6) (a₀ : Sphere m)
  [SimplyConnectedSpace {x : Sphere m // f x = b}]
  (x : {x : Sphere m // f x = b}) [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]

def SmoothIterateArfWitness (j : ℕ) : Prop :=
    ∃ g : C(Sphere (m + j), Sphere (n + j)),
      ∃ hg : ContMDiff (𝓡 (m + j)) (𝓡 (n + j)) ∞ g,
      ∃ hgreg : ∀ y, g y = equators n j b → Function.Surjective
        (mfderiv (𝓡 (m + j)) (𝓡 (n + j)) g y),
      (iterate f j).Homotopic g ∧
      letI := regularFiberAtlas f hf b hreg 6 (by simpa using hd);
      letI := regularFiber_isManifold f hf b hreg 6 _;
      letI := fiber_compact f b;
      letI := regularFiberAtlas g hg (equators n j b) hgreg 6 (by
        simp only [finrank_euclideanSpace_fin]; omega);
      letI := regularFiber_isManifold g hg (equators n j b) hgreg 6 (by
        simp only [finrank_euclideanSpace_fin]; omega);
      letI := fiber_compact g (equators n j b);
      ∃ D : {x : Sphere m // f x = b} ≃ₘ⟮𝓡 6, 𝓡 6⟯
        {y : Sphere (m + j) // g y = equators n j b},
        (∀ v, (D v).val = equators m j v.val) ∧
        ∃ hSC : SimplyConnectedSpace {y : Sphere (m + j) // g y = equators n j b},
        ∃ hπ : Subsingleton (π_ 2 {y : Sphere (m + j) // g y = equators n j b} (D x)),
        letI := hSC; letI := hπ;
        ∀ r : (embedding f hf b hreg 6 hd).TubularRetraction,
          ∀ r' : (embedding g hg (equators n j b) hgreg 6 (by omega)).TubularRetraction,
            GeometricArf.invariant (embedding f hf b hreg 6 hd)
              (frame f hf b hreg 6 hd a₀) r x =
            GeometricArf.invariant (embedding g hg (equators n j b) hgreg 6 (by omega))
              (frame g hg (equators n j b) hgreg 6 (by omega) (equators m j a₀)) r' (D x)

theorem smoothIterateArfWitness_zero :
    SmoothIterateArfWitness f hf b hreg hd a₀ x 0 := by
  unfold SmoothIterateArfWitness
  refine ⟨f, hf, hreg, ContinuousMap.Homotopic.refl f, ?_⟩
  let := regularFiberAtlas f hf b hreg 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hreg 6 (by simpa using hd)
  let := fiber_compact f b
  refine ⟨Diffeomorph.refl (𝓡 6) _ ∞, fun _ ↦ rfl,
    (inferInstance : SimplyConnectedSpace {x : Sphere m // f x = b}),
    (inferInstance : Subsingleton (π_ 2 {x : Sphere m // f x = b} x)), ?_⟩
  intro r r'
  exact (StabilizedFramedDiffeomorph.refl (embedding f hf b hreg 6 hd)
    (frame f hf b hreg 6 hd a₀)).geometricArf_eq r r' x x

theorem smoothIterateArfWitness_succ (j : ℕ)
    (ih : SmoothIterateArfWitness f hf b hreg hd a₀ x j) :
    SmoothIterateArfWitness f hf b hreg hd a₀ x (j + 1) := by
  unfold SmoothIterateArfWitness at ih ⊢
  obtain ⟨g, hg, hgreg, H, D, hD, hSC, hπ, hArf⟩ := ih
  have hdg : m + j = (n + j) + 6 := by omega
  let := regularFiberAtlas f hf b hreg 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hreg 6 (by simpa using hd)
  let := fiber_compact f b
  let := regularFiberAtlas g hg (equators n j b) hgreg 6 (by simpa using hdg)
  let := regularFiber_isManifold g hg (equators n j b) hgreg 6 (by simpa using hdg)
  let := fiber_compact g (equators n j b)
  let := hSC
  let := hπ
  obtain ⟨G, hG, HG, hGfiber, hGreg, U, hU, hKU, heq⟩ :=
    exists_smooth_regular_suspension g hg (equators n j b) hgreg
  have hGgerm : ∀ y, g y = equators n j b →
      (G : Sphere ((m + j) + 1) → Sphere ((n + j) + 1))
        =ᶠ[𝓝 (equator (m + j) y)] map g := by
    intro y hy
    have hmem : equator (m + j) y ∈ (map g) ⁻¹' {equator (n + j) (equators n j b)} := by
      change map g (equator (m + j) y) = equator (n + j) (equators n j b)
      rw [map_equator, hy]
    filter_upwards [hU.mem_nhds (hKU hmem)] with z hz
    exact heq hz
  refine ⟨G, hG, hGreg, (map_homotopic H).trans HG, ?_⟩
  let := regularFiberAtlas G hG (equator (n + j) (equators n j b)) hGreg 6 (by
    simp only [finrank_euclideanSpace_fin]; omega)
  let := regularFiber_isManifold G hG (equator (n + j) (equators n j b)) hGreg 6 (by
    simp only [finrank_euclideanSpace_fin]; omega)
  let := fiber_compact G (equator (n + j) (equators n j b))
  let := regularFiberAtlas G hG (equators n (j + 1) b) hGreg 6 (by
    simp only [finrank_euclideanSpace_fin]; omega)
  let E := fiberDiffeomorph g hg (equators n j b) hgreg 6 hdg G hG hGreg hGfiber
  let hSCG : SimplyConnectedSpace {y : Sphere (m + (j + 1)) //
      G y = equator (n + j) (equators n j b)} :=
    E.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let hπG : Subsingleton (π_ 2 {y : Sphere (m + (j + 1)) //
      G y = equator (n + j) (equators n j b)} (E (D x))) :=
    piTwo_subsingleton_of_homeomorph E.toHomeomorph (D x) (E (D x))
  refine ⟨D.trans E, ?_, hSCG, hπG, ?_⟩
  · intro v
    change (E (D v)).val = equator (m + j) (equators m j v.val)
    rw [fiberDiffeomorph_val, hD]
  · intro r r'
    obtain ⟨rg⟩ := (embedding g hg (equators n j b) hgreg 6 hdg).nonempty_tubularRetraction
      (frame g hg (equators n j b) hgreg 6 hdg (equators m j a₀))
    exact (hArf r rg).trans (geometricArf_smoothSuspension g hg (equators n j b) hgreg hdg
      (equators m j a₀) G hG hGreg hGfiber hGgerm (equators m (j + 1) a₀)
        (D x) (E (D x)) rg r')

theorem exists_smooth_iterate_with_original_arf (j : ℕ) :
    SmoothIterateArfWitness f hf b hreg hd a₀ x j := by
  induction j with
  | zero => exact smoothIterateArfWitness_zero f hf b hreg hd a₀ x
  | succ j ih => exact smoothIterateArfWitness_succ f hf b hreg hd a₀ x j ih

end NoExoticSixSphere.SphereMapSuspension
