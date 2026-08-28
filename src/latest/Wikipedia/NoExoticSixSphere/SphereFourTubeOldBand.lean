import Wikipedia.NoExoticSixSphere.SphereFourTubeRadialBand

/-!
# The original collar inside the tube exterior

The separated old time band embeds unchanged in the new band. Together
with the actual radial band it forms a disjoint open cover. The old
coordinates retain the original inverse collar map exactly.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {M B : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [TopologicalSpace B]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def oldTimeBand (t τ : M → ℝ) (δ : ℝ) : Set (TimeBand τ δ) :=
  {x | t x.val ∈ Ioo (-δ) δ}

theorem timeBand_disjoint_open_cover (hΦ : Φ.source = univ)
    (t τ : C(M, ℝ)) (δ : ℝ)
    (hOld : ∀ x, |t x| < δ → x ∉ closedRegion Φ 2)
    (hsplit : ∀ x, |τ x| < δ → |t x| < δ ∨ x ∈ openRegion Φ (3 / 2)) :
    IsOpen (oldTimeBand t τ δ) ∧ IsOpen (innerTimeBand Φ τ δ) ∧
      Disjoint (oldTimeBand t τ δ) (innerTimeBand Φ τ δ) ∧
      oldTimeBand t τ δ ∪ innerTimeBand Φ τ δ = univ := by
  refine ⟨isOpen_Ioo.preimage (t.continuous.comp continuous_subtype_val),
    isOpen_innerTimeBand Φ hΦ τ δ, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxOld hxNew
    apply hOld x.val (abs_lt.mpr hxOld)
    obtain ⟨p, hp, hpx⟩ := hxNew
    refine ⟨p, ⟨mem_univ _, mem_closedBall_zero_iff.mpr ?_⟩, hpx⟩
    have hnorm := mem_ball_zero_iff.mp hp.2
    linarith
  · ext x
    constructor
    · intro _
      exact mem_univ x
    · intro _
      rcases hsplit x.val (abs_lt.mpr x.property) with hx | hx
      · exact Or.inl (abs_lt.mp hx)
      · exact Or.inr hx

theorem exists_old_time_coordinates (t τ : C(M, ℝ)) (C : TimeCollar t B)
    (δ : ℝ) (hδw : δ ≤ C.width)
    (hOld : ∀ x, |t x| < δ → x ∉ closedRegion Φ 2)
    (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x) :
    ∃ e : oldTimeBand t τ δ ≃ₜ Ioo (-δ) δ × B,
      (∀ x, (e x).1.val = τ x.val.val) ∧
      ∀ p, (e.symm p).val.val = (C.restrictedInverse hδw p).val := by
  let X := oldTimeBand t τ δ
  have heq (x : TimeBand t δ) : τ x.val = t x.val :=
    hout x.val (hOld x.val (abs_lt.mpr x.property))
  have hmem (x : TimeBand t δ) : τ x.val ∈ Ioo (-δ) δ := by
    rw [heq x]
    exact x.property
  let e₀ : X ≃ₜ TimeBand t δ :=
    { toFun := fun x ↦ ⟨x.val.val, x.property⟩
      invFun := fun x ↦ ⟨⟨x.val, hmem x⟩, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk hmem).subtype_mk
        (fun x ↦ x.property) }
  refine ⟨e₀.trans (C.restrictedCoordinates hδw), ?_, fun _ ↦ rfl⟩
  intro x
  exact (heq (e₀ x)).symm

end NoExoticSixSphere.SphereFourTube
