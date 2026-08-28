import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCore
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedAnalytic
import Wikipedia.HopfProblem.CoveringVolumeCoordinates
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Identifying the character cocycle bundle with the associated quotient

The line bundle made from local covering sections and the diagonal orbit
quotient are independently constructed spaces. This file identifies them
by explicit inverse maps. In every local covering section, the map is the
usual scalar coordinate on the quotient fibre. Analyticity is checked in
the existing bundle and covering-quotient atlases.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.AssociatedCore

variable {G A B : Type*} [Group G] [MulAction G A]
    [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)

/-- Send a bundle vector to its orbit, using the preferred local covering
section at its base point. -/
def toAssociated (p : (data hq χ).core.TotalSpace) : AssociatedSpace (A := A) χ :=
  associatedMap χ (lift hq p.1 p.1, id (α := ℂ) p.2)

@[simp] theorem projection_toAssociated (p : (data hq χ).core.TotalSpace) :
    projection hq χ (toAssociated hq χ p) = p.1 :=
  lift_project hq p.1 (mem_baseSet hq p.1)

/-- The fibre coordinate in the preferred local covering section gives
the inverse map to the bundle total space. -/
def fromAssociated (p : AssociatedSpace (A := A) χ) : (data hq χ).core.TotalSpace :=
  ⟨projection hq χ p, fibreCoordinate hq χ
    (lift hq (projection hq χ p) (projection hq χ p)) p
    (lift_project hq _ (mem_baseSet hq _)).symm⟩

@[simp] theorem fromAssociated_proj (p : AssociatedSpace (A := A) χ) :
    (fromAssociated hq χ p).proj = projection hq χ p := rfl

@[simp] theorem toAssociated_fromAssociated (p : AssociatedSpace (A := A) χ) :
    toAssociated hq χ (fromAssociated hq χ p) = p :=
  associatedMap_fibreCoordinate hq χ _ p
    (lift_project hq _ (mem_baseSet hq _)).symm

theorem toAssociated_injective : Function.Injective (toAssociated hq χ) := by
  rintro ⟨b, z⟩ ⟨c, w⟩ he
  have hb : b = c := by
    simpa only [projection_toAssociated] using congrArg (projection hq χ) he
  subst c
  have hz : z = w := associatedMap_fibre_injective hq χ (lift hq b b) he
  cases hz
  rfl

@[simp] theorem fromAssociated_toAssociated (p : (data hq χ).core.TotalSpace) :
    fromAssociated hq χ (toAssociated hq χ p) = p := by
  apply toAssociated_injective hq χ
  exact toAssociated_fromAssociated hq χ _

/-- In any local covering section, the map uses precisely the scalar given
by the original vector-bundle chart. -/
theorem toAssociated_localTriv (i : B) (p : (data hq χ).core.TotalSpace)
    (hp : p.1 ∈ baseSet hq i) :
    toAssociated hq χ p =
      associatedMap χ (lift hq i p.1, ((data hq χ).core.localTriv i p).2) := by
  change associatedMap χ (lift hq p.1 p.1, id (α := ℂ) p.2) =
    associatedMap χ (lift hq i p.1, (χ (deck hq p.1 i p.1) : ℂ) * id (α := ℂ) p.2)
  rw [← deck_spec hq p.1 i ⟨mem_baseSet hq p.1, hp⟩]
  exact (associatedMap_diagonal χ _ _).symm

/-- Coordinates of an associated orbit in a fixed bundle chart, whenever
the chosen local lift is a specified deck translate of the original lift. -/
theorem localTriv_fromAssociated_map (i : B) (a : A) (z : ℂ) (g : G)
    (ha : q a ∈ baseSet hq i) (hg : lift hq i (q a) = g • a) :
    (data hq χ).core.localTriv i (fromAssociated hq χ (associatedMap χ (a, z))) =
      (q a, (χ g : ℂ) * z) := by
  apply Prod.ext
  · rfl
  · apply associatedMap_fibre_injective hq χ (lift hq i (q a))
    calc
      associatedMap χ (lift hq i (q a),
          ((data hq χ).core.localTriv i (fromAssociated hq χ (associatedMap χ (a, z)))).2) =
          toAssociated hq χ (fromAssociated hq χ (associatedMap χ (a, z))) :=
        (toAssociated_localTriv hq χ i (fromAssociated hq χ (associatedMap χ (a, z))) ha).symm
      _ = associatedMap χ (a, z) := toAssociated_fromAssociated hq χ _
      _ = associatedMap χ (lift hq i (q a), (χ g : ℂ) * z) := by
        rw [hg]
        exact (associatedMap_diagonal χ g (a, z)).symm

/-- The scalar coordinate of the image in an arbitrary local lift is the
character transition applied linearly to the original fibre vector. -/
theorem fibreCoordinate_toAssociated (i b : B) (z : (data hq χ).core.Fiber b)
    (hb : b ∈ baseSet hq i) :
    fibreCoordinate hq χ (lift hq i b) (toAssociated hq χ ⟨b, z⟩)
      ((projection_toAssociated hq χ _).trans (lift_project hq i hb).symm) =
        (χ (deck hq b i b) : ℂ) * id (α := ℂ) z := by
  apply associatedMap_fibre_injective hq χ (lift hq i b)
  exact (associatedMap_fibreCoordinate hq χ _ _ _).trans
    (toAssociated_localTriv hq χ i ⟨b, z⟩ hb)

/-- The linear coordinate map on a fibre, with its explicit inverse. It
agrees with the actual quotient coordinate whenever the local lift is
defined at the base point. -/
def fibreLinearEquiv (i b : B) : (data hq χ).core.Fiber b ≃ₗ[ℂ] ℂ where
  toFun z := (χ (deck hq b i b) : ℂ) * id (α := ℂ) z
  invFun z := (χ (deck hq b i b) : ℂ)⁻¹ * z
  left_inv z := by
    change (χ (deck hq b i b) : ℂ)⁻¹ *
      ((χ (deck hq b i b) : ℂ) * id (α := ℂ) z) = id (α := ℂ) z
    rw [← mul_assoc, inv_mul_cancel₀ (χ (deck hq b i b)).ne_zero, one_mul]
  right_inv z := by
    change (χ (deck hq b i b) : ℂ) * ((χ (deck hq b i b) : ℂ)⁻¹ * z) = z
    rw [← mul_assoc, mul_inv_cancel₀ (χ (deck hq b i b)).ne_zero, one_mul]
  map_add' z w := mul_add _ (id (α := ℂ) z) (id (α := ℂ) w)
  map_smul' a z := mul_left_comm _ a (id (α := ℂ) z)

@[simp] theorem fibreLinearEquiv_apply (i b : B) (z : (data hq χ).core.Fiber b) :
    fibreLinearEquiv hq χ i b z = (χ (deck hq b i b) : ℂ) * id (α := ℂ) z := rfl

theorem fibreCoordinate_toAssociated_linear (i b : B) (z : (data hq χ).core.Fiber b)
    (hb : b ∈ baseSet hq i) :
    fibreCoordinate hq χ (lift hq i b) (toAssociated hq χ ⟨b, z⟩)
      ((projection_toAssociated hq χ _).trans (lift_project hq i hb).symm) =
        fibreLinearEquiv hq χ i b z :=
  fibreCoordinate_toAssociated hq χ i b z hb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]

local notation "IA" => modelWithCornersSelf ℂ E
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ (E × ℂ)

local instance productChartedSpace : ChartedSpace (E × ℂ) (A × ℂ) :=
  inferInstanceAs (ChartedSpace (ModelProd E ℂ) (A × ℂ))

variable [IsManifold (modelWithCornersSelf ℂ E) ω A]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

local instance productManifold : IsManifold I₂ ω (A × ℂ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := IA) (I' := I₁) A ℂ

include hG

/-- The map from the independently constructed cocycle bundle is analytic
in the actual covering-quotient atlas of the associated space. -/
theorem toAssociated_holomorphic :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq χ
    ContMDiff ((IA).prod I₁) I₂ ω (toAssociated hq χ) := by
  let := CoveringQuotient.chartedSpace (E := E) hq
  let := associatedChartedSpace (E := E) hq χ
  let := CoveringQuotient.isManifold hq ω hG
  intro p
  let e := trivializationAt ℂ (data hq χ).core.Fiber p.proj
  have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have he : ContMDiffAt ((IA).prod I₁) ((IA).prod I₁) ω e p :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hp)
  have hl : ContMDiffAt IA IA ω (lift hq p.proj) p.proj :=
    (lift_holomorphic hq hG p.proj).contMDiffAt
      ((isOpen_baseSet hq p.proj).mem_nhds (mem_baseSet hq p.proj))
  have hm : ContMDiffAt ((IA).prod I₁) I₂ ω
      (fun r : B × ℂ => associatedMap χ (lift hq p.proj r.1, r.2)) (e p) := by
    have hf : ContMDiffAt ((IA).prod I₁) I₂ ω
        (fun r : B × ℂ => (lift hq p.proj r.1, r.2)) (e p) := by
      rw [modelWithCornersSelf_prod]
      exact (hl.comp (e p) contMDiffAt_fst).prodMk contMDiffAt_snd
    exact (associatedMap_holomorphic hq χ hG).contMDiffAt.comp (e p) hf
  apply (hm.comp p he).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with r hr
  exact toAssociated_localTriv hq χ p.proj r hr

/-- Pulling the inverse map back to the original covering space makes its
fibre coordinates locally multiplication by a fixed character value. -/
theorem fromAssociated_comp_holomorphic :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    ContMDiff I₂ ((IA).prod I₁) ω (fromAssociated hq χ ∘ associatedMap (A := A) χ) := by
  let := CoveringQuotient.chartedSpace (E := E) hq
  let := CoveringQuotient.isManifold hq ω hG
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · have hproj : ContMDiff I₂ IA ω (fun r : A × ℂ => q r.1) := by
      rw [modelWithCornersSelf_prod]
      exact (CoveringQuotient.contMDiff_project hq ω hG).comp contMDiff_fst
    exact hproj.contMDiffAt
  · change ContMDiffAt I₂ I₁ ω (fun r : A × ℂ =>
      ((data hq χ).core.localTriv (q p.1) (fromAssociated hq χ (associatedMap χ r))).2) p
    obtain ⟨g, _, hg⟩ := CoveringQuotient.localInverse_eventually_deck hq
      hq.continuous_const_smul (CoveringQuotient.representative hq (q p.1)) p.1
      (mem_baseSet hq (q p.1))
    have hnear : ∀ᶠ r : A × ℂ in 𝓝 p, q r.1 ∈ baseSet hq (q p.1) :=
      (hq.continuous.comp continuous_fst).continuousAt
        ((isOpen_baseSet hq (q p.1)).mem_nhds (mem_baseSet hq (q p.1)))
    have hs : ContMDiffAt I₂ I₁ ω (fun r : A × ℂ => (χ g : ℂ) * r.2) p := by
      rw [modelWithCornersSelf_prod]
      exact ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd).contMDiffAt
    apply hs.congr_of_eventuallyEq
    filter_upwards [hnear, hg.comp_tendsto continuousAt_fst] with r hr hgr
    exact congrArg Prod.snd (localTriv_fromAssociated_map hq χ (q p.1) r.1 r.2 g hr hgr)

/-- Analyticity of the inverse descends through the actual associated
covering map. -/
theorem fromAssociated_holomorphic :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq χ
    ContMDiff I₂ ((IA).prod I₁) ω (fromAssociated hq χ) := by
  let := CoveringQuotient.chartedSpace (E := E) hq
  let := associatedChartedSpace (E := E) hq χ
  let := diagonalAction (A := A) χ
  exact CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap hq χ) ((IA).prod I₁) ω
    (fromAssociated_comp_holomorphic hq χ hG)

/-- A base-preserving analytic diffeomorphism from the cocycle bundle onto
the actual diagonal orbit quotient. The original topologies and complex
atlases on both sides are unchanged. -/
def identification :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq χ
    Diffeomorph ((IA).prod I₁) I₂ (data hq χ).core.TotalSpace (AssociatedSpace (A := A) χ) ω := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq χ
  exact
    { toFun := toAssociated hq χ
      invFun := fromAssociated hq χ
      left_inv := fromAssociated_toAssociated hq χ
      right_inv := toAssociated_fromAssociated hq χ
      contMDiff_toFun := toAssociated_holomorphic hq χ hG
      contMDiff_invFun := fromAssociated_holomorphic hq χ hG }

@[simp] theorem identification_apply (p : (data hq χ).core.TotalSpace) :
    identification hq χ hG p = toAssociated hq χ p := rfl

@[simp] theorem identification_symm_apply (p : AssociatedSpace (A := A) χ) :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq χ
    (identification hq χ hG).symm p = fromAssociated hq χ p := rfl

@[simp] theorem identification_preserves_base (p : (data hq χ).core.TotalSpace) :
    projection hq χ (identification hq χ hG p) = p.proj :=
  projection_toAssociated hq χ p

@[simp] theorem identification_symm_preserves_base (p : AssociatedSpace (A := A) χ) :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq χ
    ((identification hq χ hG).symm p).proj = projection hq χ p := rfl

/-- The map on each fibre is linear in the scalar coordinate determined by
every local lift, not just in a formally transported algebraic structure. -/
theorem identification_fibreCoordinate (i b : B) (z : (data hq χ).core.Fiber b)
    (hb : b ∈ baseSet hq i) :
    fibreCoordinate hq χ (lift hq i b) (identification hq χ hG ⟨b, z⟩)
      ((identification_preserves_base hq χ hG _).trans (lift_project hq i hb).symm) =
        (χ (deck hq b i b) : ℂ) * id (α := ℂ) z :=
  fibreCoordinate_toAssociated hq χ i b z hb

theorem identification_fibreLinearEquiv (i b : B) (z : (data hq χ).core.Fiber b)
    (hb : b ∈ baseSet hq i) :
    fibreCoordinate hq χ (lift hq i b) (identification hq χ hG ⟨b, z⟩)
      ((identification_preserves_base hq χ hG _).trans (lift_project hq i hb).symm) =
        fibreLinearEquiv hq χ i b z :=
  fibreCoordinate_toAssociated hq χ i b z hb

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.AssociatedCore
