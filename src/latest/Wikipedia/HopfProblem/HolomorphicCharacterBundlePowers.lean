import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedAnalytic
import Wikipedia.HopfProblem.HolomorphicCharacterBundleObstruction

/-!
# Actual character-power bundles

For each power of a character we use the associated quotient construction
again. The fibrewise power map `[a,z] ↦ [a,z^n]` is well-defined and
holomorphic between these actual quotients. The character's order divides
the order of a finite acting group and is therefore positive in that case.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

section AssociatedPowers

variable {G A B : Type*} [Group G] [MulAction G A]

/-- The geometric fibrewise power map into the associated power-character
bundle. It is homogeneous of degree `n`, not asserted to be linear. -/
def powerMap (χ : G →* ℂˣ) (n : ℕ) :
    AssociatedSpace (A := A) χ → AssociatedSpace (A := A) (χ ^ n) :=
  Quotient.lift (fun p : A × ℂ => associatedMap (χ ^ n) (p.1, p.2 ^ n)) fun p r h => by
    obtain ⟨g, hg⟩ := h
    apply (associatedMap_eq_iff (χ ^ n) _ _).mpr
    refine ⟨g, congrArg Prod.fst hg, ?_⟩
    have hz : (χ g : ℂ) * r.2 = p.2 := congrArg Prod.snd hg
    simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rw [← mul_pow, hz]

@[simp] theorem powerMap_associatedMap (χ : G →* ℂˣ) (n : ℕ) (p : A × ℂ) :
    powerMap χ n (associatedMap χ p) = associatedMap (χ ^ n) (p.1, p.2 ^ n) := rfl

variable [TopologicalSpace A] [TopologicalSpace B]
  {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)

@[simp] theorem projection_powerMap (n : ℕ) (p : AssociatedSpace (A := A) χ) :
    projection hq (χ ^ n) (powerMap χ n p) = projection hq χ p := by
  obtain ⟨p, rfl⟩ := associatedMap_surjective χ p
  rfl

theorem powerMap_continuous (n : ℕ) : Continuous (powerMap (A := A) χ n) := by
  apply (associatedMap_isQuotientMap χ).continuous_iff.mpr
  exact (associatedMap_continuous (χ ^ n)).comp
    (continuous_fst.prodMk (continuous_snd.pow n))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]
  [IsManifold (modelWithCornersSelf ℂ E) ω A]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

local notation "IA" => modelWithCornersSelf ℂ E
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ (E × ℂ)

local instance associatedPowerProductChartedSpace : ChartedSpace (E × ℂ) (A × ℂ) :=
  inferInstanceAs (ChartedSpace (ModelProd E ℂ) (A × ℂ))

local instance associatedPowerProductManifold : IsManifold I₂ ω (A × ℂ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := IA) (I' := I₁) A ℂ

include hG

theorem powerMap_holomorphic (n : ℕ) :
    letI := associatedChartedSpace (E := E) hq χ
    letI := associatedChartedSpace (E := E) hq (χ ^ n)
    ContMDiff I₂ I₂ ω (powerMap (A := A) χ n) := by
  letI := associatedChartedSpace (E := E) hq (χ ^ n)
  letI := diagonalAction (A := A) χ
  apply CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap hq χ) I₂ ω
  apply (associatedMap_holomorphic hq (χ ^ n) hG).comp
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst.prodMk ((contDiff_id.pow n).contMDiff.comp contMDiff_snd)

end AssociatedPowers

section CharacterOrder

variable {G : Type*} [Group G] (χ : G →* ℂˣ)

theorem character_pow_card : χ ^ Nat.card G = 1 := by
  ext g
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply]
  rw [← map_pow, pow_card_eq_one', map_one]

theorem orderOf_character_dvd_card : orderOf χ ∣ Nat.card G :=
  orderOf_dvd_iff_pow_eq_one.mpr (character_pow_card χ)

theorem orderOf_character_pos [Finite G] : 0 < orderOf χ := by
  have hd := orderOf_character_dvd_card χ
  have hc : 0 < Nat.card G := Nat.card_pos
  by_contra hn
  have hz : orderOf χ = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz, zero_dvd_iff] at hd
  omega

end CharacterOrder

end Wikipedia.HopfProblem.HolomorphicCharacterBundle
