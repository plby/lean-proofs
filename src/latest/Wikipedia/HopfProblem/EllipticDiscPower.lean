import Wikipedia.HopfProblem.SpecialPeriodsLocal
import Wikipedia.HopfProblem.EllipticData
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.LocalAtTarget

/-!
# Positive power maps of the actual complex unit disc

The map `z ↦ z^m` is a holomorphic, surjective, proper self-map of the
open unit disc for every positive integer `m`.  Properness is obtained
by restricting the proper complex polynomial to the exact inverse image
of the open unit disc, rather than by treating the open disc as compact.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

theorem pow_mem_unitDisc_iff (m : ℕ) (hm : 0 < m) (z : ℂ) :
    z ^ m ∈ unitDisc ↔ z ∈ unitDisc := by
  change dist (z ^ m) 0 < 1 ↔ dist z 0 < 1
  rw [dist_zero_right, dist_zero_right, norm_pow]
  exact pow_lt_one_iff_of_nonneg (norm_nonneg z) hm.ne'

/-- The full inverse image of the unit disc under a positive power map
is the unit disc itself. -/
theorem complexPower_preimage_unitDisc (m : ℕ) (hm : 0 < m) :
    (fun z : ℂ => z ^ m) ⁻¹' (unitDisc : Set ℂ) = (unitDisc : Set ℂ) := by
  ext z
  exact pow_mem_unitDisc_iff m hm z

/-- The positive power map on the inherited open unit disc. -/
def discPower (m : ℕ) (hm : 0 < m) (z : Disc) : Disc :=
  ⟨(z : ℂ) ^ m, (pow_mem_unitDisc_iff m hm z).mpr z.property⟩

@[simp] theorem discPower_coe (m : ℕ) (hm : 0 < m) (z : Disc) :
    (discPower m hm z : ℂ) = (z : ℂ) ^ m := rfl

theorem discPower_holomorphic (m : ℕ) (hm : 0 < m) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discPower m hm) := by
  intro z
  have he : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun w : Disc => (discPower m hm w : ℂ)) z ↔
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discPower m hm) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_subtype_val.pow m) z)

theorem discPower_continuous (m : ℕ) (hm : 0 < m) : Continuous (discPower m hm) :=
  (discPower_holomorphic m hm).continuous

/-- Every point of the disc has an `m`th root in the same disc. -/
theorem discPower_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (discPower m hm) := by
  intro w
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) hm
  have hmem : z ∈ unitDisc := (pow_mem_unitDisc_iff m hm z).mp (hz ▸ w.property)
  exact ⟨⟨z, hmem⟩, Subtype.ext hz⟩

/-- A positive complex monomial is a proper map of the whole plane. -/
theorem complexPower_isProperMap (m : ℕ) (hm : 0 < m) :
    IsProperMap (fun z : ℂ => z ^ m) := by
  have hp : 0 < (Polynomial.X ^ m : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast hm
  simpa only [Polynomial.eval_X_pow] using
    (Polynomial.X ^ m : Polynomial ℂ).isProperMap_eval hp

/-- The disc power map is proper for the actual open-disc topology. -/
theorem discPower_isProperMap (m : ℕ) (hm : 0 < m) : IsProperMap (discPower m hm) := by
  let e : Disc ≃ₜ ((fun z : ℂ => z ^ m) ⁻¹' (unitDisc : Set ℂ)) :=
    Homeomorph.setCongr (complexPower_preimage_unitDisc m hm).symm
  have hp := ((complexPower_isProperMap m hm).restrictPreimage (unitDisc : Set ℂ)).comp
    e.isProperMap
  have he : (unitDisc : Set ℂ).restrictPreimage (fun z : ℂ => z ^ m) ∘ e =
      discPower m hm := by
    funext z
    rfl
  rwa [he] at hp

/-- The center of the actual open unit disc. -/
def discZero : Disc := ⟨0, by simp [unitDisc]⟩

@[simp] theorem discZero_coe : (discZero : ℂ) = 0 := rfl

@[simp] theorem discPower_coe_eq_zero_iff (m : ℕ) (hm : 0 < m) (z : Disc) :
    (discPower m hm z : ℂ) = 0 ↔ (z : ℂ) = 0 := by
  simp only [discPower_coe, pow_eq_zero_iff hm.ne']

@[simp] theorem discPower_eq_zero_iff (m : ℕ) (hm : 0 < m) (z : Disc) :
    discPower m hm z = discZero ↔ z = discZero := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact discPower_coe_eq_zero_iff m hm z

@[simp] theorem discPower_zero (m : ℕ) (hm : 0 < m) :
    discPower m hm discZero = discZero := (discPower_eq_zero_iff m hm _).mpr rfl

theorem discPower_preimage_zero (m : ℕ) (hm : 0 < m) :
    discPower m hm ⁻¹' {discZero} = {discZero} := by
  ext z
  exact discPower_eq_zero_iff m hm z

/-- Compact subsets of the base disc have compact inverse images. -/
theorem discPower_isCompact_preimage (m : ℕ) (hm : 0 < m) {K : Set Disc}
    (hK : IsCompact K) : IsCompact (discPower m hm ⁻¹' K) :=
  (discPower_isProperMap m hm).isCompact_preimage hK

end Wikipedia.HopfProblem.Elliptic
