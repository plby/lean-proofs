import Wikipedia.HopfProblem.DegreeCollapseCyclicExtensionCoordinate

/-!
# The actual finite quotient character of a cyclic extension

Reduce the constructed rational coordinate modulo the integers and descend
along the original surjection. Every exterior relation gives its literal
rational residue. A nonzero value is equivalent to existence of a positive
nondivisible relation; the quotient cardinality constructs that relation.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.CyclicExtensionCharacter

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite H]
  (μ : G) (q : G →+ H) (hker : q.ker = AddSubgroup.zmultiples μ)
  (hμ : Injective (fun k : ℤ ↦ k • μ))

theorem residueCoordinate_kernel :
    LinearMap.ker q.toIntLinearMap ≤
      LinearMap.ker (RationalResidue.residue.comp (rationalCoordinate μ q hker hμ)) := by
  intro g hg
  have hm : g ∈ AddSubgroup.zmultiples μ := by
    rw [← hker]
    exact hg
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  change RationalResidue.residue (rationalCoordinate μ q hker hμ (k • μ)) = 0
  rw [map_zsmul, rationalCoordinate_meridian]
  simpa only [zsmul_eq_mul, mul_one] using RationalResidue.residue_intCast k

def character (hq : Surjective q) : H →ₗ[ℤ] RationalResidue.Value :=
  ((LinearMap.ker q.toIntLinearMap).liftQ
    (RationalResidue.residue.comp (rationalCoordinate μ q hker hμ))
      (residueCoordinate_kernel μ q hker hμ)).comp
        (q.toIntLinearMap.quotKerEquivOfSurjective hq).symm.toLinearMap

theorem character_quotient (hq : Surjective q) (g : G) :
    character μ q hker hμ hq (q g) =
      RationalResidue.residue (rationalCoordinate μ q hker hμ g) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply q.toIntLinearMap
    (show Surjective q.toIntLinearMap from hq) g
  exact congrArg ((LinearMap.ker q.toIntLinearMap).liftQ
    (RationalResidue.residue.comp (rationalCoordinate μ q hker hμ))
    (residueCoordinate_kernel μ q hker hμ)) he

theorem character_of_relation (hq : Surjective q) (g : G) (l p : ℤ) (hl : l ≠ 0)
    (hrel : l • g + p • μ = 0) :
    character μ q hker hμ hq (q g) = RationalResidue.residue (-(p : ℚ) / (l : ℚ)) := by
  rw [character_quotient, rationalCoordinate_of_relation μ q hker hμ g l p hl hrel]

theorem character_eq_zero_iff_dvd (hq : Surjective q) (g : G) (l p : ℤ) (hl : l ≠ 0)
    (hrel : l • g + p • μ = 0) :
    character μ q hker hμ hq (q g) = 0 ↔ l ∣ p := by
  rw [character_of_relation μ q hker hμ hq g l p hl hrel]
  exact RationalResidue.residue_neg_div_eq_zero_iff p l hl

include hker in
theorem exists_positive_relation (g : G) :
    ∃ l p : ℤ, 0 < l ∧ l • g + p • μ = 0 := by
  refine ⟨Nat.card H, -coefficient μ q hker g, ?_, ?_⟩
  · exact_mod_cast (Nat.card_pos : 0 < Nat.card H)
  · rw [neg_smul, coefficient_spec, add_neg_cancel]

theorem character_ne_zero_iff_nondivisible_relation (hq : Surjective q) (g : G) :
    character μ q hker hμ hq (q g) ≠ 0 ↔
      ∃ l p : ℤ, 0 < l ∧ ¬ l ∣ p ∧ l • g + p • μ = 0 := by
  constructor
  · intro hn
    obtain ⟨l, p, hl, hrel⟩ := exists_positive_relation μ q hker g
    exact ⟨l, p, hl, fun hp ↦ hn
      ((character_eq_zero_iff_dvd μ q hker hμ hq g l p hl.ne' hrel).mpr hp), hrel⟩
  · rintro ⟨l, p, hl, hp, hrel⟩ hz
    exact hp ((character_eq_zero_iff_dvd μ q hker hμ hq g l p hl.ne' hrel).mp hz)

end Wikipedia.HopfProblem.DegreeCollapse.CyclicExtensionCharacter
