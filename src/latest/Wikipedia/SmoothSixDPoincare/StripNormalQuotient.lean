import Wikipedia.SmoothSixDPoincare.StripCenterImmersion
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The sheet frame in the quotient by a transverse strip plane

In a genuine ambient sheet chart, the strip's horizontal derivative is the
arc direction and its vertical derivative has nonzero sheet-normal component.
Consequently the remaining sheet directions remain independent after passing
to the quotient by the strip tangent plane. This is the linear input for the
boundary two-frame in tubular disk-normal coordinates.
-/

noncomputable section

open Function

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

variable {A B Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The sheet directions complementary to its straight arc coordinate. -/
def sheetTransverseInclusion : A →L[ℝ] Space A B :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B).comp (ContinuousLinearMap.inr ℝ ℝ A)

theorem sheetTransverseInclusion_apply (a : A) :
    (sheetTransverseInclusion : A →L[ℝ] Space A B) a = ((0, a), 0) := rfl

/-- No nonzero transverse sheet direction lies in the actual strip tangent plane. -/
theorem sheetTransverse_eq_strip_iff (L : (ℝ × ℝ) →L[ℝ] Space A B)
    (hh : L (1, 0) = center 1) (hn : (L (0, 1)).2 ≠ 0) (a : A) (p : ℝ × ℝ) :
    sheetTransverseInclusion a = L p ↔ a = 0 ∧ p = 0 := by
  constructor
  · intro heq
    have hsplit : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
    have hexp : L p = p.1 • center 1 + p.2 • L (0, 1) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_smul, map_smul, hh]
    rw [hexp] at heq
    have hp2zero : p.2 • (L (0, 1)).2 = 0 := by
      simpa [sheetTransverseInclusion_apply, center] using (congrArg Prod.snd heq).symm
    have hp2 : p.2 = 0 := (smul_eq_zero.mp hp2zero).resolve_right hn
    rw [hp2, zero_smul, add_zero] at heq
    have hp1 : p.1 = 0 := by
      simpa [sheetTransverseInclusion_apply, center] using
        (congrArg (fun q : Space A B => q.1.1) heq).symm
    have ha : a = 0 := by
      simpa [sheetTransverseInclusion_apply, center] using
        congrArg (fun q : Space A B => q.1.2) heq
    exact ⟨ha, Prod.ext hp1 hp2⟩
  · rintro ⟨rfl, rfl⟩
    rw [map_zero, map_zero]

/-- A normal quotient with precisely the strip tangent kernel gives an actual sheet frame. -/
theorem injective_sheetTransverse_normalQuotient
    (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : Space A B →L[ℝ] Z)
    (hh : L (1, 0) = center 1) (hn : (L (0, 1)).2 ≠ 0)
    (hker : Q.ker = L.range) : Injective (Q.comp sheetTransverseInclusion) := by
  have hz : ∀ a : A, Q (sheetTransverseInclusion a) = 0 → a = 0 := by
    intro a ha
    have hmem : sheetTransverseInclusion a ∈ L.range := by
      rw [← hker]
      exact ha
    obtain ⟨p, hp⟩ := hmem
    exact ((sheetTransverse_eq_strip_iff L hh hn a p).mp hp.symm).1
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  change (Q.comp sheetTransverseInclusion) (a - b) = 0
  rw [map_sub, hab, sub_self]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pull the exact tangent kernel back through an injective ambient chart derivative. -/
theorem ker_comp_eq_range_of_injective
    (T : Space A B →L[ℝ] V) (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : V →L[ℝ] Z)
    (hT : Injective T) (hker : Q.ker = (T.comp L).range) :
    (Q.comp T).ker = L.range := by
  ext v
  constructor
  · intro hv
    have hmem : T v ∈ (T.comp L).range := by
      rw [← hker]
      exact hv
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, hT hp⟩
  · rintro ⟨p, rfl⟩
    have hmem : T (L p) ∈ Q.ker := by
      rw [hker]
      exact ⟨p, rfl⟩
    exact hmem

end Wikipedia.SmoothSixDPoincare.StripCoordinates
