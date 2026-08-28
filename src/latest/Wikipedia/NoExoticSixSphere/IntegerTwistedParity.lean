import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# A parity quotient for a triangular pair of integer relations

This algebraic calculation keeps the integer endomorphisms as parameters,
so checking it does not unfold the geometric singular-chain constructions.
-/

namespace NoExoticSixSphere.IntegerTwistedParity

variable (A B : ℤ →ₗ[ℤ] ℤ)

def projection : (ℤ × ℤ) →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap.comp
    ((AddMonoidHom.snd ℤ ℤ + B.toAddMonoidHom.comp (AddMonoidHom.fst ℤ ℤ)).toIntLinearMap)

theorem projection_apply (p : ℤ × ℤ) :
    projection B p = ((p.2 + B p.1 : ℤ) : ZMod 2) := rfl

theorem projection_surjective : Function.Surjective (projection B) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨(0, k), ?_⟩
  simp [projection_apply]

theorem range_eq_kernel (F : (ℤ × ℤ) →ₗ[ℤ] ℤ × ℤ)
    (hF : ∀ a b, F (a, b) = (b, -(A a + B b)))
    (hA : Set.range A = Set.range (fun z : ℤ ↦ 2 * z)) :
    LinearMap.range F = LinearMap.ker (projection B) := by
  ext p
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    rw [LinearMap.mem_ker, hF, projection_apply]
    have ha : A a ∈ Set.range A := ⟨a, rfl⟩
    rw [hA] at ha
    obtain ⟨k, hk⟩ := ha
    have hs : -(A a + B b) + B b = -(2 * k) := by rw [← hk]; ring
    change ((-(A a + B b) + B b : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨-k, ?_⟩
    rw [hs]
    ring
  · intro hp
    change ((p.2 + B p.1 : ℤ) : ZMod 2) = 0 at hp
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (p.2 + B p.1) 2).mp hp
    obtain ⟨k, hk⟩ := hd
    have htarget : -(p.2 + B p.1) ∈ Set.range A := by
      rw [hA]
      refine ⟨-k, ?_⟩
      rw [hk]
      ring
    obtain ⟨a, ha⟩ := htarget
    refine ⟨(a, p.1), ?_⟩
    rw [hF, ha]
    apply Prod.ext
    · rfl
    · ring

end NoExoticSixSphere.IntegerTwistedParity
