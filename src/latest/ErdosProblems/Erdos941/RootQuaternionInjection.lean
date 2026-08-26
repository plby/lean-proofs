import ErdosProblems.Erdos941.RootSphereQuaternions
import Mathlib.Data.Nat.Squarefree

/-! # Distinct roots at squarefree moduli give distinct Hurwitz quaternions -/

namespace Erdos941

open scoped Quaternion

theorem rootHurwitz_sub (B C : ℕ) (v : Triple) :
    rootHurwitz B v - rootHurwitz C v = ((B : ℤ) - C : ℤ) := by
  dsimp [rootHurwitz]
  push_cast
  abel

theorem rootHurwitz_factor_unique_mod {a B C : ℕ} (ha : Squarefree a)
    {v : Triple} {q s t : hurwitzOrder} (hq : hurwitzNorm q = a)
    (hs : s * q = rootHurwitz B v) (ht : t * q = rootHurwitz C v) :
    B % a = C % a := by
  have hsub : (s - t) * q = rootHurwitz B v - rootHurwitz C v := by
    rw [sub_mul, hs, ht]
  have hdiv : a ∣ hurwitzNorm ((s - t) * q) := by
    rw [hurwitzNorm_mul, hq]
    exact dvd_mul_left _ _
  have hdivI : (a : ℤ) ∣ (hurwitzNorm ((s - t) * q) : ℤ) := by exact_mod_cast hdiv
  rw [hsub, rootHurwitz_sub, hurwitzNorm_intCast] at hdivI
  have hd : (a : ℤ) ∣ (B : ℤ) - C :=
    ((Int.squarefree_natCast.mpr ha).dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdivI
  exact (Nat.modEq_iff_dvd.mpr hd).symm

structure SquarefreeRootDatum (n : ℕ) where
  modulus : ℕ
  root : ℕ
  modulus_pos : 0 < modulus
  squarefree : Squarefree modulus
  coprime : modulus.Coprime (2 * n)
  root_lt : root < modulus
  root_dvd : modulus ∣ root ^ 2 + n

structure RootSphereWitness {n : ℕ} (v : Triple) (d : SquarefreeRootDatum n) where
  liftedRoot : ℕ
  quaternion : hurwitzOrder
  factor : hurwitzOrder
  point : Triple
  root_mod : liftedRoot % d.modulus = d.root % d.modulus
  norm_eq : hurwitzNorm quaternion = d.modulus
  factor_eq : factor * quaternion = rootHurwitz liftedRoot v
  point_mem : point ∈ spherePoints n
  intertwines : (quaternion : ℍ[ℚ]) * pureQuaternion v = pureQuaternion point * quaternion

noncomputable def rootSphereWitness {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (d : SquarefreeRootDatum n) : RootSphereWitness v d := by
  have h : Nonempty (RootSphereWitness v d) := by
    obtain ⟨B, q, s, w, hB, hq, hs, hw, hqw⟩ :=
      exists_root_sphere_quaternion hv d.modulus_pos d.root_dvd d.coprime
    exact ⟨⟨B, q, s, w, hB, hq, hs, hw, hqw⟩⟩
  exact Classical.choice h

noncomputable def rootQuaternionChoice {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (d : SquarefreeRootDatum n) : hurwitzOrder := (rootSphereWitness hv d).quaternion

theorem rootQuaternionChoice_injective {v : Triple} {n : ℕ} (hv : tripleNorm v = n) :
    Function.Injective (rootQuaternionChoice hv) := by
  intro d e hq
  let D := rootSphereWitness hv d
  let E := rootSphereWitness hv e
  change D.quaternion = E.quaternion at hq
  have ha : d.modulus = e.modulus := by rw [← D.norm_eq, ← E.norm_eq, hq]
  have hr : d.root = e.root := by
    have hs : E.factor * D.quaternion = rootHurwitz E.liftedRoot v := by
      rw [hq]
      exact E.factor_eq
    have hmod := rootHurwitz_factor_unique_mod d.squarefree D.norm_eq D.factor_eq hs
    have hemod : E.liftedRoot % d.modulus = e.root % d.modulus := by
      rw [ha]
      exact E.root_mod
    rw [D.root_mod, hemod, Nat.mod_eq_of_lt d.root_lt,
      Nat.mod_eq_of_lt (ha ▸ e.root_lt)] at hmod
    exact hmod
  cases d
  cases e
  cases ha
  cases hr
  rfl

end Erdos941
