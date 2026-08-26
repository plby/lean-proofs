import ErdosProblems.Erdos941.PrimitiveRootInjection

/-! # Root data at all moduli coprime to twice the sphere norm -/

namespace Erdos941

open scoped Quaternion

structure RootDatum (n : ℕ) where
  modulus : ℕ
  root : ℕ
  modulus_pos : 0 < modulus
  coprime : modulus.Coprime (2 * n)
  root_lt : root < modulus
  root_dvd : modulus ∣ root ^ 2 + n

structure AllRootSphereWitness {n : ℕ} (v : Triple) (d : RootDatum n) where
  liftedRoot : ℕ
  quaternion : hurwitzOrder
  factor : hurwitzOrder
  point : Triple
  root_mod : liftedRoot % d.modulus = d.root % d.modulus
  norm_eq : hurwitzNorm quaternion = d.modulus
  factor_eq : factor * quaternion = rootHurwitz liftedRoot v
  point_mem : point ∈ spherePoints n
  intertwines : (quaternion : ℍ[ℚ]) * pureQuaternion v = pureQuaternion point * quaternion

noncomputable def allRootSphereWitness {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (d : RootDatum n) : AllRootSphereWitness v d := by
  have h : Nonempty (AllRootSphereWitness v d) := by
    obtain ⟨B, q, s, w, hB, hq, hs, hw, hqw⟩ :=
      exists_root_sphere_quaternion hv d.modulus_pos d.root_dvd d.coprime
    exact ⟨⟨B, q, s, w, hB, hq, hs, hw, hqw⟩⟩
  exact Classical.choice h

noncomputable def allRootQuaternionChoice {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (d : RootDatum n) : hurwitzOrder := (allRootSphereWitness hv d).quaternion

theorem allRootQuaternionChoice_injective {v : Triple} {n : ℕ} (hv : tripleNorm v = n) (hp : PrimitiveTriple v) :
    Function.Injective (allRootQuaternionChoice hv) := by
  intro d e hq
  let D := allRootSphereWitness hv d
  let E := allRootSphereWitness hv e
  change D.quaternion = E.quaternion at hq
  have ha : d.modulus = e.modulus := by rw [← D.norm_eq, ← E.norm_eq, hq]
  have hr : d.root = e.root := by
    have hs : E.factor * D.quaternion = rootHurwitz E.liftedRoot v := by
      rw [hq]
      exact E.factor_eq
    have hmod := rootHurwitz_factor_unique_mod_primitive
      (d.coprime.of_dvd_right (dvd_mul_right 2 n)) hp D.norm_eq D.factor_eq hs
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
