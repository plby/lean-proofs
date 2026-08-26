import ErdosProblems.Erdos941.IntertwinerLattice
import ErdosProblems.Erdos941.QuaternionGram

/-! # Integral bases for the modules of sphere intertwiners -/

namespace Erdos941

open scoped Quaternion

def integralIntertwiners (v w : Triple) : Submodule ℤ hurwitzOrder where
  carrier := {q | (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q}
  zero_mem' := by simp
  add_mem' := by
    intro q r hq hr
    change ((q : ℍ[ℚ]) + (r : ℍ[ℚ])) * pureQuaternion v =
      pureQuaternion w * ((q : ℍ[ℚ]) + (r : ℍ[ℚ]))
    rw [add_mul, mul_add, hq, hr]
  smul_mem' := by
    intro a q hq
    change (a • (q : ℍ[ℚ])) * pureQuaternion v = pureQuaternion w * (a • (q : ℍ[ℚ]))
    rw [smul_mul_assoc, mul_smul_comm, hq]

def parameterToIntertwiners {v w : Triple} {n : ℕ} (hv : tripleNorm v = n)
    {q : hurwitzOrder}
    (hq : (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q) :
    parameterLattice hv q →ₗ[ℤ] integralIntertwiners v w where
  toFun z := ⟨parameterLatticeMap hv q z, quaternionParam_intertwines hv hq z⟩
  map_add' z t := Subtype.ext ((parameterLatticeMap hv q).map_add _ _)
  map_smul' r z := Subtype.ext ((parameterLatticeMap hv q).map_smul r z)

noncomputable def parameterIntertwinerEquiv {v w : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) (hv0 : v ≠ 0) {q : hurwitzOrder} (hq0 : q ≠ 0)
    (hq : (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q) :
    parameterLattice hv q ≃ₗ[ℤ] integralIntertwiners v w :=
  LinearEquiv.ofBijective (parameterToIntertwiners hv hq) ⟨by
    intro z t h
    apply parameterLatticeMap_injective hv hq0
    exact congrArg Subtype.val h,
    by
      intro r
      obtain ⟨z, hz⟩ := parameterLattice_covers_intertwiners hv hv0 hq0 hq r.property
      exact ⟨z, Subtype.ext hz⟩⟩

noncomputable def integralIntertwinerBasis {v w : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) (hv0 : v ≠ 0) {q : hurwitzOrder} (hq0 : q ≠ 0)
    (hq : (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q) :
    Module.Basis (Fin 2) ℤ (integralIntertwiners v w) :=
  (parameterLatticeBasis hv hq0).map (parameterIntertwinerEquiv hv hv0 hq0 hq)

def integralIntertwinerInclusion (v w : Triple) : integralIntertwiners v w →ₗ[ℤ] ℍ[ℚ] where
  toFun z := ((z : hurwitzOrder) : ℍ[ℚ])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem integralIntertwinerInclusion_injective (v w : Triple) :
    Function.Injective (integralIntertwinerInclusion v w) := by
  intro z t h
  exact Subtype.ext (Subtype.ext h)

theorem integralIntertwinerBasis_independent {v w : Triple}
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w)) :
    LinearIndependent ℚ (fun i => ((b i : hurwitzOrder) : ℍ[ℚ])) := by
  have hli := b.linearIndependent.map' (integralIntertwinerInclusion v w)
    (LinearMap.ker_eq_bot.mpr (integralIntertwinerInclusion_injective v w))
  rw [LinearIndependent.iff_fractionRing ℤ ℚ] at hli
  exact hli

theorem integralIntertwinerBasis_gram_pos {v w : Triple}
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w)) :
    0 < hurwitzGram (b 0) (b 1) := by
  apply hurwitzGram_pos_of_linearIndependent
  convert integralIntertwinerBasis_independent b using 1
  funext i
  fin_cases i <;> rfl

theorem integralIntertwinerBasis_gram_lower {v w : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v)
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w)) :
    (n : ℚ) / 4 ≤ hurwitzGram (b 0) (b 1) :=
  intertwiner_gram_lower hv hp (b 0).property (b 1).property
    (integralIntertwinerBasis_gram_pos b)

end Erdos941
