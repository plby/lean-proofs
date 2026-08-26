import ErdosProblems.Erdos941.SphereQuadraticOrder

/-! # The area of a lattice of Hurwitz intertwiners -/

namespace Erdos941

open scoped Quaternion

theorem star_pureQuaternion (v : Triple) : star (pureQuaternion v) = -pureQuaternion v :=
  Quaternion.star_eq_neg.mpr rfl

theorem star_mul_intertwiner_commutes {v w : Triple} {q r : ℍ[ℚ]}
    (hq : q * pureQuaternion v = pureQuaternion w * q)
    (hr : r * pureQuaternion v = pureQuaternion w * r) :
    (star q * r) * pureQuaternion v = pureQuaternion v * (star q * r) := by
  have hstar := congrArg star hq
  rw [star_mul, star_mul, star_pureQuaternion, star_pureQuaternion,
    neg_mul, mul_neg, neg_inj] at hstar
  calc
    star q * r * pureQuaternion v = star q * (r * pureQuaternion v) := mul_assoc _ _ _
    _ = star q * (pureQuaternion w * r) := congrArg (star q * ·) hr
    _ = (star q * pureQuaternion w) * r := (mul_assoc _ _ _).symm
    _ = (pureQuaternion v * star q) * r := congrArg (· * r) hstar.symm
    _ = pureQuaternion v * (star q * r) := mul_assoc _ _ _

theorem sphereFieldEmbedding_norm {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (z : SphereQuadraticField n) :
    Quaternion.normSq (sphereFieldEmbedding hv z) = z.re ^ 2 + (n : ℚ) * z.im ^ 2 := by
  rw [Quaternion.normSq_def']
  change (sphereFieldEmbedding hv z).re ^ 2 + (sphereFieldEmbedding hv z).imI ^ 2 +
    (sphereFieldEmbedding hv z).imJ ^ 2 + (sphereFieldEmbedding hv z).imK ^ 2 = _
  rw [sphereFieldEmbedding_re, sphereFieldEmbedding_imI, sphereFieldEmbedding_imJ,
    sphereFieldEmbedding_imK]
  have hvQ : (v.1 : ℚ) ^ 2 + (v.2.1 : ℚ) ^ 2 + (v.2.2 : ℚ) ^ 2 = n := by
    exact_mod_cast hv
  linear_combination z.im ^ 2 * hvQ

def hurwitzGram (q r : hurwitzOrder) : ℚ :=
  Quaternion.normSq (q : ℍ[ℚ]) * Quaternion.normSq (r : ℍ[ℚ]) -
    (star (q : ℍ[ℚ]) * (r : ℍ[ℚ])).re ^ 2

theorem intertwiner_gram_integer_multiple {v w : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) {q r : hurwitzOrder}
    (hq : (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q)
    (hr : (r : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * r) :
    ∃ s : ℤ, 4 * hurwitzGram q r = (n : ℚ) * (s : ℚ) ^ 2 := by
  have hcomm := star_mul_intertwiner_commutes hq hr
  obtain ⟨a, b, hab⟩ := (pureQuaternion_commutes_iff hp.ne_zero _).mp hcomm
  let z : SphereQuadraticField n := ⟨a, b⟩
  have hz : sphereFieldEmbedding hv z = star (q : ℍ[ℚ]) * (r : ℍ[ℚ]) := hab.symm
  have hzmem : z ∈ sphereQuadraticOrder hv := by
    change sphereFieldEmbedding hv z ∈ hurwitzOrder
    rw [hz]
    exact hurwitzOrder.mul_mem (hurwitz_star_mem q.property) r.property
  obtain ⟨i, s, hi, hs, hA, hB, hC⟩ :=
    (sphereQuadraticOrder_coordinates hv hp z).mp hzmem
  have hnorm := sphereFieldEmbedding_norm hv z
  rw [hz, map_mul, Quaternion.normSq_star] at hnorm
  have hre : (star (q : ℍ[ℚ]) * (r : ℍ[ℚ])).re = z.re := by
    rw [← hz, sphereFieldEmbedding_re]
  refine ⟨s, ?_⟩
  dsimp only [hurwitzGram]
  rw [hre, hnorm, hs]
  ring

theorem intertwiner_gram_lower {v w : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) {q r : hurwitzOrder}
    (hq : (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q)
    (hr : (r : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * r)
    (hpos : 0 < hurwitzGram q r) : (n : ℚ) / 4 ≤ hurwitzGram q r := by
  obtain ⟨s, hs⟩ := intertwiner_gram_integer_multiple hv hp hq hr
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs; linarith
  have hs1 : (1 : ℤ) ≤ s ^ 2 := by
    have hcases : s ≤ -1 ∨ 1 ≤ s := by omega
    rcases hcases with h | h <;> nlinarith
  have hsQ : (1 : ℚ) ≤ (s : ℚ) ^ 2 := by exact_mod_cast hs1
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  nlinarith

end Erdos941
