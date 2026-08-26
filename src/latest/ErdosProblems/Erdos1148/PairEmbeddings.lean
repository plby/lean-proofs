import ErdosProblems.Erdos1148.FormAction

/-!
# From form pairs to binary-by-ternary embeddings

The basic lemma counts pairs by viewing them as isometric embeddings of
`d*x^2 + ℓ*x*y + d*y^2` into the ternary discriminant form. This file supplies
that construction and proves injectivity when the binary form is nondegenerate.
-/

namespace Erdos1148.DukeArithmetic

def discrQuadraticForm (R : Type*) [CommRing R] : QuadraticForm R (R × R × R) :=
  QuadraticMap.ofPolar discr
    (by intro a t; dsimp [discr]; ring)
    (by intro t u v; dsimp [QuadraticMap.polar, discr]; ring)
    (by intro a t u; dsimp [QuadraticMap.polar, discr]; ring)

def pairSourceForm {R : Type*} [CommRing R] (d ℓ : R) : QuadraticForm R (R × R) :=
  QuadraticMap.ofPolar (fun v => d * v.1 ^ 2 + ℓ * v.1 * v.2 + d * v.2 ^ 2)
    (by intro a t; dsimp; ring)
    (by intro t u v; dsimp [QuadraticMap.polar]; ring)
    (by intro a t u; dsimp [QuadraticMap.polar]; ring)

def pairLinear {R : Type*} [CommRing R] (t u : R × R × R) :
    (R × R) →ₗ[R] (R × R × R) where
  toFun v := (v.1 * t.1 + v.2 * u.1,
    v.1 * t.2.1 + v.2 * u.2.1, v.1 * t.2.2 + v.2 * u.2.2)
  map_add' v w := by ext <;> dsimp <;> ring
  map_smul' a v := by ext <;> dsimp <;> ring

lemma discr_pairLinear {R : Type*} [CommRing R] {d ℓ : R} {t u : R × R × R}
    (ht : discr t = d) (hu : discr u = d) (hp : pairing t u = ℓ) (v : R × R) :
    discr (pairLinear t u v) = pairSourceForm d ℓ v := by
  change discr (pairLinear t u v) = d * v.1 ^ 2 + ℓ * v.1 * v.2 + d * v.2 ^ 2
  dsimp [discr, pairing, pairLinear] at ht hu hp ⊢
  linear_combination v.1 ^ 2 * ht + v.2 ^ 2 * hu + v.1 * v.2 * hp

def pairIsometry {R : Type*} [CommRing R] {d ℓ : R} (p : FormPair R d ℓ) :
    QuadraticMap.Isometry (pairSourceForm d ℓ) (discrQuadraticForm R) :=
  { pairLinear p.1.1 p.1.2 with
    map_app' := discr_pairLinear p.2.1 p.2.2.1 p.2.2.2 }

lemma pairing_self {R : Type*} [CommRing R] (t : R × R × R) :
    pairing t t = 2 * discr t := by
  dsimp [pairing, discr]
  ring

lemma pairing_comm {R : Type*} [CommRing R] (t u : R × R × R) :
    pairing t u = pairing u t := by
  dsimp [pairing]
  ring

lemma pairing_pairLinear_right {R : Type*} [CommRing R]
    (t u w : R × R × R) (v : R × R) :
    pairing t (pairLinear u w v) = v.1 * pairing t u + v.2 * pairing t w := by
  dsimp [pairing, pairLinear]
  ring

lemma pairLinear_eq_zero {R : Type*} [CommRing R] [NoZeroDivisors R]
    {d ℓ : R} {t u : R × R × R} (ht : discr t = d) (hu : discr u = d)
    (hp : pairing t u = ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) {v : R × R}
    (hv : pairLinear t u v = 0) : v = 0 := by
  have hxt := congrArg (pairing t) hv
  have hxu := congrArg (pairing u) hv
  have hzero (w : R × R × R) : pairing w 0 = 0 := by simp [pairing]
  have hxt' : v.1 * (2 * d) + v.2 * ℓ = 0 := by
    simpa only [pairing_pairLinear_right, pairing_self, ht, hp, hzero] using hxt
  have hxu' : v.1 * ℓ + v.2 * (2 * d) = 0 := by
    simpa only [pairing_pairLinear_right, pairing_comm u t, pairing_self, hu, hp, hzero]
      using hxu
  have hdet : 4 * d ^ 2 - ℓ ^ 2 ≠ 0 := sub_ne_zero.mpr hnd.symm
  have hx : v.1 = 0 := by
    have hmul : (4 * d ^ 2 - ℓ ^ 2) * v.1 = 0 := by
      linear_combination 2 * d * hxt' - ℓ * hxu'
    exact (mul_eq_zero.mp hmul).resolve_left hdet
  have hy : v.2 = 0 := by
    have hmul : (4 * d ^ 2 - ℓ ^ 2) * v.2 = 0 := by
      linear_combination 2 * d * hxu' - ℓ * hxt'
    exact (mul_eq_zero.mp hmul).resolve_left hdet
  exact Prod.ext hx hy

lemma pairIsometry_injective {R : Type*} [CommRing R] [NoZeroDivisors R]
    {d ℓ : R} (p : FormPair R d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Function.Injective (pairIsometry p) := by
  intro v w hvw
  have hzero : pairLinear p.1.1 p.1.2 (v - w) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hvw
  exact sub_eq_zero.mp (pairLinear_eq_zero p.2.1 p.2.2.1 p.2.2.2 hnd hzero)

def formPairOfIsometry {R : Type*} [CommRing R] {d ℓ : R}
    (f : QuadraticMap.Isometry (pairSourceForm d ℓ) (discrQuadraticForm R)) :
    FormPair R d ℓ := by
  have ht : discr (f (1, 0)) = d := by
    have h := f.map_app (1, 0)
    change discr (f (1, 0)) = d * 1 ^ 2 + ℓ * 1 * 0 + d * 0 ^ 2 at h
    simpa only [one_pow, zero_pow (by decide : 2 ≠ 0), mul_one, mul_zero, add_zero] using h
  have hu : discr (f (0, 1)) = d := by
    have h := f.map_app (0, 1)
    change discr (f (0, 1)) = d * 0 ^ 2 + ℓ * 0 * 1 + d * 1 ^ 2 at h
    simpa only [one_pow, zero_pow (by decide : 2 ≠ 0), mul_one, mul_zero, zero_add] using h
  refine ⟨(f (1, 0), f (0, 1)), ht, hu, ?_⟩
  have hmap : f (1, -1) = f (1, 0) - f (0, 1) := by
    convert f.toLinearMap.map_sub (1, 0) (0, 1) using 1 <;> simp
  have h := f.map_app (1, -1)
  change discr (f (1, -1)) = d * 1 ^ 2 + ℓ * 1 * (-1) + d * (-1) ^ 2 at h
  rw [hmap, discr_sub, ht, hu] at h
  linear_combination -h

lemma formPairOfIsometry_pairIsometry {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) : formPairOfIsometry (pairIsometry p) = p := by
  apply Subtype.ext
  change (pairLinear p.1.1 p.1.2 (1, 0), pairLinear p.1.1 p.1.2 (0, 1)) = p.1
  simp [pairLinear]

lemma pairIsometry_formPairOfIsometry {R : Type*} [CommRing R] {d ℓ : R}
    (f : QuadraticMap.Isometry (pairSourceForm d ℓ) (discrQuadraticForm R)) :
    pairIsometry (formPairOfIsometry f) = f := by
  apply QuadraticMap.Isometry.ext
  intro v
  change pairLinear (f (1, 0)) (f (0, 1)) v = f v
  symm
  calc
    f v = f (v.1 • (1, 0) + v.2 • (0, 1)) := by
      congr 1
      ext <;> simp
    _ = v.1 • f (1, 0) + v.2 • f (0, 1) := by rw [map_add, map_smul, map_smul]
    _ = pairLinear (f (1, 0)) (f (0, 1)) v := rfl

/-- The correspondence used to transfer the representation bound to pairs of forms. -/
def formPairEquivIsometry {R : Type*} [CommRing R] (d ℓ : R) :
    FormPair R d ℓ ≃ QuadraticMap.Isometry (pairSourceForm d ℓ) (discrQuadraticForm R) where
  toFun := pairIsometry
  invFun := formPairOfIsometry
  left_inv := formPairOfIsometry_pairIsometry
  right_inv := pairIsometry_formPairOfIsometry

end Erdos1148.DukeArithmetic
