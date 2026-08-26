import ErdosProblems.Erdos941.PrimitiveTriples

/-! # Euler's integral quaternion conjugation map on triples -/

namespace Erdos941

def fourNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

def eulerTripleMap (a b c d : ℤ) : Triple →ₗ[ℤ] Triple where
  toFun v :=
    ((a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) * v.1 +
        2 * (b * c - a * d) * v.2.1 + 2 * (b * d + a * c) * v.2.2,
      2 * (b * c + a * d) * v.1 +
        (a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) * v.2.1 + 2 * (c * d - a * b) * v.2.2,
      2 * (b * d - a * c) * v.1 + 2 * (c * d + a * b) * v.2.1 +
        (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) * v.2.2)
  map_add' v w := by ext <;> dsimp <;> ring
  map_smul' r v := by ext <;> dsimp <;> ring

theorem eulerTripleMap_norm (a b c d : ℤ) (v : Triple) :
    tripleNorm (eulerTripleMap a b c d v) = fourNorm a b c d ^ 2 * tripleNorm v := by
  dsimp [tripleNorm, norm3, eulerTripleMap, fourNorm]
  ring

theorem eulerTripleMap_inverse (a b c d : ℤ) (v : Triple) :
    eulerTripleMap a (-b) (-c) (-d) (eulerTripleMap a b c d v) =
      (fourNorm a b c d ^ 2) • v := by
  ext <;> dsimp [eulerTripleMap, fourNorm] <;> ring

def tripleBasis (i : Fin 3) : Triple :=
  if i = 0 then (1, 0, 0) else if i = 1 then (0, 1, 0) else (0, 0, 1)

def TripleDivisible (p : ℤ) (v : Triple) : Prop :=
  p ∣ v.1 ∧ p ∣ v.2.1 ∧ p ∣ v.2.2

theorem TripleDivisible.add {p : ℤ} {v w : Triple}
    (hv : TripleDivisible p v) (hw : TripleDivisible p w) : TripleDivisible p (v + w) :=
  ⟨dvd_add hv.1 hw.1, dvd_add hv.2.1 hw.2.1, dvd_add hv.2.2 hw.2.2⟩

theorem TripleDivisible.smul {p r : ℤ} {v : Triple} (hv : TripleDivisible p v) :
    TripleDivisible p (r • v) :=
  ⟨dvd_mul_of_dvd_right hv.1 r, dvd_mul_of_dvd_right hv.2.1 r,
    dvd_mul_of_dvd_right hv.2.2 r⟩

theorem TripleDivisible.linearMap {p : ℤ} {v : Triple} (hv : TripleDivisible p v)
    (T : Triple →ₗ[ℤ] Triple) : TripleDivisible p (T v) := by
  obtain ⟨a, ha⟩ := hv.1
  obtain ⟨b, hb⟩ := hv.2.1
  obtain ⟨c, hc⟩ := hv.2.2
  have heq : v = p • (a, b, c) := Prod.ext ha (Prod.ext hb hc)
  rw [heq, map_smul]
  exact ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem eulerTripleMap_nonzero_mod_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a b c d : ℤ} (hn : fourNorm a b c d = p) :
    ∃ i : Fin 3, ¬TripleDivisible p (eulerTripleMap a b c d (tripleBasis i)) := by
  by_contra! h
  have h0 := (h 0).1
  have h1 := (h 1).2.1
  have h2 := (h 2).2.2
  norm_num [eulerTripleMap, tripleBasis, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide] at h0 h1 h2
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have htwo : ¬(p : ℤ) ∣ 2 := by
    intro hdiv
    have hdivN : p ∣ 2 := by exact_mod_cast hdiv
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hdivN |>.resolve_left hp.ne_one)
  have hnD : (p : ℤ) ∣ fourNorm a b c d := by rw [hn]
  have hfourA : (p : ℤ) ∣ 4 * a ^ 2 := by
    convert dvd_add (dvd_add (dvd_add h0 h1) h2) hnD using 1 <;> try rfl
    dsimp only [fourNorm]
    ring
  have hA2 : (p : ℤ) ∣ a ^ 2 := by
    have hfour : ¬(p : ℤ) ∣ 4 := by
      intro hdiv
      have hdiv' : (p : ℤ) ∣ 2 * 2 := by simpa using hdiv
      exact (hpI.dvd_mul.mp hdiv').elim htwo htwo
    exact (hpI.dvd_mul.mp hfourA).resolve_left hfour
  have hB2 : (p : ℤ) ∣ b ^ 2 := by
    have hh : (p : ℤ) ∣ 2 * b ^ 2 := by
      convert dvd_sub (dvd_add h0 hnD) (dvd_mul_of_dvd_right hA2 2) using 1 <;> try rfl
      dsimp only [fourNorm]
      ring
    exact (hpI.dvd_mul.mp hh).resolve_left htwo
  have hC2 : (p : ℤ) ∣ c ^ 2 := by
    have hh : (p : ℤ) ∣ 2 * c ^ 2 := by
      convert dvd_sub (dvd_add h1 hnD) (dvd_mul_of_dvd_right hA2 2) using 1 <;> try rfl
      dsimp only [fourNorm]
      ring
    exact (hpI.dvd_mul.mp hh).resolve_left htwo
  have hD2 : (p : ℤ) ∣ d ^ 2 := by
    have hh : (p : ℤ) ∣ 2 * d ^ 2 := by
      convert dvd_sub (dvd_add h2 hnD) (dvd_mul_of_dvd_right hA2 2) using 1 <;> try rfl
      dsimp only [fourNorm]
      ring
    exact (hpI.dvd_mul.mp hh).resolve_left htwo
  have hA : (p : ℤ) ∣ a := hpI.dvd_of_dvd_pow hA2
  have hB : (p : ℤ) ∣ b := hpI.dvd_of_dvd_pow hB2
  have hC : (p : ℤ) ∣ c := hpI.dvd_of_dvd_pow hC2
  have hD : (p : ℤ) ∣ d := hpI.dvd_of_dvd_pow hD2
  have hpp : (p : ℤ) ^ 2 ∣ (p : ℤ) := by
    have hh : (p : ℤ) ^ 2 ∣ fourNorm a b c d :=
      dvd_add (dvd_add (dvd_add (pow_dvd_pow_of_dvd hA 2)
        (pow_dvd_pow_of_dvd hB 2)) (pow_dvd_pow_of_dvd hC 2)) (pow_dvd_pow_of_dvd hD 2)
    rwa [hn] at hh
  have hppI : (p : ℤ) * p ∣ (p : ℤ) := by simpa only [pow_two] using hpp
  have hppN : p * p ∣ p := by exact_mod_cast hppI
  exact hp.ne_one (Nat.isUnit_iff.mp (hp.squarefree p hppN))

end Erdos941
