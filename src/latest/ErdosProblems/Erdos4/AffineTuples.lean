import ErdosProblems.Erdos4.JointSurvivalAsymptotic

/-!
# Geometry of the affine tuples

The tuple points are distinct. Two tuples with distinct sufficiently
large prime sources which contain one common target have no other
common point. This is the off-diagonal input for the conditional second
moment; it is an exact arithmetic statement.
-/

open scoped BigOperators

namespace Erdos4.AffineTuples

variable {k : ℕ}

def tuple (h : Fin k → ℕ) (p n : ℕ) : Finset ℕ :=
  Finset.univ.image (fun i => n + h i * p)

theorem mem_tuple (h : Fin k → ℕ) (p n q : ℕ) :
    q ∈ tuple h p n ↔ ∃ i : Fin k, n + h i * p = q := by
  simp [tuple]

theorem card_tuple (h : Fin k → ℕ) (hh : Function.Injective h) {p : ℕ} (hp : 0 < p)
    (n : ℕ) : (tuple h p n).card = k := by
  have hinj : Function.Injective (fun i : Fin k => n + h i * p) := by
    intro i j hij
    exact hh (mul_right_cancel₀ hp.ne' (Nat.add_left_cancel hij))
  simp only [tuple, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem shift_injective (K : ℕ) : Function.Injective (AffineWeights.shift K : Fin k → ℕ) := by
  intro i j hij
  apply Fin.ext
  exact mul_right_cancel₀ (primorial_pos K).ne' hij

theorem points_mod_source (h : Fin k → ℕ) (p n : ℕ) {q y : ℕ}
    (hq : q ∈ tuple h p n) (hy : y ∈ tuple h p n) : y ≡ q [MOD p] := by
  obtain ⟨i, rfl⟩ := (mem_tuple h p n q).mp hq
  obtain ⟨j, rfl⟩ := (mem_tuple h p n y).mp hy
  simp [Nat.ModEq, Nat.add_mod]

theorem shift_mod_other_source_injective (K : ℕ) {p p' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hK : K < p) (hk : k ≤ p) (hne : p ≠ p')
    (n : ℕ) : Function.Injective
      (fun i : Fin k => (n + AffineWeights.shift K i * p' : ℕ) : Fin k → ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hW : (primorial K : ZMod p) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hK) (hp.dvd_primorial_iff.mp
      ((ZMod.natCast_eq_zero_iff (primorial K) p).mp hz))
  have hp'0 : (p' : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ p' := (ZMod.natCast_eq_zero_iff p' p).mp hz
    exact hne ((Nat.dvd_prime hp').mp hd |>.resolve_left hp.ne_one)
  intro i j hij
  simp only [Nat.cast_add, Nat.cast_mul, AffineWeights.shift] at hij
  have hmul : (i.val : ZMod p) * ((primorial K : ZMod p) * (p' : ZMod p)) =
      (j.val : ZMod p) * ((primorial K : ZMod p) * (p' : ZMod p)) := by
    have hh := add_left_cancel hij
    simpa only [Nat.cast_mul, mul_assoc] using hh
  have hval := mul_right_cancel₀ (mul_ne_zero hW hp'0) hmul
  have hmod := (ZMod.natCast_eq_natCast_iff i.val j.val p).mp hval
  exact Fin.ext (hmod.eq_of_lt_of_lt (i.isLt.trans_le hk) (j.isLt.trans_le hk))

/-- Distinct prime sources cannot create a second intersection point in
two tuples already anchored at the same target. -/
theorem common_point_unique (K : ℕ) {p p' n n' q y : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hK : K < p) (hk : k ≤ p) (hne : p ≠ p')
    (hq : q ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n)
    (hq' : q ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p' n')
    (hy : y ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n)
    (hy' : y ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p' n') : y = q := by
  have hmod := points_mod_source (AffineWeights.shift K) p n hq hy
  obtain ⟨i, hi⟩ := (mem_tuple (AffineWeights.shift K) p' n' y).mp hy'
  obtain ⟨j, hj⟩ := (mem_tuple (AffineWeights.shift K) p' n' q).mp hq'
  have heq : i = j := shift_mod_other_source_injective K hp hp' hK hk hne n'
    ((ZMod.natCast_eq_natCast_iff _ _ p).mpr (by simpa only [hi, hj] using hmod))
  subst j
  exact hi.symm.trans hj

theorem intersection_eq_singleton (K : ℕ) {p p' n n' q : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hK : K < p) (hk : k ≤ p) (hne : p ≠ p')
    (hq : q ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n)
    (hq' : q ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p' n') :
    tuple (AffineWeights.shift K : Fin k → ℕ) p n ∩
      tuple (AffineWeights.shift K : Fin k → ℕ) p' n' = {q} := by
  ext y
  constructor
  · intro hy
    exact Finset.mem_singleton.mpr (common_point_unique K hp hp' hK hk hne hq hq'
      (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2)
  · intro hy
    have heq := Finset.mem_singleton.mp hy
    subst y
    exact Finset.mem_inter.mpr ⟨hq, hq'⟩

end Erdos4.AffineTuples
