import ErdosProblems.Erdos486.BiasedColoring

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic collision counts for the biased-colouring block

For a subset `S` and an index `i ∉ S`, reduction modulo `q_S` and modulo
`p_i` is independent: the two moduli are coprime.  We choose a canonical
endpoint representing each residue modulo `q_S` (and use zero if there is no
such endpoint).  The residues for which the `p_i`-coordinate agrees with this
candidate form the graph of a function

`ZMod q_S → ZMod p_i`.

The Chinese remainder theorem therefore gives exactly one admissible
`p_i`-coordinate above every `q_S`-coordinate.  This file carries that count
from the pair period `q_S * p_i` to the explicit common period
`biasedPeriod j`.
-/

namespace Erdos486

/-- A canonical endpoint representing `z` modulo `q_S`.  If the endpoint
interval contains no representative, use zero.  At scales `j ≥ 400`, the
representative is unique by `candidateEndpoints_card_le_one`. -/
noncomputable def biasedCandidate (j : ℕ)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S)) : ℕ :=
  if h : (candidateEndpoints j S z).Nonempty then h.choose else 0

theorem biasedCandidate_mem_of_nonempty {j : ℕ}
    {S : Finset (Fin (biasedK j))} {z : ZMod (biasedModulus j S)}
    (h : (candidateEndpoints j S z).Nonempty) :
    biasedCandidate j S z ∈ candidateEndpoints j S z := by
  simp only [biasedCandidate, dif_pos h]
  exact h.choose_spec

/-- At relevant scales, any endpoint representing `z` is the canonical one. -/
theorem biasedCandidate_eq_of_mem {j m : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S))
    (hm : m ∈ candidateEndpoints j S z) :
    biasedCandidate j S z = m := by
  classical
  have hne : (candidateEndpoints j S z).Nonempty := ⟨m, hm⟩
  have hc := biasedCandidate_mem_of_nonempty hne
  have hcard := candidateEndpoints_card_le_one hj S z
  rw [Finset.card_le_one_iff] at hcard
  exact hcard hc hm

/-- If `i ∉ S`, the subset modulus `q_S` is coprime to `p_i`. -/
theorem biasedModulus_coprime_skeletonPrime {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    Nat.Coprime (biasedModulus j S) (skeletonPrime (biasedK j) i) := by
  have hp : (skeletonPrime (biasedK j) i).Prime :=
    (skeletonPrime_spec (biasedK j) i).1
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  rwa [skeletonPrime_dvd_biasedModulus_iff]

/-- The extra prime `p_i` divides the explicit common period, since it divides
the factor indexed by `insert i S`. -/
theorem skeletonPrime_dvd_biasedPeriod (j : ℕ) (i : Fin (biasedK j)) :
    skeletonPrime (biasedK j) i ∣ biasedPeriod j := by
  apply dvd_trans (b := biasedModulus j {i})
  · rw [skeletonPrime_dvd_biasedModulus_iff]
    simp
  · exact biasedModulus_dvd_period j {i}

/-- The pair period `q_S p_i` divides the common period. -/
theorem biasedPairPeriod_dvd_biasedPeriod {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    biasedModulus j S * skeletonPrime (biasedK j) i ∣ biasedPeriod j := by
  exact (biasedModulus_coprime_skeletonPrime S i hi).mul_dvd_of_dvd_of_dvd
    (biasedModulus_dvd_period j S) (skeletonPrime_dvd_biasedPeriod j i)

/-- Collision with the `p_i`-coordinate of the canonical endpoint determined
by the residue of `x` modulo `q_S`. -/
def IsBiasedCollision (j : ℕ) (S : Finset (Fin (biasedK j)))
    (i : Fin (biasedK j)) (x : ℕ) : Prop :=
  (x : ZMod (skeletonPrime (biasedK j) i)) =
    (biasedCandidate j S (x : ZMod (biasedModulus j S)) :
      ZMod (skeletonPrime (biasedK j) i))

noncomputable instance instDecidableIsBiasedCollision (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (x : ℕ) :
    Decidable (IsBiasedCollision j S i x) := by
  unfold IsBiasedCollision
  infer_instance

/-- The collision relation is periodic with pair period `q_S p_i`. -/
theorem isBiasedCollision_periodic (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    Function.Periodic (IsBiasedCollision j S i)
      (biasedModulus j S * skeletonPrime (biasedK j) i) := by
  intro x
  simp [IsBiasedCollision, Nat.cast_add, Nat.cast_mul]

/-- The graph of a function has one point over each element of its domain. -/
private def functionGraphEquiv {α β : Type*} (f : α → β) :
    {y : α × β // y.2 = f y.1} ≃ α where
  toFun y := y.1.1
  invFun a := ⟨(a, f a), rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    exact Prod.ext rfl hab.symm
  right_inv := by
    intro a
    rfl

/-- CRT identifies the collision residues in a pair period with the graph of
an arbitrary function `ZMod q → ZMod p`. -/
private noncomputable def finChineseRemainderEquiv (q p : ℕ)
    [NeZero q] [NeZero p] (hqp : Nat.Coprime q p) :
    Fin (q * p) ≃ ZMod q × ZMod p where
  toFun x := ((x.val : ZMod q), (x.val : ZMod p))
  invFun y :=
    ⟨((ZMod.chineseRemainder hqp).symm y).val, ZMod.val_lt _⟩
  left_inv x := by
    apply Fin.ext
    change ((ZMod.chineseRemainder hqp).symm
      ((x.val : ZMod q), (x.val : ZMod p))).val = x.val
    have hz : (ZMod.chineseRemainder hqp).symm
        ((x.val : ZMod q), (x.val : ZMod p)) =
        (x.val : ZMod (q * p)) := by
      apply (ZMod.chineseRemainder hqp).injective
      rw [(ZMod.chineseRemainder hqp).apply_symm_apply]
      change ((x.val : ZMod q), (x.val : ZMod p)) =
        (ZMod.cast (x.val : ZMod (q * p)) : ZMod q × ZMod p)
      apply Prod.ext <;> simp
    rw [hz, ZMod.val_natCast_of_lt x.isLt]
  right_inv y := by
    let z := (ZMod.chineseRemainder hqp).symm y
    change ((z.val : ZMod q), (z.val : ZMod p)) = y
    calc
      ((z.val : ZMod q), (z.val : ZMod p)) =
          (ZMod.chineseRemainder hqp) z := by
        change ((z.val : ZMod q), (z.val : ZMod p)) =
          (ZMod.cast z : ZMod q × ZMod p)
        apply Prod.ext <;> simp [ZMod.natCast_val]
      _ = y := (ZMod.chineseRemainder hqp).apply_symm_apply y

private noncomputable def modCollisionEquiv (q p : ℕ)
    [NeZero q] [NeZero p] (hqp : Nat.Coprime q p)
    (f : ZMod q → ZMod p) :
    {x : Fin (q * p) //
      (x.val : ZMod p) = f (x.val : ZMod q)} ≃ ZMod q := by
  let e : Fin (q * p) ≃ ZMod q × ZMod p :=
    finChineseRemainderEquiv q p hqp
  refine (e.subtypeEquiv ?_).trans (functionGraphEquiv f)
  intro x
  change ((x.val : ZMod p) = f (x.val : ZMod q)) ↔
    (e x).2 = f (e x).1
  rfl

/-- In one pair period, the collision graph has exactly `q` representatives. -/
theorem count_mod_collision_eq (q p : ℕ) [NeZero q] [NeZero p]
    (hqp : Nat.Coprime q p) (f : ZMod q → ZMod p) :
    (q * p).count
      (fun x : ℕ ↦ (x : ZMod p) = f (x : ZMod q)) = q := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let P : ℕ → Prop := fun x ↦ (x : ZMod p) = f (x : ZMod q)
  let s := (Finset.range (q * p)).filter P
  have hslt : ∀ x ∈ s, x < q * p := by
    intro x hx
    exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  have hsattach : s.attachFin hslt =
      (Finset.univ.filter fun x : Fin (q * p) ↦
        (x.val : ZMod p) = f (x.val : ZMod q)) := by
    ext x
    simp [s, P]
  change s.card = q
  rw [← Finset.card_attachFin s hslt, hsattach,
    ← Fintype.card_subtype]
  exact (Fintype.card_congr (modCollisionEquiv q p hqp f)).trans
    (ZMod.card q)

/-- Repeating a periodic predicate through `t` complete periods multiplies
its count by `t`. -/
theorem count_mul_of_periodic (P : ℕ → Prop) [DecidablePred P]
    (a t : ℕ) (hP : Function.Periodic P a) :
    (t * a).count P = t * a.count P := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_mul, Nat.count_add, ih]
      have hshift : (fun k ↦ P (t * a + k)) = P := by
        funext k
        simpa [Nat.nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using
          (hP.nsmul t) k
      simp only [hshift]
      simp [Nat.add_mul]

/-- In the pair period `q_S p_i`, the biased collision relation has exactly
`q_S` representatives. -/
theorem biasedCollision_pair_count {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    (biasedModulus j S * skeletonPrime (biasedK j) i).count
      (IsBiasedCollision j S i) = biasedModulus j S := by
  letI : NeZero (biasedModulus j S) :=
    ⟨(biasedModulus_pos j S).ne'⟩
  letI : NeZero (skeletonPrime (biasedK j) i) :=
    biasedPrimeNeZero (biasedK j) i
  simpa only [IsBiasedCollision] using!
    count_mod_collision_eq (biasedModulus j S)
      (skeletonPrime (biasedK j) i)
      (biasedModulus_coprime_skeletonPrime S i hi)
      (fun z ↦ (biasedCandidate j S z :
        ZMod (skeletonPrime (biasedK j) i)))

/-- Number of collisions among the canonical representatives
`0, ..., biasedPeriod j - 1`. -/
noncomputable def biasedCollisionCount (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) : ℕ := by
  classical
  exact (biasedPeriod j).count (IsBiasedCollision j S i)

/-- The collision set has exact proportion `1 / p_i` in the explicit common
period.  The cross-multiplied form avoids division and coercions. -/
theorem skeletonPrime_mul_biasedCollisionCount_eq_period {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    skeletonPrime (biasedK j) i * biasedCollisionCount j S i =
      biasedPeriod j := by
  classical
  let q := biasedModulus j S
  let p := skeletonPrime (biasedK j) i
  let N := biasedPeriod j
  have hdiv : q * p ∣ N := biasedPairPeriod_dvd_biasedPeriod S i hi
  rcases hdiv with ⟨t, ht⟩
  have hpair : (q * p).count (IsBiasedCollision j S i) = q := by
    simpa only [q, p] using biasedCollision_pair_count S i hi
  have hperiod : Function.Periodic (IsBiasedCollision j S i) (q * p) := by
    simpa only [q, p] using isBiasedCollision_periodic j S i
  calc
    skeletonPrime (biasedK j) i * biasedCollisionCount j S i =
        p * ((t * (q * p)).count (IsBiasedCollision j S i)) := by
      simp only [p, biasedCollisionCount, N] at ht ⊢
      rw [ht, Nat.mul_comm (q * p) t]
    _ = p * (t * (q * p).count (IsBiasedCollision j S i)) := by
      rw [count_mul_of_periodic _ _ _ hperiod]
    _ = p * (t * q) := by rw [hpair]
    _ = (q * p) * t := by ring
    _ = N := ht.symm

/-- In particular, the requested collision-cardinality bound holds. -/
theorem skeletonPrime_mul_biasedCollisionCount_le_period {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    skeletonPrime (biasedK j) i * biasedCollisionCount j S i ≤
      biasedPeriod j :=
  (skeletonPrime_mul_biasedCollisionCount_eq_period S i hi).le

/-- An actual endpoint matching `x` modulo both `q_S` and `p_i` satisfies the
canonical collision relation. -/
theorem isBiasedCollision_of_endpoint {j x m : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j))
    (hm : m ∈ biasedEndpoints j)
    (hq : (x : ZMod (biasedModulus j S)) =
      (m : ZMod (biasedModulus j S)))
    (hp : (x : ZMod (skeletonPrime (biasedK j) i)) =
      (m : ZMod (skeletonPrime (biasedK j) i))) :
    IsBiasedCollision j S i x := by
  have hmCandidate : m ∈
      candidateEndpoints j S (x : ZMod (biasedModulus j S)) := by
    simp only [candidateEndpoints, Finset.mem_filter]
    exact ⟨hm, hq.symm⟩
  have hcandidate := biasedCandidate_eq_of_mem hj S
    (x : ZMod (biasedModulus j S)) hmCandidate
  rw [IsBiasedCollision, hcandidate]
  exact hp

end Erdos486
