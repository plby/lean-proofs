/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.PadicIsometry

/-!
# Erdős 730: finite higher-power counting

This file isolates the unconditional finite counting statements used in
§5 of the positive-density proof.  There are two independent parts.

* A predicate on residues modulo `q` occurs in an interval of `N`
  consecutive integers at most `(N / q + 1)` times its full-period count.
  Applying this to a bijective p-adic branch map gives the complete/padded
  block bound in (26), including depth `r = 0`.
* The finite set of pairs `(p,a)` with `p` prime, `a ≥ 2`, and `p^a ≤ Z`
  has cardinality at most
  `sqrt Z + cubeRootFloor Z * log 2 Z`.  This is the exact natural-number
  form of (27).

No asymptotic assertion is made here.
-/

namespace Erdos730

/-! ## Consecutive intervals modulo a positive modulus -/

/-- Number of offsets `i < N` for which `start + i` has an allowed residue
modulo `q`. -/
def intervalResidueCount (q start N : ℕ) (P : ZMod q → Prop)
    [DecidablePred P] : ℕ :=
  (Finset.range N).filter (fun i ↦ P ((start + i : ℕ) : ZMod q)) |>.card

/-- A consecutive interval meets an allowed residue set no more often than
the number of offset blocks times the number of allowed residues in one
complete period.  The harmless `+1` is the padded final block.

This theorem is deliberately stated for arbitrary predicates on `ZMod q`;
the p-adic polynomial enters only in the corollary below. -/
theorem intervalResidueCount_le
    {q start N : ℕ} [NeZero q] (P : ZMod q → Prop) [DecidablePred P] :
    intervalResidueCount q start N P ≤
      (N / q + 1) * (Finset.univ.filter P).card := by
  let source : Finset ℕ :=
    (Finset.range N).filter (fun i ↦ P ((start + i : ℕ) : ZMod q))
  let target : Type := Fin (N / q + 1) × ↑(Finset.univ.filter P)
  let encode : ↑source → target := fun i ↦
    (⟨i.1 / q, by
        apply Nat.lt_succ_iff.mpr
        apply Nat.div_le_div_right
        exact (Finset.mem_range.mp (Finset.mem_filter.mp i.2).1).le⟩,
      ⟨((start + i.1 : ℕ) : ZMod q), by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp i.2).2⟩⟩)
  have hencode : Function.Injective encode := by
    intro i j hij
    have hdiv : i.1 / q = j.1 / q := by
      simpa [encode] using congrArg (fun z : target ↦ (z.1 : ℕ)) hij
    have hcast : ((start + i.1 : ℕ) : ZMod q) =
        ((start + j.1 : ℕ) : ZMod q) := by
      simpa [encode] using congrArg (fun z : target ↦ (z.2.1 : ZMod q)) hij
    have hadd : start + i.1 ≡ start + j.1 [MOD q] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have hmod : i.1 % q = j.1 % q := by
      exact Nat.ModEq.add_left_cancel' start hadd
    apply Subtype.ext
    calc
      i.1 = q * (i.1 / q) + i.1 % q := (Nat.div_add_mod i.1 q).symm
      _ = q * (j.1 / q) + j.1 % q := by rw [hdiv, hmod]
      _ = j.1 := Nat.div_add_mod j.1 q
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [intervalResidueCount, source, target, Fintype.card_subtype] using hcard

/-- The count after a bijection of residues is bounded by the number of
padded blocks times the cardinality of the allowed image set. -/
theorem interval_bijective_preimage_count_le
    {q start N : ℕ} [NeZero q]
    (G : ZMod q → ZMod q) (hG : Function.Bijective G)
    (A : Finset (ZMod q)) :
    intervalResidueCount q start N (fun z ↦ G z ∈ A) ≤
      (N / q + 1) * A.card := by
  calc
    intervalResidueCount q start N (fun z ↦ G z ∈ A) ≤
        (N / q + 1) * (Finset.univ.filter fun z ↦ G z ∈ A).card :=
      intervalResidueCount_le _
    _ = (N / q + 1) * A.card := by
      rw [card_filter_preimage_of_bijective G hG A]

/-! ## The p-adic branch-map block bound -/

/-- Count of offsets in a consecutive parameter interval whose image under a
p-adic branch map belongs to `A`. -/
def padicBranchAllowedCount
    (p r start N : ℕ) (q u b v : ZMod (p ^ r))
    (A : Finset (ZMod (p ^ r))) : ℕ :=
  intervalResidueCount (p ^ r) start N
    (fun z ↦ padicBranchMap (p : ZMod (p ^ r)) q u b v z ∈ A)

/-- Complete/padded block form of the first inequality in (26).

If the allowed set has `H^r` residues, an interval of `N` parameters contains
at most `(N / p^r + 1) H^r` allowed branch values.  There is no `r ≥ 1`
hypothesis: at `r = 0`, `ZMod (p^0)` is the one-element ring and the bound is
the intended vacuous digit bound. -/
theorem padicBranchAllowedCount_le
    {p r start N H : ℕ} (hp : p.Prime)
    (q u v : ZMod (p ^ r)) {b : ZMod (p ^ r)} (hb : IsUnit b)
    (A : Finset (ZMod (p ^ r))) (hA : A.card = H ^ r) :
    padicBranchAllowedCount p r start N q u b v A ≤
      (N / p ^ r + 1) * H ^ r := by
  let : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  unfold padicBranchAllowedCount
  calc
    intervalResidueCount (p ^ r) start N
          (fun z ↦ padicBranchMap (p : ZMod (p ^ r)) q u b v z ∈ A)
        ≤ (N / p ^ r + 1) * A.card :=
      interval_bijective_preimage_count_le _
        (padicBranchMap_bijective hp.pos hb q u v) A
    _ = (N / p ^ r + 1) * H ^ r := by rw [hA]

/-- Version used when a root progression has at most `U+1` parameters.
This is the exact finite, floor-valued form of the first bound in (26). -/
theorem padicBranchAllowedCount_le_of_length
    {p r start N H U : ℕ} (hp : p.Prime)
    (q u v : ZMod (p ^ r)) {b : ZMod (p ^ r)} (hb : IsUnit b)
    (A : Finset (ZMod (p ^ r))) (hA : A.card = H ^ r)
    (hN : N ≤ U + 1) :
    padicBranchAllowedCount p r start N q u b v A ≤
      ((U + 1) / p ^ r + 1) * H ^ r := by
  calc
    padicBranchAllowedCount p r start N q u b v A
        ≤ (N / p ^ r + 1) * H ^ r :=
      padicBranchAllowedCount_le hp q u v hb A hA
    _ ≤ ((U + 1) / p ^ r + 1) * H ^ r := by
      exact Nat.mul_le_mul_right _
        (Nat.add_le_add_right (Nat.div_le_div_right hN) 1)

/-! ## Exact finite higher-prime-power pair count -/

/-- Floor cube root, defined without introducing an analytic real root. -/
def cubeRootFloor (Z : ℕ) : ℕ :=
  Nat.findGreatest (fun n ↦ n ^ 3 ≤ Z) Z

/-- The floor cube root really has cube at most `Z`. -/
theorem cubeRootFloor_pow_le (Z : ℕ) : cubeRootFloor Z ^ 3 ≤ Z := by
  unfold cubeRootFloor
  exact Nat.findGreatest_spec (P := fun n ↦ n ^ 3 ≤ Z) (m := 0)
    (Nat.zero_le Z) (by norm_num)

/-- Every natural whose cube is at most `Z` is at most the floor cube root. -/
theorem le_cubeRootFloor {n Z : ℕ} (hnZ : n ≤ Z) (hcube : n ^ 3 ≤ Z) :
    n ≤ cubeRootFloor Z := by
  exact Nat.le_findGreatest hnZ hcube

/-- The finite set counted by `M(Z)` in (27).  The range bounds are redundant
under the filter conditions; they only make the set computationally finite. -/
def higherPrimePowerPairs (Z : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Z + 1)).product (Finset.range (Nat.log 2 Z + 1))).filter
    (fun pa ↦ pa.1.Prime ∧ 2 ≤ pa.2 ∧ pa.1 ^ pa.2 ≤ Z)

/-- The computational range bounds in `higherPrimePowerPairs` lose no pairs:
this is exactly the predicate defining `M(Z)` in the paper. -/
theorem mem_higherPrimePowerPairs_iff {p a Z : ℕ} :
    (p, a) ∈ higherPrimePowerPairs Z ↔
      p.Prime ∧ 2 ≤ a ∧ p ^ a ≤ Z := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hp, ha2, hpow⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
      Finset.mem_range.mpr ?_⟩, ⟨hp, ha2, hpow⟩⟩
    · have hp_le_pow : p ≤ p ^ a := by
        calc
          p = p ^ 1 := by simp
          _ ≤ p ^ a := pow_le_pow_right' hp.one_le (by omega)
      omega
    · have htwoPow : 2 ^ a ≤ Z :=
        (Nat.pow_le_pow_left hp.two_le a).trans hpow
      have haLog : a ≤ Nat.log 2 Z :=
        Nat.le_log_of_pow_le (by norm_num) htwoPow
      omega

/-- Every higher-prime-power pair lies either on the square row below
`sqrt Z`, or in the rectangle below `cubeRootFloor Z` and `log_2 Z`. -/
theorem higherPrimePowerPairs_subset_boxes (Z : ℕ) :
    higherPrimePowerPairs Z ⊆
      ((Finset.Icc 2 (Nat.sqrt Z)).product {2}) ∪
        ((Finset.Icc 2 (cubeRootFloor Z)).product
          (Finset.Icc 3 (Nat.log 2 Z))) := by
  intro pa hpa
  rcases mem_higherPrimePowerPairs_iff.mp hpa with ⟨hp, ha2, hpow⟩
  by_cases hea : pa.2 = 2
  · apply Finset.mem_union_left
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩,
      Finset.mem_singleton.mpr hea⟩
    exact Nat.le_sqrt'.2 (by simpa [hea] using hpow)
  · apply Finset.mem_union_right
    have ha3 : 3 ≤ pa.2 := by omega
    have hpone : 1 ≤ pa.1 := hp.one_le
    have hp3 : pa.1 ^ 3 ≤ Z :=
      (pow_le_pow_right' hpone ha3).trans hpow
    have hp_le_cube : pa.1 ≤ pa.1 ^ 3 := by
      calc
        pa.1 = pa.1 ^ 1 := by simp
        _ ≤ pa.1 ^ 3 := pow_le_pow_right' hpone (by omega)
    have hp_le_Z : pa.1 ≤ Z := hp_le_cube.trans hp3
    have hpCube : pa.1 ≤ cubeRootFloor Z := le_cubeRootFloor hp_le_Z hp3
    have htwoPow : 2 ^ pa.2 ≤ Z :=
      (Nat.pow_le_pow_left hp.two_le pa.2).trans hpow
    have haBound : pa.2 ≤ Nat.log 2 Z :=
      Nat.le_log_of_pow_le (by norm_num) htwoPow
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpCube⟩,
        Finset.mem_Icc.mpr ⟨ha3, haBound⟩⟩

/-- Exact finite inequality behind (27):

`M(Z) ≤ floor(sqrt Z) + floor(cuberoot Z) * floor(log_2 Z)`.

The paper's displayed bound uses the corresponding real quantities, which
are weakly larger. -/
theorem higherPrimePowerPairs_card_le (Z : ℕ) :
    (higherPrimePowerPairs Z).card ≤
      Nat.sqrt Z + cubeRootFloor Z * Nat.log 2 Z := by
  let squares : Finset (ℕ × ℕ) :=
    (Finset.Icc 2 (Nat.sqrt Z)).product {2}
  let higher : Finset (ℕ × ℕ) :=
    (Finset.Icc 2 (cubeRootFloor Z)).product
      (Finset.Icc 3 (Nat.log 2 Z))
  have hsubset : higherPrimePowerPairs Z ⊆ squares ∪ higher := by
    simpa [squares, higher] using higherPrimePowerPairs_subset_boxes Z
  have hsq : squares.card ≤ Nat.sqrt Z := by
    have hcard := Finset.card_product (Finset.Icc 2 (Nat.sqrt Z)) ({2} : Finset ℕ)
    rw [Nat.card_Icc, Finset.card_singleton, mul_one] at hcard
    rw [show squares.card = Nat.sqrt Z + 1 - 2 from hcard]
    omega
  have hhigher : higher.card ≤ cubeRootFloor Z * Nat.log 2 Z := by
    have hcard := Finset.card_product (Finset.Icc 2 (cubeRootFloor Z))
      (Finset.Icc 3 (Nat.log 2 Z))
    rw [Nat.card_Icc, Nat.card_Icc] at hcard
    rw [show higher.card =
      (cubeRootFloor Z + 1 - 2) * (Nat.log 2 Z + 1 - 3) from hcard]
    apply Nat.mul_le_mul <;> omega
  calc
    (higherPrimePowerPairs Z).card ≤ (squares ∪ higher).card :=
      Finset.card_le_card hsubset
    _ ≤ squares.card + higher.card := Finset.card_union_le _ _
    _ ≤ Nat.sqrt Z + cubeRootFloor Z * Nat.log 2 Z :=
      Nat.add_le_add hsq hhigher

end Erdos730
