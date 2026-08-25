import ErdosProblems.Erdos1058.Erdos1058PeriodicSieve

/-!
# A shared cubic-character sieve

Multiplicativity reduces the characters of `p * q` and `p * q^2` to the
characters of `p` and `q`.  Certify the three character classes at each small
modulus once.  Translation by the gap then becomes a rotation of their masks,
and the bounded sieve becomes an intersection of periodic sets.

The concrete certificates use only kernel reduction of natural-number
arithmetic.  No compiled-evaluation axiom or trusted generator is needed.
-/

set_option Elab.async false

namespace Erdos1058.PeriodicSieveCertificate

/-- Rotate a residue set to test membership of `p + d` at position `p`.
High bits need not be removed: the result is intersected with an unshifted
mask of residues below `r`. -/
def rotate (mask r d : ℕ) : ℕ :=
  (mask >>> (d % r)) ||| (mask <<< (r - d % r))

lemma rotate_accepts {mask r d p : ℕ} (hp : p < r)
    (hb : mask.testBit ((p + d) % r) = true) :
    (rotate mask r d).testBit p = true := by
  have hr : 0 < r := by omega
  have hd := Nat.mod_lt d hr
  have hm : (p + d) % r = (p + d % r) % r := by
    simpa only [Nat.mod_eq_of_lt hp] using Nat.add_mod p d r
  rw [rotate, Nat.testBit_or, Bool.or_eq_true]
  by_cases hsum : p + d % r < r
  · left
    rw [Nat.testBit_shiftRight]
    rw [hm, Nat.mod_eq_of_lt hsum] at hb
    simpa only [Nat.add_comm] using hb
  · right
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true]
    refine ⟨by simp only [decide_eq_true_eq]; omega, ?_⟩
    have heq : p + d % r = (p - (r - d % r)) + r := by omega
    have hlt : p - (r - d % r) < r := by omega
    rw [hm, heq] at hb
    simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt hlt] using hb

structure CharacterClass where
  value : ℕ
  bits : ℕ

structure CharacterRow where
  period : ℕ
  depth : ℕ
  classes : List CharacterClass

/-- Certify the character of each nonzero residue just once, independently
of the gap.  Every later gap uses only rotations and intersections. -/
def characterCheck (row : CharacterRow) : Bool :=
  decide (row.period ∈ cubicModuliList) &&
    decide (36000000 ≤ row.period * 2 ^ row.depth) &&
    (List.range row.period).all fun x =>
      decide (x = 0) || row.classes.any fun c =>
        decide (cubicPowModFuel ((row.period - 1) / 3) x
          ((row.period - 1) / 3) row.period = c.value) && c.bits.testBit x

lemma character_class_exists {row : CharacterRow} {p : ℕ}
    (hc : characterCheck row = true) (hp : p % row.period ≠ 0) :
    ∃ c ∈ row.classes, c.bits.testBit (p % row.period) = true ∧
      (p : ZMod row.period) ^ ((row.period - 1) / 3) = (c.value : ZMod row.period) := by
  simp only [characterCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hr : 0 < row.period := lt_of_lt_of_le (by decide) (seven_le_of_mem_cubicModuliList hc.1.1)
  have hx := List.all_eq_true.mp hc.2 (p % row.period)
    (List.mem_range.mpr (Nat.mod_lt _ hr))
  simp only [hp, decide_false, Bool.false_or, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨c, hcmem, hpow, hbit⟩ := hx
  refine ⟨c, hcmem, hbit, ?_⟩
  rw [cubicPowModFuel_eq_pow_mod Nat.lt_two_pow_self] at hpow
  have hcast := congrArg (fun n : ℕ => (n : ZMod row.period)) hpow
  simpa using hcast

def characterProduct (kind a b : ℕ) : ℕ :=
  if kind = 0 then a * b else if kind = 1 then a * (b * b) else a

def unions : List ℕ → ℕ
  | [] => 0
  | x :: xs => x ||| unions xs

lemma unions_accepts {xs : List ℕ} {x p : ℕ} (hx : x ∈ xs)
    (hb : x.testBit p = true) : (unions xs).testBit p = true := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [unions, Nat.testBit_or, Bool.or_eq_true]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl hb
      · exact Or.inr (ih hx)

def pairMask (d kind : ℕ) (row : CharacterRow) : ℕ :=
  unions (row.classes.flatMap fun a => row.classes.map fun b =>
    if characterProduct kind a.value b.value % row.period = 1 % row.period
    then a.bits &&& rotate b.bits row.period d else 0)

lemma pairMask_accepts {row : CharacterRow} {d kind p : ℕ}
    (hc : characterCheck row = true) (hk : kind ≤ 2)
    (hl : cubicCRTLocalForm d kind row.period p = true) :
    (pairMask d kind row).testBit (p % row.period) = true := by
  have hc' := hc
  simp only [characterCheck, Bool.and_eq_true, decide_eq_true_eq] at hc'
  have hr : 1 < row.period := lt_of_lt_of_le (by decide) (seven_le_of_mem_cubicModuliList hc'.1.1)
  obtain ⟨hpnz, hqnz, hpow⟩ := (cubicCRTLocalForm_eq_true_iff hr).mp hl
  obtain ⟨a, ha, hab, hap⟩ := character_class_exists hc hpnz
  obtain ⟨b, hb, hbb, hbp⟩ := character_class_exists hc hqnz
  have hprod : characterProduct kind a.value b.value % row.period = 1 % row.period := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ row.period).mp
    have hsquare : (((p + d : ℕ) : ZMod row.period) ^ 2) ^ ((row.period - 1) / 3) =
        (((p + d : ℕ) : ZMod row.period) ^ ((row.period - 1) / 3)) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
    interval_cases kind
    · rw [cast_cubicCRTLocalBase_zero, mul_pow, hap, hbp] at hpow
      simpa [characterProduct] using hpow
    · rw [cast_cubicCRTLocalBase_one, mul_pow, hsquare, hap, hbp] at hpow
      simpa [characterProduct, pow_two] using hpow
    · rw [cast_cubicCRTLocalBase_two, hap] at hpow
      simpa [characterProduct] using hpow
  unfold pairMask
  apply unions_accepts (x := a.bits &&& rotate b.bits row.period d)
  · apply List.mem_flatMap.mpr
    refine ⟨a, ha, List.mem_map.mpr ⟨b, hb, ?_⟩⟩
    simp only [if_pos hprod]
  · rw [Nat.testBit_and, Bool.and_eq_true]
    refine ⟨hab, rotate_accepts (Nat.mod_lt _ (by omega)) ?_⟩
    simpa only [Nat.mod_add_mod] using hbb

def toPeriodic (d kind : ℕ) (row : CharacterRow) : PeriodicMask :=
  ⟨row.period, pairMask d kind row, row.depth⟩

lemma character_intersection_accepts {rows : List CharacterRow} {d kind p : ℕ}
    (hc : rows.all characterCheck = true) (hk : kind ≤ 2) (hp : p < 36000000)
    (hl : ∀ r ∈ cubicModuliList, cubicCRTLocalForm d kind r p = true) :
    (intersection 36000000 (rows.map (toPeriodic d kind))).testBit p = true := by
  induction rows with
  | nil =>
      change (((1 : ℕ) <<< 36000000) - 1).testBit p = true
      exact interval_accepts hp
  | cons row rows ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hc
      change (tile (pairMask d kind row) row.period row.depth &&&
        intersection 36000000 (rows.map (toPeriodic d kind))).testBit p = true
      rw [Nat.testBit_and, Bool.and_eq_true]
      have hc' := hc.1
      simp only [characterCheck, Bool.and_eq_true, decide_eq_true_eq] at hc'
      refine ⟨tile_accepts (by have := seven_le_of_mem_cubicModuliList hc'.1.1; omega)
        (hp.trans_le hc'.1.2) (pairMask_accepts hc.1 hk (hl _ hc'.1.1)), ih hc.2⟩

lemma obstruction_of_character_certificate {rows : List CharacterRow} {d kind : ℕ}
    {exceptions : List ExceptionWitness} (hk : kind ≤ 2)
    (hrows : rows.all characterCheck = true)
    (hbits : intersection 36000000 (rows.map (toPeriodic d kind)) =
      positions (exceptions.map (·.position)))
    (hexceptions : exceptions.all (exceptionCheck d) = true) : Obstruction d kind := by
  intro p hp433 hp36 hp hq hlocal
  have hbit := character_intersection_accepts hrows hk hp36 hlocal
  rw [hbits, positions_spec] at hbit
  obtain ⟨w, hw, heq⟩ := List.mem_map.mp hbit
  exact exception_not_prime_pair (List.all_eq_true.mp hexceptions w hw) heq.symm hp433 hp hq

end Erdos1058.PeriodicSieveCertificate
