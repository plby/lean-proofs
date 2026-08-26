import ErdosProblems.Erdos394.RootBoxFirstMoment

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact local counts behind the general root-pair congruence lattice

For a prime `p`, a pair of root labels `(A,B)` imposes two independent zero
conditions only when both labels vanish.  In every other case it imposes one
linear condition on the residue pair `(j,l)`.  Thus the local underlying
lattice index is `p²` in the both-zero case and `p` otherwise.
-/

open Nat Finset

namespace Erdos394

noncomputable local instance zmodFintypePair (p : ℕ) [NeZero p] :
    Fintype (ZMod p) := Fintype.ofFinite _

/-- Underlying local congruence set for one pair of root labels.  Nonvanishing
conditions on exact labels are deliberately omitted; this is the rank-two
lattice used in the pair-moment argument. -/
noncomputable def localPairCongruenceSet (p A B : ℕ) [NeZero p] :
    Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun jl ↦
    if A = 0 ∧ B = 0 then jl.1 = 0 ∧ jl.2 = 0
    else if A = 0 then jl.1 = 0
    else if B = 0 then jl.2 = 0
    else (A : ZMod p) * jl.2 = (B : ZMod p) * jl.1

/-- Exact-label-compatible local residue pairs.  Relative to the underlying
lattice, every non-both-zero prime removes the origin. -/
noncomputable def localExactPairSet (p A B : ℕ) [NeZero p] :
    Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun jl ↦
    if A = 0 ∧ B = 0 then jl.1 = 0 ∧ jl.2 = 0
    else if A = 0 then jl.1 = 0 ∧ jl.2 ≠ 0
    else if B = 0 then jl.1 ≠ 0 ∧ jl.2 = 0
    else jl.1 ≠ 0 ∧ jl.2 ≠ 0 ∧
      (A : ZMod p) * jl.2 = (B : ZMod p) * jl.1

/-- A positive natural below the modulus has nonzero cast in `ZMod`. -/
theorem natCast_zmod_ne_zero_of_pos_of_lt {p A : ℕ} (hApos : 0 < A)
    (hAlt : A < p) : (A : ZMod p) ≠ 0 := by
  intro hz
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hAlt, ZMod.val_zero] at hv
  omega

/-- In the both-zero-label case there is exactly one local residue pair. -/
theorem card_localPairCongruenceSet_zero_zero (p : ℕ) [NeZero p] :
    (localPairCongruenceSet p 0 0).card = 1 := by
  classical
  have heq : localPairCongruenceSet p 0 0 = {(0, 0)} := by
    ext jl
    simp [localPairCongruenceSet, Prod.ext_iff]
  rw [heq]
  simp

/-- If only the first label is zero, the first coordinate is forced and the
second is free. -/
theorem card_localPairCongruenceSet_zero_nonzero {p B : ℕ} [NeZero p]
    (hB : B ≠ 0) :
    (localPairCongruenceSet p 0 B).card = p := by
  classical
  let s := localPairCongruenceSet p 0 B
  calc
    s.card = (Finset.univ : Finset (ZMod p)).card := by
      apply Finset.card_bij (fun jl _ ↦ jl.2)
      · intro jl hjl
        exact Finset.mem_univ _
      · intro a ha b hb hab
        have ha0 : a.1 = 0 := by
          simpa [s, localPairCongruenceSet, hB] using
            (Finset.mem_filter.mp ha).2
        have hb0 : b.1 = 0 := by
          simpa [s, localPairCongruenceSet, hB] using
            (Finset.mem_filter.mp hb).2
        apply Prod.ext
        · rw [ha0, hb0]
        · exact hab
      · intro l hl
        refine ⟨(0, l), ?_, rfl⟩
        simp [s, localPairCongruenceSet, hB]
    _ = p := by simp [ZMod.card]

/-- If only the second label is zero, the second coordinate is forced and the
first is free. -/
theorem card_localPairCongruenceSet_nonzero_zero {p A : ℕ} [NeZero p]
    (hA : A ≠ 0) :
    (localPairCongruenceSet p A 0).card = p := by
  classical
  let s := localPairCongruenceSet p A 0
  calc
    s.card = (Finset.univ : Finset (ZMod p)).card := by
      apply Finset.card_bij (fun jl _ ↦ jl.1)
      · intro jl hjl
        exact Finset.mem_univ _
      · intro a ha b hb hab
        have ha0 : a.2 = 0 := by
          simpa [s, localPairCongruenceSet, hA] using
            (Finset.mem_filter.mp ha).2
        have hb0 : b.2 = 0 := by
          simpa [s, localPairCongruenceSet, hA] using
            (Finset.mem_filter.mp hb).2
        apply Prod.ext
        · exact hab
        · rw [ha0, hb0]
      · intro j hj
        refine ⟨(j, 0), ?_, rfl⟩
        simp [s, localPairCongruenceSet, hA]
    _ = p := by simp [ZMod.card]

/-- With two nonzero labels below `p`, one coordinate determines the other,
so there are exactly `p` local residue pairs. -/
theorem card_localPairCongruenceSet_nonzero_nonzero {p A B : ℕ} [NeZero p]
    (hp : p.Prime) (hApos : 0 < A) (hAlt : A < p) (hB : B ≠ 0) :
    (localPairCongruenceSet p A B).card = p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let s := localPairCongruenceSet p A B
  have hA : A ≠ 0 := Nat.ne_of_gt hApos
  have hAz : (A : ZMod p) ≠ 0 :=
    natCast_zmod_ne_zero_of_pos_of_lt hApos hAlt
  calc
    s.card = (Finset.univ : Finset (ZMod p)).card := by
      apply Finset.card_bij (fun jl _ ↦ jl.1)
      · intro jl hjl
        exact Finset.mem_univ _
      · intro a ha b hb hab
        have harel : (A : ZMod p) * a.2 = (B : ZMod p) * a.1 := by
          simpa [s, localPairCongruenceSet, hA, hB] using
            (Finset.mem_filter.mp ha).2
        have hbrel : (A : ZMod p) * b.2 = (B : ZMod p) * b.1 := by
          simpa [s, localPairCongruenceSet, hA, hB] using
            (Finset.mem_filter.mp hb).2
        apply Prod.ext
        · exact hab
        · apply mul_left_cancel₀ hAz
          rw [harel, hbrel, hab]
      · intro j hj
        let l : ZMod p := (A : ZMod p)⁻¹ * (B : ZMod p) * j
        refine ⟨(j, l), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [localPairCongruenceSet, hA, hB, and_self, if_false, s]
        dsimp [l]
        field_simp
    _ = p := by simp [ZMod.card]

/-- Uniform local cardinality: one residue pair for two zero labels and `p`
residue pairs in every one-equation case. -/
theorem card_localPairCongruenceSet {p K A B : ℕ} [NeZero p] (hp : p.Prime)
    (hA : A < K) (hB : B < K) (hKp : K < p) :
    (localPairCongruenceSet p A B).card =
      if A = 0 ∧ B = 0 then 1 else p := by
  by_cases hAz : A = 0
  · subst A
    by_cases hBz : B = 0
    · subst B
      simp [card_localPairCongruenceSet_zero_zero]
    · simp [hBz, card_localPairCongruenceSet_zero_nonzero hBz]
  · by_cases hBz : B = 0
    · subst B
      simp [hAz, card_localPairCongruenceSet_nonzero_zero hAz]
    · have hApos : 0 < A := Nat.pos_of_ne_zero hAz
      have hAlt : A < p := hA.trans hKp
      simp [hAz, hBz,
        card_localPairCongruenceSet_nonzero_nonzero hp hApos hAlt hBz]

/-- The nonzero residues modulo `p`. -/
noncomputable def nonzeroZModFinset (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.erase 0

/-- There are exactly `p-1` nonzero residues modulo a positive `p`. -/
theorem card_nonzeroZModFinset (p : ℕ) [NeZero p] :
    (nonzeroZModFinset p).card = p - 1 := by
  classical
  unfold nonzeroZModFinset
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p))]
  simp [ZMod.card]

/-- Exact labels `(0,0)` allow only the origin. -/
theorem card_localExactPairSet_zero_zero (p : ℕ) [NeZero p] :
    (localExactPairSet p 0 0).card = 1 := by
  classical
  have heq : localExactPairSet p 0 0 = {(0, 0)} := by
    ext jl
    simp [localExactPairSet, Prod.ext_iff]
  rw [heq]
  simp

/-- A one-zero exact label pair has `p-1` compatible residue pairs. -/
theorem card_localExactPairSet_zero_nonzero {p B : ℕ} [NeZero p]
    (hB : B ≠ 0) :
    (localExactPairSet p 0 B).card = p - 1 := by
  classical
  let s := localExactPairSet p 0 B
  let u := nonzeroZModFinset p
  calc
    s.card = u.card := by
      apply Finset.card_bij (fun jl _ ↦ jl.2)
      · intro jl hjl
        have hrel : jl.1 = 0 ∧ jl.2 ≠ 0 := by
          simpa [s, localExactPairSet, hB] using
            (Finset.mem_filter.mp hjl).2
        simpa [u, nonzeroZModFinset] using hrel.2
      · intro x hx y hy hxy
        have hxrel : x.1 = 0 ∧ x.2 ≠ 0 := by
          simpa [s, localExactPairSet, hB] using
            (Finset.mem_filter.mp hx).2
        have hyrel : y.1 = 0 ∧ y.2 ≠ 0 := by
          simpa [s, localExactPairSet, hB] using
            (Finset.mem_filter.mp hy).2
        have hx0 : x.1 = 0 := hxrel.1
        have hy0 : y.1 = 0 := hyrel.1
        apply Prod.ext
        · rw [hx0, hy0]
        · exact hxy
      · intro l hl
        have hlne : l ≠ 0 := by
          simpa [u, nonzeroZModFinset] using hl
        refine ⟨(0, l), ?_, rfl⟩
        simp [s, localExactPairSet, hB, hlne]
    _ = p - 1 := card_nonzeroZModFinset p

/-- The symmetric one-zero exact label pair also has `p-1` choices. -/
theorem card_localExactPairSet_nonzero_zero {p A : ℕ} [NeZero p]
    (hA : A ≠ 0) :
    (localExactPairSet p A 0).card = p - 1 := by
  classical
  let s := localExactPairSet p A 0
  let u := nonzeroZModFinset p
  calc
    s.card = u.card := by
      apply Finset.card_bij (fun jl _ ↦ jl.1)
      · intro jl hjl
        have hrel : jl.1 ≠ 0 ∧ jl.2 = 0 := by
          simpa [s, localExactPairSet, hA] using
            (Finset.mem_filter.mp hjl).2
        simpa [u, nonzeroZModFinset] using hrel.1
      · intro x hx y hy hxy
        have hxrel : x.1 ≠ 0 ∧ x.2 = 0 := by
          simpa [s, localExactPairSet, hA] using
            (Finset.mem_filter.mp hx).2
        have hyrel : y.1 ≠ 0 ∧ y.2 = 0 := by
          simpa [s, localExactPairSet, hA] using
            (Finset.mem_filter.mp hy).2
        have hx0 : x.2 = 0 := hxrel.2
        have hy0 : y.2 = 0 := hyrel.2
        apply Prod.ext
        · exact hxy
        · rw [hx0, hy0]
      · intro j hj
        have hjne : j ≠ 0 := by
          simpa [u, nonzeroZModFinset] using hj
        refine ⟨(j, 0), ?_, rfl⟩
        simp [s, localExactPairSet, hA, hjne]
    _ = p - 1 := card_nonzeroZModFinset p

/-- Two nonzero exact labels give one compatible nonzero second coordinate
for each nonzero first coordinate. -/
theorem card_localExactPairSet_nonzero_nonzero {p A B : ℕ} [NeZero p]
    (hp : p.Prime) (hApos : 0 < A) (hAlt : A < p)
    (hBpos : 0 < B) (hBlt : B < p) :
    (localExactPairSet p A B).card = p - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let s := localExactPairSet p A B
  let u := nonzeroZModFinset p
  have hA : A ≠ 0 := Nat.ne_of_gt hApos
  have hB : B ≠ 0 := Nat.ne_of_gt hBpos
  have hAz : (A : ZMod p) ≠ 0 :=
    natCast_zmod_ne_zero_of_pos_of_lt hApos hAlt
  have hBz : (B : ZMod p) ≠ 0 :=
    natCast_zmod_ne_zero_of_pos_of_lt hBpos hBlt
  calc
    s.card = u.card := by
      apply Finset.card_bij (fun jl _ ↦ jl.1)
      · intro jl hjl
        have hrel : jl.1 ≠ 0 ∧ jl.2 ≠ 0 ∧
            (A : ZMod p) * jl.2 = (B : ZMod p) * jl.1 := by
          simpa [s, localExactPairSet, hA, hB] using
            (Finset.mem_filter.mp hjl).2
        simpa [u, nonzeroZModFinset] using hrel.1
      · intro x hx y hy hxy
        have hxfull : x.1 ≠ 0 ∧ x.2 ≠ 0 ∧
            (A : ZMod p) * x.2 = (B : ZMod p) * x.1 := by
          simpa [s, localExactPairSet, hA, hB] using
            (Finset.mem_filter.mp hx).2
        have hyfull : y.1 ≠ 0 ∧ y.2 ≠ 0 ∧
            (A : ZMod p) * y.2 = (B : ZMod p) * y.1 := by
          simpa [s, localExactPairSet, hA, hB] using
            (Finset.mem_filter.mp hy).2
        have hxrel := hxfull.2.2
        have hyrel := hyfull.2.2
        apply Prod.ext
        · exact hxy
        · apply mul_left_cancel₀ hAz
          rw [hxrel, hyrel, hxy]
      · intro j hj
        have hjne : j ≠ 0 := by
          simpa [u, nonzeroZModFinset] using hj
        let l : ZMod p := (A : ZMod p)⁻¹ * (B : ZMod p) * j
        have hlne : l ≠ 0 := by
          exact mul_ne_zero (mul_ne_zero (inv_ne_zero hAz) hBz) hjne
        refine ⟨(j, l), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [localExactPairSet, hA, hB, and_self, if_false]
        refine ⟨hjne, hlne, ?_⟩
        dsimp [l]
        field_simp
    _ = p - 1 := card_nonzeroZModFinset p

/-- Uniform exact-pair cardinality: one at a both-zero prime and `p-1`
otherwise. -/
theorem card_localExactPairSet {p K A B : ℕ} [NeZero p] (hp : p.Prime)
    (hA : A < K) (hB : B < K) (hKp : K < p) :
    (localExactPairSet p A B).card =
      if A = 0 ∧ B = 0 then 1 else p - 1 := by
  by_cases hAz : A = 0
  · subst A
    by_cases hBz : B = 0
    · subst B
      simp [card_localExactPairSet_zero_zero]
    · simp [hBz, card_localExactPairSet_zero_nonzero hBz]
  · by_cases hBz : B = 0
    · subst B
      simp [hAz, card_localExactPairSet_nonzero_zero hAz]
    · have hApos : 0 < A := Nat.pos_of_ne_zero hAz
      have hBpos : 0 < B := Nat.pos_of_ne_zero hBz
      have hAlt : A < p := hA.trans hKp
      have hBlt : B < p := hB.trans hKp
      simp [hAz, hBz, card_localExactPairSet_nonzero_nonzero hp
        hApos hAlt hBpos hBlt]

/-- Primes at which both members of a label pair vanish. -/
def bothZeroLabelPrimes (P : Finset ℕ) (a b : ℕ → ℕ) : Finset ℕ :=
  P.filter (fun p ↦ a p = 0 ∧ b p = 0)

/-- Product of the both-zero primes. -/
def pairBothZeroProduct (P : Finset ℕ) (a b : ℕ → ℕ) : ℕ :=
  primeProduct (bothZeroLabelPrimes P a b)

/-- Number of independent exact-label-compatible residue-pair choices. -/
def pairExactResidueCount (P : Finset ℕ) (a b : ℕ → ℕ) : ℕ :=
  ∏ p ∈ P, if a p = 0 ∧ b p = 0 then 1 else p - 1

/-- Number of unit multipliers compatible with any fixed exact residue pair:
there are `p-1` choices at both-zero primes and one elsewhere. -/
def pairMultiplierCount (P : Finset ℕ) (a b : ℕ → ℕ) : ℕ :=
  primeUnitCount (bothZeroLabelPrimes P a b)

/-- The exact-pair residue count is the unit-count product outside the
both-zero primes. -/
theorem pairExactResidueCount_eq_sdiffUnitCount
    (P : Finset ℕ) (a b : ℕ → ℕ) :
    pairExactResidueCount P a b =
      primeUnitCount (P \ bothZeroLabelPrimes P a b) := by
  classical
  let Z := bothZeroLabelPrimes P a b
  calc
    pairExactResidueCount P a b =
        ∏ p ∈ P, if a p = 0 ∧ b p = 0 then 1 else p - 1 := rfl
    _ = ∏ p ∈ P \ Z,
          if a p = 0 ∧ b p = 0 then 1 else p - 1 := by
      symm
      apply Finset.prod_subset Finset.sdiff_subset
      intro p hpP hpnot
      have hpZ : p ∈ Z := by
        simp only [Finset.mem_sdiff, not_and, not_not] at hpnot
        exact hpnot hpP
      have hz : a p = 0 ∧ b p = 0 :=
        (Finset.mem_filter.mp hpZ).2
      simp [hz]
    _ = primeUnitCount (P \ Z) := by
      unfold primeUnitCount
      apply Finset.prod_congr rfl
      intro p hp
      have hpnotZ : p ∉ Z := (Finset.mem_sdiff.mp hp).2
      have hz : ¬(a p = 0 ∧ b p = 0) := by
        intro hz
        exact hpnotZ (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1, hz⟩)
      simp [hz]

/-- Exact cancellation of the label-dependent residue and multiplier factors.
Every label pair contributes exactly the full local unit count per complete
`q×q` residue box. -/
theorem pairExactResidueCount_mul_multiplierCount
    (P : Finset ℕ) (a b : ℕ → ℕ) :
    pairExactResidueCount P a b * pairMultiplierCount P a b =
      primeUnitCount P := by
  classical
  rw [pairExactResidueCount_eq_sdiffUnitCount]
  unfold pairMultiplierCount primeUnitCount
  exact Finset.prod_sdiff (s₁ := bothZeroLabelPrimes P a b)
    (s₂ := P) (f := fun p : ℕ ↦ p - 1) (Finset.filter_subset _ _)

/-- Number of independent local residue-pair choices in the underlying
congruence lattice. -/
def pairLatticeResidueCount (P : Finset ℕ) (a b : ℕ → ℕ) : ℕ :=
  ∏ p ∈ P, if a p = 0 ∧ b p = 0 then 1 else p

/-- The local-choice count is the product of exactly the primes outside the
both-zero set. -/
theorem pairLatticeResidueCount_eq_sdiffProduct
    (P : Finset ℕ) (a b : ℕ → ℕ) :
    pairLatticeResidueCount P a b =
      primeProduct (P \ bothZeroLabelPrimes P a b) := by
  classical
  let Z := bothZeroLabelPrimes P a b
  calc
    pairLatticeResidueCount P a b =
        ∏ p ∈ P, if a p = 0 ∧ b p = 0 then 1 else p := rfl
    _ = ∏ p ∈ P \ Z, if a p = 0 ∧ b p = 0 then 1 else p := by
      symm
      apply Finset.prod_subset Finset.sdiff_subset
      intro p hpP hpnot
      have hpZ : p ∈ Z := by
        simp only [Finset.mem_sdiff, not_and, not_not] at hpnot
        exact hpnot hpP
      have hz : a p = 0 ∧ b p = 0 :=
        (Finset.mem_filter.mp hpZ).2
      simp [hz]
    _ = primeProduct (P \ Z) := by
      unfold primeProduct
      apply Finset.prod_congr rfl
      intro p hp
      have hpnotZ : p ∉ Z := (Finset.mem_sdiff.mp hp).2
      have hz : ¬(a p = 0 ∧ b p = 0) := by
        intro hz
        exact hpnotZ (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1, hz⟩)
      simp [hz]

/-- The prime product splits exactly into the both-zero factor and the local
residue-choice count. -/
theorem pairLatticeResidueCount_mul_bothZero
    (P : Finset ℕ) (a b : ℕ → ℕ) :
    pairLatticeResidueCount P a b * pairBothZeroProduct P a b =
      primeProduct P := by
  classical
  rw [pairLatticeResidueCount_eq_sdiffProduct]
  unfold pairBothZeroProduct
  exact Finset.prod_sdiff (s₁ := bothZeroLabelPrimes P a b)
    (s₂ := P) (f := fun p : ℕ ↦ p) (Finset.filter_subset _ _)

/-- Denominator-free determinant identity.  A complete residue square has
`q²` points, while the compatible local choices have cardinality `q/q₀`; the
corresponding lattice index is therefore `q q₀`. -/
theorem pairLattice_fundamental_cell_identity
    (P : Finset ℕ) (a b : ℕ → ℕ) :
    primeProduct P * primeProduct P =
      (primeProduct P * pairBothZeroProduct P a b) *
        pairLatticeResidueCount P a b := by
  have hsplit := pairLatticeResidueCount_mul_bothZero P a b
  calc
    primeProduct P * primeProduct P =
        primeProduct P *
          (pairLatticeResidueCount P a b * pairBothZeroProduct P a b) := by
      rw [hsplit]
    _ = (primeProduct P * pairBothZeroProduct P a b) *
          pairLatticeResidueCount P a b := by ac_rfl

/-- Quotient form of the exact index/determinant `q q₀`. -/
theorem pairLattice_index_eq (P : Finset ℕ) (a b : ℕ → ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    primeProduct P * primeProduct P /
        pairLatticeResidueCount P a b =
      primeProduct P * pairBothZeroProduct P a b := by
  have hcount : 0 < pairLatticeResidueCount P a b := by
    unfold pairLatticeResidueCount
    apply Finset.prod_pos
    intro p hp
    by_cases hz : a p = 0 ∧ b p = 0
    · simp [hz]
    · simp [hz, (hprime p hp).pos]
  rw [pairLattice_fundamental_cell_identity P a b]
  exact Nat.mul_div_cancel _ hcount

end Erdos394
