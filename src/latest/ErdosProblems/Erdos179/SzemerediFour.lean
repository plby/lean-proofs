/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos171

/-!
# The four-term case of Szemerédi's theorem

This file derives the qualitative four-term Szemerédi theorem used in the
Fox--Pohoata upper bound for Erdős Problem 179 from the completed density
Hales--Jewett theorem in `ErdosProblems.Erdos171`.

The proof uses the standard base-four encoding of words. Under this encoding
a combinatorial line is a genuine four-term arithmetic progression. For a
dense subset of a sufficiently long initial interval, discarding the last
incomplete base-four block and pigeonholing the remaining full blocks
produces a dense set of words to which density Hales--Jewett applies.
-/

open Finset Set

namespace Erdos179

/-- A finite set of natural numbers contains a nonconstant four-term
arithmetic progression. -/
def ContainsFourAP (T : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ T

/-- Qualitative finitary Szemerédi theorem for progressions of length four,
in the exact initial-interval form needed by the upper-bound argument. -/
def FiniteSzemerediFour : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ q ≥ N,
    ∀ T : Finset ℕ, T ⊆ range q → delta * q ≤ T.card → ContainsFourAP T

namespace SzemerediFour

/-- The completed density-Hales--Jewett theorem for the four-letter
alphabet. -/
theorem finiteDensityHJ_four : Erdos171.FiniteDensityHJ 4 :=
  Erdos171.finiteDensityHJ_all_of_alphabetDensityIncrement
    Erdos171.alphabetDensityIncrement 4 (by omega)

private noncomputable def encodeWord {iota : Type*} [Fintype iota] (L : ℕ)
    (x : iota → Fin L) : ℕ :=
  Nat.ofDigits L (List.ofFn (fun j : Fin (Fintype.card iota) ↦
    (x ((Fintype.equivFin iota).symm j) : ℕ)))

private theorem encodeWord_lt {iota : Type*} [Fintype iota] {L : ℕ}
    (hL : 1 < L) (x : iota → Fin L) :
    encodeWord L x < L ^ Fintype.card iota := by
  have h := Nat.ofDigits_lt_base_pow_length (b := L)
    (l := List.ofFn (fun j : Fin (Fintype.card iota) ↦
      (x ((Fintype.equivFin iota).symm j) : ℕ))) hL
  have hh := h (by
    intro d hd
    simp only [List.mem_ofFn] at hd
    rcases hd with ⟨j, rfl⟩
    exact (x ((Fintype.equivFin iota).symm j)).isLt)
  simpa [encodeWord] using hh

private theorem encodeWord_injective {iota : Type*} [Fintype iota]
    {L : ℕ} (hL : 1 < L) :
    Function.Injective (encodeWord (iota := iota) L) := by
  intro x y hxy
  let xs : List ℕ := List.ofFn (fun j : Fin (Fintype.card iota) ↦
    (x ((Fintype.equivFin iota).symm j) : ℕ))
  let ys : List ℕ := List.ofFn (fun j : Fin (Fintype.card iota) ↦
    (y ((Fintype.equivFin iota).symm j) : ℕ))
  have hxs : ∀ d ∈ xs, d < L := by
    intro d hd
    simp only [xs, List.mem_ofFn] at hd
    rcases hd with ⟨j, rfl⟩
    exact (x ((Fintype.equivFin iota).symm j)).isLt
  have hys : ∀ d ∈ ys, d < L := by
    intro d hd
    simp only [ys, List.mem_ofFn] at hd
    rcases hd with ⟨j, rfl⟩
    exact (y ((Fintype.equivFin iota).symm j)).isLt
  have hlists : xs = ys := by
    apply Nat.ofDigits_inj_of_len_eq hL (by simp [xs, ys]) hxs hys
    simpa [encodeWord, xs, ys] using hxy
  funext i
  let j : Fin (Fintype.card iota) := Fintype.equivFin iota i
  have hj := congrArg (fun z : List ℕ ↦ z.getD j 0) hlists
  have hval : (x i : ℕ) = (y i : ℕ) := by
    simpa [xs, ys, j] using hj
  exact Fin.ext hval

private noncomputable def encodedFin (m : ℕ) (x : Erdos171.Word 4 m) : Fin (4 ^ m) :=
  ⟨encodeWord 4 x, by simpa using encodeWord_lt (by omega : 1 < 4) x⟩

private theorem encodedFin_bijective (m : ℕ) :
    Function.Bijective (encodedFin m) := by
  apply (Fintype.bijective_iff_injective_and_card (encodedFin m)).2
  constructor
  · intro x y hxy
    apply encodeWord_injective (by omega : 1 < 4)
    exact congrArg Fin.val hxy
  · simp [Erdos171.card_word]

private noncomputable def lineOptions {alpha iota : Type*} [Fintype iota]
    (l : Combinatorics.Line alpha iota) : List (Option alpha) :=
  List.ofFn (fun j : Fin (Fintype.card iota) ↦
    l.idxFun ((Fintype.equivFin iota).symm j))

private def optionMask {alpha : Type*} : Option alpha → ℕ
  | none => 1
  | some _ => 0

private def optionBase {L : ℕ} : Option (Fin L) → ℕ
  | none => 0
  | some x => (x : ℕ)

private theorem ofDigits_option_line {L : ℕ} (r : Fin L)
    (opts : List (Option (Fin L))) :
    Nat.ofDigits L (opts.map (fun o : Option (Fin L) ↦ (o.getD r : ℕ))) =
      Nat.ofDigits L (opts.map optionBase) +
        (r : ℕ) * Nat.ofDigits L (opts.map optionMask) := by
  induction opts with
  | nil => simp
  | cons o opts ih =>
      cases o <;> simp [Nat.ofDigits_cons, optionMask, optionBase, ih] <;> ring

private theorem line_step_pos {iota : Type*} [Fintype iota] {L : ℕ}
    (hL : 1 < L) (l : Combinatorics.Line (Fin L) iota) :
    0 < Nat.ofDigits L ((lineOptions l).map optionMask) := by
  by_contra h
  have hz : Nat.ofDigits L ((lineOptions l).map optionMask) = 0 := by omega
  rcases l.proper with ⟨i, hi⟩
  have hmemOpt : (none : Option (Fin L)) ∈ lineOptions l := by
    unfold lineOptions
    simp only [List.mem_ofFn]
    refine ⟨(Fintype.equivFin iota) i, ?_⟩
    simp [hi]
  have hmemOne : 1 ∈ (lineOptions l).map optionMask := by
    exact List.mem_map.mpr ⟨none, hmemOpt, rfl⟩
  have hallzero := Nat.digits_zero_of_eq_zero (by omega : L ≠ 0) hz 1 hmemOne
  omega

private theorem encode_line_affine {iota : Type*} [Fintype iota] {L : ℕ}
    (hL : 1 < L) (l : Combinatorics.Line (Fin L) iota) (r : Fin L) :
    let zero : Fin L := ⟨0, by omega⟩
    encodeWord L (l r) =
      encodeWord L (l zero) + (r : ℕ) *
        Nat.ofDigits L ((lineOptions l).map optionMask) := by
  let zero : Fin L := ⟨0, by omega⟩
  change encodeWord L (l r) = encodeWord L (l zero) + _
  let opts : List (Option (Fin L)) :=
    List.ofFn (fun j : Fin (Fintype.card iota) ↦
      l.idxFun ((Fintype.equivFin iota).symm j))
  have hrList :
      List.ofFn (fun j : Fin (Fintype.card iota) ↦
        ((l r) ((Fintype.equivFin iota).symm j) : ℕ)) =
        opts.map (fun o : Option (Fin L) ↦ (o.getD r : ℕ)) := by
    rw [List.map_ofFn, List.ofFn_inj]
    funext j
    simp only [Function.comp_apply, Combinatorics.Line.coe_apply]
  have hzList :
      List.ofFn (fun j : Fin (Fintype.card iota) ↦
        ((l zero) ((Fintype.equivFin iota).symm j) : ℕ)) =
        opts.map optionBase := by
    rw [List.map_ofFn, List.ofFn_inj]
    funext j
    simp only [Function.comp_apply, Combinatorics.Line.coe_apply]
    cases l.idxFun ((Fintype.equivFin iota).symm j) <;>
      simp [optionBase, zero]
  unfold encodeWord lineOptions
  rw [hrList, hzList]
  exact ofDigits_option_line r opts

/-- Density Hales--Jewett for four letters, transported through base-four
encoding, gives the exact finite four-term Szemeredi statement required by
the additive-combinatorial reduction. -/
theorem finiteSzemerediFour : FiniteSzemerediFour := by
  intro delta hdelta
  by_cases hdelta_one : 1 < delta
  · refine ⟨1, ?_⟩
    intro q hq T hT hcard
    have hqpos : 0 < q := by omega
    have hTcardNat : T.card ≤ q := by simpa using Finset.card_le_card hT
    have hTcardReal : (T.card : ℝ) ≤ q := by exact_mod_cast hTcardNat
    have hqReal : (0 : ℝ) < q := by exact_mod_cast hqpos
    exfalso
    nlinarith
  · have hdelta_le_one : delta ≤ 1 := le_of_not_gt hdelta_one
    obtain ⟨m0, hm0⟩ :=
      finiteDensityHJ_four.eventual (by omega) (delta / 4) (by positivity)
    let m : ℕ := m0 + Nat.ceil (4 / delta) + 1
    let L : ℕ := 4 ^ m
    have hm0m : m0 ≤ m := by dsimp [m]; omega
    have hLpos : 0 < L := by simp [L]
    have hmL : m ≤ L := by
      have hpow := Nat.mul_le_pow (a := 4) (by omega) m
      dsimp [L]
      omega
    have hceil_m : Nat.ceil (4 / delta) ≤ m := by dsimp [m]; omega
    have hfour_div_L : 4 / delta ≤ (L : ℝ) := by
      calc
        4 / delta ≤ (Nat.ceil (4 / delta) : ℕ) := Nat.le_ceil _
        _ ≤ m := by exact_mod_cast hceil_m
        _ ≤ L := by exact_mod_cast hmL
    have hunit : (1 : ℝ) ≤ delta / 4 * L := by
      calc
        (1 : ℝ) = delta / 4 * (4 / delta) := by
          field_simp [ne_of_gt hdelta]
        _ ≤ delta / 4 * L := by gcongr
    let N : ℕ := Nat.ceil (2 * (L : ℝ) / delta) + 1
    refine ⟨N, ?_⟩
    intro q hq T hT hcard
    have hqbig : 2 * (L : ℝ) / delta < q := by
      calc
        2 * (L : ℝ) / delta < Nat.ceil (2 * (L : ℝ) / delta) + 1 :=
          lt_of_le_of_lt (Nat.le_ceil _) (by norm_num)
        _ = N := by simp [N]
        _ ≤ q := by exact_mod_cast hq
    have htwiceL : 2 * (L : ℝ) < delta * q := by
      have hmul := mul_lt_mul_of_pos_left hqbig hdelta
      have hid : delta * (2 * (L : ℝ) / delta) = 2 * L := by
        field_simp [ne_of_gt hdelta]
      rw [hid] at hmul
      exact hmul
    have hLhalf : (L : ℝ) ≤ delta / 2 * q := by nlinarith
    have hqLReal : 2 * (L : ℝ) < q := by
      calc
        2 * (L : ℝ) < delta * q := htwiceL
        _ ≤ 1 * q := by gcongr
        _ = q := one_mul _
    have hqLNat : 2 * L < q := by exact_mod_cast hqLReal
    let r : ℕ := q / L
    have hrpos : 0 < r := by
      dsimp [r]
      exact Nat.div_pos (by omega : L ≤ q) hLpos
    have hrLq : r * L ≤ q := by
      dsimp [r]
      exact Nat.div_mul_le_self q L
    have hrem : q - r * L < L := by
      have hmod := Nat.mod_lt q hLpos
      have hdivmod := Nat.div_add_mod q L
      have hdivmod' : q / L * L + q % L = q := by
        simpa [Nat.mul_comm] using hdivmod
      dsimp [r]
      omega
    let S : Finset ℕ := T ∩ range (r * L)
    let R : Finset ℕ := range q \ range (r * L)
    have hrange : range (r * L) ⊆ range q := range_mono hrLq
    have hRcard : R.card = q - r * L := by
      simp [R, Finset.card_sdiff, Finset.inter_eq_left.mpr hrange]
    have hTsub : T ⊆ S ∪ R := by
      intro x hx
      by_cases hxsmall : x < r * L
      · exact mem_union_left _ (mem_inter.mpr ⟨hx, mem_range.mpr hxsmall⟩)
      · apply Finset.mem_union_right
        rw [Finset.mem_sdiff]
        exact ⟨hT hx, by simpa using hxsmall⟩
    have hTupper : T.card ≤ S.card + (q - r * L) := by
      calc
        T.card ≤ (S ∪ R).card := card_le_card hTsub
        _ ≤ S.card + R.card := Finset.card_union_le S R
        _ = S.card + (q - r * L) := by rw [hRcard]
    have hTupperReal : (T.card : ℝ) ≤ S.card + (q - r * L) := by
      exact_mod_cast hTupper
    have hremReal : ((q - r * L : ℕ) : ℝ) ≤ L := by exact_mod_cast hrem.le
    have hremReal' : (q : ℝ) - r * L ≤ L := by
      rw [← Nat.cast_mul, ← Nat.cast_sub hrLq]
      exact hremReal
    have hSlarge : delta / 2 * q ≤ (S.card : ℝ) := by
      have hcardReal : delta * q ≤ (T.card : ℝ) := by simpa using hcard
      have hTupperReal' : (T.card : ℝ) ≤ S.card + L := by
        nlinarith [hTupperReal, hremReal']
      nlinarith
    have hSblocks : delta / 2 * (r * L : ℕ) ≤ (S.card : ℝ) := by
      calc
        delta / 2 * (r * L : ℕ) ≤ delta / 2 * q := by gcongr
        _ ≤ (S.card : ℝ) := hSlarge
    let n : ℕ := Nat.ceil (delta / 4 * L)
    have hnupper : (n : ℝ) ≤ delta / 2 * L := by
      have hceil := Nat.ceil_lt_add_one (show 0 ≤ delta / 4 * (L : ℝ) by positivity)
      dsimp [n]
      exact hceil.le.trans (by nlinarith [hunit])
    have hmulReal : (r * n : ℕ) ≤ (S.card : ℝ) := by
      calc
        ((r * n : ℕ) : ℝ) = (r : ℝ) * n := by push_cast; ring
        _ ≤ (r : ℝ) * (delta / 2 * L) := by gcongr
        _ = delta / 2 * (r * L : ℕ) := by push_cast; ring
        _ ≤ (S.card : ℝ) := hSblocks
    have hmul : r * n ≤ S.card := by exact_mod_cast hmulReal
    have hmap : ∀ x ∈ S, x / L ∈ range r := by
      intro x hx
      rw [Finset.mem_range]
      have hxlt : x < r * L := Finset.mem_range.mp (mem_inter.mp hx).2
      exact (Nat.div_lt_iff_lt_mul hLpos).2 (by simpa [Nat.mul_comm] using hxlt)
    obtain ⟨j, hj, hjcard⟩ :=
      exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := S) (t := range r) (f := fun x : ℕ ↦ x / L) (n := n)
        hmap ⟨0, Finset.mem_range.mpr hrpos⟩ (by simpa using hmul)
    have hjlt : j < r := Finset.mem_range.mp hj
    let W : Finset (Erdos171.Word 4 m) :=
      univ.filter (fun w ↦ j * L + (encodedFin m w).val ∈ T)
    have hWcard : W.card = #{x ∈ S | x / L = j} := by
      apply Finset.card_bij (fun w (_ : w ∈ W) ↦ j * L + (encodedFin m w).val)
      · intro w hw
        rw [mem_filter]
        have hwT : j * L + (encodedFin m w).val ∈ T := (mem_filter.mp hw).2
        have hwlt : j * L + (encodedFin m w).val < r * L := by
          calc
            j * L + (encodedFin m w).val < j * L + L :=
              Nat.add_lt_add_left (encodedFin m w).isLt _
            _ = (j + 1) * L := by ring
            _ ≤ r * L := Nat.mul_le_mul_right L (by omega)
        constructor
        · exact mem_inter.mpr ⟨hwT, mem_range.mpr hwlt⟩
        · rw [Nat.add_comm, Nat.mul_comm j L, Nat.add_mul_div_left _ _ hLpos,
            Nat.div_eq_of_lt (encodedFin m w).isLt]
          simp
      · intro w₁ hw₁ w₂ hw₂ heq
        apply (encodedFin_bijective m).1
        apply Fin.ext
        omega
      · intro x hx
        have hx' := mem_filter.mp hx
        have hxS := mem_inter.mp hx'.1
        let z : Fin L := ⟨x % L, Nat.mod_lt x hLpos⟩
        obtain ⟨w, hw⟩ := (encodedFin_bijective m).2 z
        refine ⟨w, ?_, ?_⟩
        · rw [mem_filter]
          constructor
          · exact mem_univ w
          · have hval : (encodedFin m w).val = x % L := congrArg Fin.val hw
            have hdivmod := Nat.div_add_mod x L
            have hrepr : j * L + x % L = x := by
              calc
                j * L + x % L = L * (x / L) + x % L := by rw [hx'.2]; ring
                _ = x := hdivmod
            rw [hval, hrepr]
            exact hxS.1
        · have hval : (encodedFin m w).val = x % L := congrArg Fin.val hw
          have hdivmod := Nat.div_add_mod x L
          rw [hval]
          calc
            j * L + x % L = L * (x / L) + x % L := by rw [hx'.2]; ring
            _ = x := hdivmod
    have hWlarge : delta / 4 * L ≤ (W.card : ℝ) := by
      have hnlow : delta / 4 * (L : ℝ) ≤ n := Nat.le_ceil _
      have hjcardReal : (n : ℝ) ≤ (#{x ∈ S | x / L = j} : ℕ) := by
        exact_mod_cast hjcard
      rw [hWcard]
      exact hnlow.trans hjcardReal
    have hWdensity : delta / 4 ≤ Erdos171.density W := by
      rw [Erdos171.density_eq_card_div_card, Erdos171.card_word]
      have hLReal : (0 : ℝ) < L := by exact_mod_cast hLpos
      apply (le_div_iff₀ hLReal).2
      simpa [L, Nat.cast_pow] using hWlarge
    obtain ⟨l, hl⟩ :=
      Erdos171.containsLine_coe_finset_iff.mp (hm0 m hm0m W hWdensity)
    let zero : Fin 4 := ⟨0, by omega⟩
    let b : ℕ := j * L + encodeWord 4 (l zero)
    let d : ℕ := Nat.ofDigits 4 ((lineOptions l).map optionMask)
    refine ⟨b, d, line_step_pos (by omega : 1 < 4) l, ?_⟩
    intro i hi
    let ri : Fin 4 := ⟨i, hi⟩
    have hri := hl ri
    have hriT : j * L + (encodedFin m (l ri)).val ∈ T := (mem_filter.mp hri).2
    dsimp [encodedFin] at hriT
    rw [encode_line_affine (by omega : 1 < 4) l ri] at hriT
    simpa [b, d, ri, zero, Nat.add_assoc] using hriT

end SzemerediFour

end Erdos179
