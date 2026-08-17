/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos54.FiniteSums
import ErdosProblems.Erdos54.Lev
import ErdosProblems.Erdos54.RoughNumbers
import ErdosProblems.Erdos54.CyclicGrowth
import ErdosProblems.Erdos54.Probability
import ErdosProblems.Erdos54.Asymptotics
import ErdosProblems.Erdos54.Assembly
import ErdosProblems.Erdos54.CyclicGrowthParameters

/-!
# The robust finite block for Erdős Problem 54

This file contains the integer-rounded, two-colour specialization of
Conlon--Fox--Pham's robust block lemma.  The sample length at scale `x` is
`ceil (6 log x)`.  A good block consists of `1280*q` distinct rough integers
in `[x,2*x)`, and every subblock of cardinality at least `640*q` covers the
closed interval `[160*q*x,560*q*x]` by distinct subset sums.

The proof is separated into two layers.  `UniversallyModularGood` is the
finite property supplied by the probabilistic modular-growth argument.  The
remaining lemmas in this file turn that property into the desired interval
by adjoining moduli, applying Lev's interval theorem to forty disjoint
pieces, and using Graham's extension lemma.
-/

open scoped BigOperators Pointwise

namespace Erdos54

/-- The integer-rounded length of one modular random sample. -/
noncomputable def blockSampleLength (x : ℕ) : ℕ :=
  Nat.ceil (6 * Real.log (x : ℝ))

/-- The exact robust-block conclusion used in the dyadic construction. -/
def IsRobustBlock (x q : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Ico x (2 * x) ∧
  S.card = 1280 * q ∧
  ∀ T : Finset ℕ, T ⊆ S → 640 * q ≤ T.card →
    CoversInterval T (160 * q * x) (560 * q * x)

/-- Every `q`-element part of a universally modular-good set has at least
`h` subset-sum residues modulo each unused element of the ambient set.

This is stronger than the particular forty tests needed below, but it is
the convenient deterministic output of the finite union bound. -/
def UniversallyModularGood (q h : ℕ) (S : Finset ℕ) : Prop :=
  ∀ P : Finset ℕ, P ⊆ S → P.card = q →
    ∀ m ∈ S \ P, h ≤ (subsetSumResidues m P).card

theorem UniversallyModularGood.mono_modulus_set {q h : ℕ} {S : Finset ℕ}
    (hgood : UniversallyModularGood q h S) {P : Finset ℕ}
    (hPS : P ⊆ S) (hPcard : P.card = q) {B : Finset ℕ} (hPB : P ⊆ B)
    {m : ℕ} (hmS : m ∈ S) (hmB : m ∉ B) :
    h ≤ (subsetSumResidues m B).card := by
  have hmP : m ∉ P := fun hm ↦ hmB (hPB hm)
  have hbase := hgood P hPS hPcard m (Finset.mem_sdiff.mpr ⟨hmS, hmP⟩)
  exact hbase.trans (Finset.card_le_card <| by
    intro r hr
    rcases mem_subsetSumResidues.mp hr with ⟨n, hn, rfl⟩
    exact mem_subsetSumResidues.mpr
      ⟨n, subsetSumValues_mono hPB hn, rfl⟩)

/-! ## Extracting the deterministic modular property from a good sample -/

abbrev CoordinateSubset (N q : ℕ) :=
  {J : Finset (Fin N) // J.card = q}

noncomputable def coordinateSubsetEmbedding {N q : ℕ}
    (J : CoordinateSubset N q) : Fin q ↪ Fin N :=
  (J.1.equivFinOfCardEq J.2).symm.toEmbedding.trans
    (Function.Embedding.subtype fun i : Fin N ↦ i ∈ J.1)

theorem image_coordinateSubsetEmbedding {N q : ℕ} (J : CoordinateSubset N q) :
    Finset.univ.image (coordinateSubsetEmbedding J) = J.1 := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨j, -, rfl⟩
    exact ((J.1.equivFinOfCardEq J.2).symm j).property
  · intro hi
    let z : ↑J.1 := ⟨i, hi⟩
    let j : Fin q := J.1.equivFinOfCardEq J.2 z
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    simp [coordinateSubsetEmbedding, j, z]

theorem card_coordinateSubset_le (N q : ℕ) :
    Fintype.card (CoordinateSubset N q) ≤ 2 ^ N := by
  calc
    Fintype.card (CoordinateSubset N q) ≤
        Fintype.card (Finset (Fin N)) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 2 ^ N := by simp

/-- The inverse-superpolynomial saving in the cyclic estimate eventually
absorbs both the choice of coordinates and the choice of a rough modulus.
This deliberately crude bound only uses `|roughNumbers x| ≤ x`,
`x ≤ 3^u`, and a very large lower bound on the rounded logarithmic scale. -/
theorem coordinate_modulus_factor_le_logScale_power
    {x q u : ℕ} (hq : q ≤ 6 * u) (hxpow : x ≤ 3 ^ u)
    (hlarge : 2 ^ 16008 ≤ u) :
    2 * Fintype.card
        (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) ≤
      u ^ (u / 2) := by
  have hu : 1 ≤ u := (by positivity : 0 < 2 ^ 16008).trans_le hlarge
  have hrough : (roughNumbers x).card ≤ x := by
    calc
      (roughNumbers x).card ≤ (Finset.Ico x (2 * x)).card :=
        Finset.card_le_card fun n hn ↦
          Finset.mem_Ico.mpr ⟨(mem_roughNumbers.mp hn).1,
            (mem_roughNumbers.mp hn).2.1⟩
      _ = x := by simp; omega
  have hxTwo : x ≤ 2 ^ (2 * u) := by
    calc
      x ≤ 3 ^ u := hxpow
      _ ≤ 4 ^ u := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (2 * u) := by rw [pow_mul]; norm_num
  have hcoord := card_coordinateSubset_le (1280 * q) q
  have hindex :
      Fintype.card (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) ≤
        2 ^ (8002 * u) := by
    rw [Fintype.card_prod, Fintype.card_coe]
    calc
      Fintype.card (CoordinateSubset (1280 * q) q) *
          (roughNumbers x).card ≤ 2 ^ (1280 * q) * x :=
        Nat.mul_le_mul hcoord hrough
      _ ≤ 2 ^ (8000 * u) * 2 ^ (2 * u) := by
        exact Nat.mul_le_mul
          (Nat.pow_le_pow_right (by omega) (by omega)) hxTwo
      _ = 2 ^ (8002 * u) := by
        rw [← pow_add]
        congr 1
        ring
  have htwoIndex :
      2 * Fintype.card
          (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) ≤
        2 ^ (8003 * u) := by
    calc
      2 * Fintype.card
          (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) ≤
          2 * 2 ^ (8002 * u) := Nat.mul_le_mul_left 2 hindex
      _ = 2 ^ (8002 * u + 1) := by
        rw [pow_add]
        simp [Nat.mul_comm]
      _ ≤ 2 ^ (8003 * u) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hexponent : 8003 * u ≤ 16008 * (u / 2) := by
    have hmod : u % 2 < 2 := Nat.mod_lt _ (by omega)
    have hdecomp := Nat.div_add_mod u 2
    omega
  calc
    2 * Fintype.card
        (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) ≤
        2 ^ (8003 * u) := htwoIndex
    _ ≤ 2 ^ (16008 * (u / 2)) :=
      Nat.pow_le_pow_right (by omega) hexponent
    _ = (2 ^ 16008) ^ (u / 2) := by rw [pow_mul]
    _ ≤ u ^ (u / 2) := Nat.pow_le_pow_left hlarge _

def sampleValueSet {x N : ℕ} (f : Fin N → ↑(roughNumbers x)) : Finset ℕ :=
  Finset.univ.image fun i ↦ (f i : ℕ)

def modularProjectionBad (x N q : ℕ)
    (i : CoordinateSubset N q × ↑(roughNumbers x))
    (f : Fin N → ↑(roughNumbers x)) : Prop :=
  FiniteProbability.projectTuple (coordinateSubsetEmbedding i.1) f ∈
    badCyclicTuples x (i.2 : ℕ) q

/-- Avoiding every short cyclic failure gives the universal modular
property required by the deterministic block argument. -/
theorem universallyModularGood_of_avoids
    {x N q : ℕ} {f : Fin N → ↑(roughNumbers x)}
    (hf : Function.Injective f)
    (havoid : ∀ i : CoordinateSubset N q × ↑(roughNumbers x),
      ¬ modularProjectionBad x N q i f) :
    UniversallyModularGood q (x / 4) (sampleValueSet f) := by
  classical
  let g : Fin N → ℕ := fun i ↦ (f i : ℕ)
  have hg : Function.Injective g := by
    intro i j hij
    apply hf
    exact Subtype.ext hij
  intro P hPS hPcard m hm
  let J₀ : Finset (Fin N) := Finset.univ.filter fun i ↦ g i ∈ P
  have hJimage : J₀.image g = P := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro haP
      have haS : a ∈ sampleValueSet f := hPS haP
      rcases Finset.mem_image.mp haS with ⟨i, -, hia⟩
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hia⟩
      simpa [g, hia] using haP
  have hJcard : J₀.card = q := by
    calc
      J₀.card = (J₀.image g).card :=
        (Finset.card_image_of_injective J₀ hg).symm
      _ = P.card := by rw [hJimage]
      _ = q := hPcard
  let J : CoordinateSubset N q := ⟨J₀, hJcard⟩
  have hmrough : m ∈ roughNumbers x := by
    have hmS := (Finset.mem_sdiff.mp hm).1
    rcases Finset.mem_image.mp hmS with ⟨i, -, him⟩
    simpa [sampleValueSet, him] using (f i).property
  let mt : ↑(roughNumbers x) := ⟨m, hmrough⟩
  let e := coordinateSubsetEmbedding J
  let short := FiniteProbability.projectTuple e f
  have heimage : Finset.univ.image e = J₀ := by
    dsimp only [e]
    simpa [J] using image_coordinateSubsetEmbedding J
  have hshortInj : Function.Injective (fun i ↦ (short i : ℕ)) := by
    intro i j hij
    have hsub : short i = short j := Subtype.ext hij
    have hef : e i = e j := hf hsub
    exact e.injective hef
  have hshortImage : Finset.univ.image (fun i ↦ (short i : ℕ)) = P := by
    rw [← hJimage]
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨i, -, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨e i, ?_, rfl⟩
      have hei : e i ∈ Finset.univ.image e :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [heimage] at hei
      exact hei
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨j, hj, rfl⟩
      have hj' : j ∈ Finset.univ.image e := by
        rw [heimage]
        exact hj
      rcases Finset.mem_image.mp hj' with ⟨i, -, hij⟩
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      subst j
      rfl
  have hnotbad : short ∉ badCyclicTuples x m q := by
    simpa [modularProjectionBad, J, mt, e, short] using havoid ⟨J, mt⟩
  have hlarge : x ≤
      4 * (cyclicSubsetSumResidues m (fun i ↦ (short i : ℕ))).card := by
    rw [← not_lt]
    simpa only [mem_badCyclicTuples, not_not] using hnotbad
  have hbridge := cyclicSubsetSumResidues_eq_subsetSumResidues_image
    (m := m) (fun i ↦ (short i : ℕ)) hshortInj
  rw [hshortImage] at hbridge
  rw [hbridge] at hlarge
  omega

/-- Finite union-bound packaging.  A uniform bound for the bad short tuples,
together with the displayed strict counting inequality, produces an
injective long sample with the deterministic modular property. -/
theorem exists_universallyModularGood_sample_of_bad_bound
    {x N q B : ℕ}
    (hbad : ∀ m ∈ roughNumbers x, (badCyclicTuples x m q).card ≤ B)
    (hsmall :
      Fintype.card (CoordinateSubset N q × ↑(roughNumbers x)) *
          (B * (roughNumbers x).card ^ (N - q)) +
        N * N * ((roughNumbers x).card ^ (N - 1)) <
          (roughNumbers x).card ^ N) :
    ∃ f : Fin N → ↑(roughNumbers x),
      Function.Injective f ∧
      UniversallyModularGood q (x / 4) (sampleValueSet f) := by
  classical
  let event := modularProjectionBad x N q
  have hevent : ∀ i : CoordinateSubset N q × ↑(roughNumbers x),
      (Finset.univ.filter (event i)).card ≤
        B * (roughNumbers x).card ^ (N - q) := by
    intro i
    have hpull := FiniteProbability.pullbackTuples_card_le
      (coordinateSubsetEmbedding i.1) (badCyclicTuples x (i.2 : ℕ) q)
    have hbadm := hbad (i.2 : ℕ) i.2.property
    calc
      (Finset.univ.filter (event i)).card ≤
          (badCyclicTuples x (i.2 : ℕ) q).card *
            (roughNumbers x).card ^ (N - q) := by
        simpa [event, modularProjectionBad, FiniteProbability.pullbackTuples]
          using hpull
      _ ≤ B * (roughNumbers x).card ^ (N - q) :=
        Nat.mul_le_mul_right _ hbadm
  obtain ⟨f, hf, havoid⟩ := FiniteProbability.exists_injective_avoiding_of_bounds
    N (B * (roughNumbers x).card ^ (N - q)) event hevent (by simpa using hsmall)
  exact ⟨f, hf, universallyModularGood_of_avoids hf havoid⟩

/-- A convenient division-free sufficient condition for the strict counting
inequality in the preceding selection theorem. -/
theorem sample_counting_inequality_of_two_budgets
    {x N q B : ℕ} (hqN : q ≤ N) (hN : 1 ≤ N)
    (hM : 0 < (roughNumbers x).card)
    (hevent :
      2 * Fintype.card (CoordinateSubset N q × ↑(roughNumbers x)) * B ≤
        (roughNumbers x).card ^ q)
    (hcollision : 2 * N * N < (roughNumbers x).card) :
    Fintype.card (CoordinateSubset N q × ↑(roughNumbers x)) *
          (B * (roughNumbers x).card ^ (N - q)) +
        N * N * ((roughNumbers x).card ^ (N - 1)) <
          (roughNumbers x).card ^ N := by
  let M := (roughNumbers x).card
  let I := Fintype.card (CoordinateSubset N q × ↑(roughNumbers x))
  have hpowSplit : M ^ q * M ^ (N - q) = M ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hqN]
  have hpowPred : M ^ N = M * M ^ (N - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [pow_add]
    simp
  have hhalfEvent :
      2 * (I * (B * M ^ (N - q))) ≤ M ^ N := by
    calc
      2 * (I * (B * M ^ (N - q))) =
          (2 * I * B) * M ^ (N - q) := by ring
      _ ≤ M ^ q * M ^ (N - q) :=
        Nat.mul_le_mul_right _ hevent
      _ = M ^ N := hpowSplit
  have hpowpos : 0 < M ^ (N - 1) := pow_pos hM _
  have hhalfCollision :
      2 * (N * N * M ^ (N - 1)) < M ^ N := by
    rw [hpowPred]
    have hmul := (Nat.mul_lt_mul_right hpowpos).mpr hcollision
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  dsimp only [I, M] at hhalfEvent hhalfCollision ⊢
  omega

/-- Repeatedly adjoining a disjoint set of moduli grows the number of
integer subset sums by at least `h` at every step. -/
theorem card_subsetSumValues_union_lower_of_modularGood
    {q h : ℕ} {S P R : Finset ℕ}
    (hgood : UniversallyModularGood q h S)
    (hPS : P ⊆ S) (hRS : R ⊆ S) (hPcard : P.card = q)
    (hdisj : Disjoint P R) (hpos : ∀ m ∈ R, 0 < m) :
    (subsetSumValues P).card + R.card * h ≤
      (subsetSumValues (P ∪ R)).card := by
  classical
  induction R using Finset.induction_on with
  | empty => simp
  | @insert m R hmR ih =>
      have hmS : m ∈ S := hRS (by simp)
      have hRS' : R ⊆ S := fun z hz ↦ hRS (by simp [hz])
      have hdisj' : Disjoint P R := hdisj.mono_right (Finset.subset_insert m R)
      have hmP : m ∉ P := by
        rw [Finset.disjoint_left] at hdisj
        exact fun hm ↦ hdisj hm (by simp)
      have hmPR : m ∉ P ∪ R := by simp [hmP, hmR]
      have hres : h ≤ (subsetSumResidues m (P ∪ R)).card :=
        hgood.mono_modulus_set hPS hPcard (Finset.subset_union_left) hmS hmPR
      have hgrow := adjoin_modulus_card_growth (hpos m (by simp)) hmPR hres
      have hrec := ih hRS' hdisj' (fun z hz ↦ hpos z (by simp [hz]))
      rw [Finset.union_insert, Finset.card_insert_of_notMem hmR]
      calc
        (subsetSumValues P).card + (R.card + 1) * h =
            ((subsetSumValues P).card + R.card * h) + h := by
              simp [Nat.add_mul, Nat.add_assoc]
        _ ≤ (subsetSumValues (P ∪ R)).card + h := Nat.add_le_add_right hrec h
        _ ≤ (subsetSumValues (insert m (P ∪ R))).card := hgrow

/-- The convenient consequence used for every `2*q`-element piece. -/
theorem card_subsetSumValues_pair_lower
    {q h : ℕ} {S P R : Finset ℕ}
    (hgood : UniversallyModularGood q h S)
    (hPS : P ⊆ S) (hRS : R ⊆ S)
    (hPcard : P.card = q) (hRcard : R.card = q)
    (hdisj : Disjoint P R) (hpos : ∀ m ∈ R, 0 < m) :
    q * h ≤ (subsetSumValues (P ∪ R)).card := by
  have h := card_subsetSumValues_union_lower_of_modularGood
    hgood hPS hRS hPcard hdisj hpos
  rw [hRcard] at h
  omega

/-- Subset sums of a set of `k` integers below `2*x` lie in `[0,2*x*k]`. -/
theorem subsetSumValues_subset_Icc_of_lt
    {x k : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Ico x (2 * x))
    (hcard : B.card = k) :
    subsetSumValues B ⊆ Finset.Icc 0 (2 * x * k) := by
  intro n hn
  rcases mem_subsetSumValues.mp hn with ⟨U, hUB, rfl⟩
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.zero_le _, ?_⟩
  calc
    ∑ a ∈ U, a ≤ ∑ _a ∈ U, 2 * x := by
      gcongr with a ha
      exact (Finset.mem_Ico.mp (hB (hUB ha))).2.le
    _ = 2 * x * U.card := by simp [Nat.mul_comm]
    _ ≤ 2 * x * k := Nat.mul_le_mul_left _ (by
      rw [← hcard]
      exact Finset.card_le_card hUB)

/-- If every member of a finite set in `[0,Q]` is divisible by `d`, there
are at most `Q/d+1` members. -/
theorem card_le_div_add_one_of_all_dvd {A : Finset ℕ} {Q d : ℕ}
    (hAQ : A ⊆ Finset.Icc 0 Q) (hdvd : ∀ a ∈ A, d ∣ a) :
    A.card ≤ Q / d + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / d
  have hinj : Set.InjOn f (A : Set ℕ) := by
    intro a ha b hb hab
    change a / d = b / d at hab
    calc
      a = a / d * d := (Nat.div_mul_cancel (hdvd a ha)).symm
      _ = b / d * d := by rw [hab]
      _ = b := Nat.div_mul_cancel (hdvd b hb)
  have himage : A.image f ⊆ Finset.range (Q / d + 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    apply Finset.mem_range.mpr
    have haQ := (Finset.mem_Icc.mp (hAQ ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haQ)
  calc
    A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (Q / d + 1)).card := Finset.card_le_card himage
    _ = Q / d + 1 := by simp

/-- A dense subset-sum set made from sufficiently rough integers cannot lie
in a nontrivial residue class.  The constant `18` is the rounded form of the
spacing estimate in CFP's application of Lev's theorem. -/
theorem subsetSumValues_isPrimitive_of_rough
    {x w n Q : ℕ} {B : Finset ℕ}
    (hBrough : B ⊆ roughNumbersAt x w) (hBne : B.Nonempty)
    (hcard : n ≤ (subsetSumValues B).card)
    (hspan : subsetSumValues B ⊆ Finset.Icc 0 Q)
    (hw : 17 ≤ w) (hratio : Q < 18 * (n - 1)) :
    IsPrimitive (subsetSumValues B) := by
  intro d hd hres
  obtain ⟨r, hr⟩ := hres
  have hrzero : r = 0 := by
    have := hr 0 (zero_mem_subsetSumValues B)
    simpa using this.symm
  have halldvd : ∀ a ∈ subsetSumValues B, d ∣ a := by
    intro a ha
    apply (ZMod.natCast_eq_zero_iff a d).mp
    simpa [hrzero] using hr a ha
  have hspaced := card_le_div_add_one_of_all_dvd hspan halldvd
  have hdle : d ≤ 17 := by
    by_contra hnot
    have hd18 : 18 ≤ d := by omega
    have hmul : d * ((subsetSumValues B).card - 1) ≤ Q := by
      have hsub : (subsetSumValues B).card - 1 ≤ Q / d := by omega
      have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hsub
      simpa [Nat.mul_comm] using this
    have hnsub : n - 1 ≤ (subsetSumValues B).card - 1 := Nat.sub_le_sub_right hcard 1
    have h18d : 18 * (n - 1) ≤ d * (n - 1) :=
      Nat.mul_le_mul_right (n - 1) hd18
    have hdn : d * (n - 1) ≤ d * ((subsetSumValues B).card - 1) :=
      Nat.mul_le_mul_left d hnsub
    have : 18 * (n - 1) ≤ Q := by
      calc
        18 * (n - 1) ≤ d * (n - 1) := h18d
        _ ≤ d * ((subsetSumValues B).card - 1) := hdn
        _ ≤ Q := hmul
    omega
  obtain ⟨b, hbB⟩ := hBne
  have hbrough := mem_roughNumbersAt.mp (hBrough hbB)
  let p := d.minFac
  have hpprime : p.Prime := Nat.minFac_prime hd.ne'
  have hpd : p ∣ d := Nat.minFac_dvd d
  have hpw : p ≤ w := by
    exact (Nat.minFac_le (by omega : 0 < d)).trans (hdle.trans hw)
  have hdb : d ∣ b := by
    apply halldvd b
    exact mem_subsetSumValues.mpr ⟨{b}, by simpa, by simp⟩
  exact hbrough.2.2 p hpw hpprime (hpd.trans hdb)

/-! ## Equal finite partitions -/

/-- A finite set of cardinality `pieces * q` can be partitioned into a list
of `pieces` pairwise-disjoint `q`-element sets.  The list formulation is
chosen because it feeds directly into `listSum`. -/
theorem exists_equipartition (U : Finset ℕ) (pieces q : ℕ)
    (hcard : U.card = pieces * q) :
    ∃ l : List (Finset ℕ),
      l.length = pieces ∧
      l.Pairwise Disjoint ∧
      (∀ B ∈ l, B.card = q) ∧
      l.toFinset.biUnion id = U := by
  classical
  induction pieces generalizing U with
  | zero =>
      have hU : U = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
      subst U
      exact ⟨[], by simp⟩
  | succ pieces ih =>
      have hqU : q ≤ U.card := by
        rw [hcard, Nat.succ_mul]
        omega
      obtain ⟨B, hBU, hBcard⟩ := Finset.exists_subset_card_eq hqU
      let R := U \ B
      have hRcard : R.card = pieces * q := by
        dsimp only [R]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBU, hcard, hBcard,
          Nat.succ_mul]
        omega
      obtain ⟨l, hlen, hpair, hlcard, hlunion⟩ := ih R hRcard
      refine ⟨B :: l, by simp [hlen], ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpair⟩
        intro C hCl
        rw [Finset.disjoint_left]
        intro a haB haC
        have haR : a ∈ R := by
          rw [← hlunion]
          simp only [Finset.mem_biUnion, List.mem_toFinset]
          exact ⟨C, hCl, haC⟩
        exact (Finset.mem_sdiff.mp haR).2 haB
      · intro C hC
        simp only [List.mem_cons] at hC
        rcases hC with rfl | hCl
        · exact hBcard
        · exact hlcard C hCl
      · ext a
        simp only [List.toFinset_cons, Finset.mem_biUnion, Finset.mem_insert,
          List.mem_toFinset, id_eq]
        constructor
        · rintro ⟨C, rfl | hCl, haC⟩
          · exact hBU haC
          · have : a ∈ R := by
              rw [← hlunion]
              simp only [Finset.mem_biUnion, List.mem_toFinset]
              exact ⟨C, hCl, haC⟩
            exact (Finset.mem_sdiff.mp this).1
        · intro haU
          by_cases haB : a ∈ B
          · exact ⟨B, Or.inl rfl, haB⟩
          · have haR : a ∈ R := Finset.mem_sdiff.mpr ⟨haU, haB⟩
            rw [← hlunion] at haR
            simp only [Finset.mem_biUnion, List.mem_toFinset] at haR
            obtain ⟨C, hCl, haC⟩ := haR
            exact ⟨C, Or.inr hCl, haC⟩

/-! ## Canonical halves of one piece -/

/-- A classically chosen subset of cardinality `min q B.card`. -/
noncomputable def chosenPart (q : ℕ) (B : Finset ℕ) : Finset ℕ :=
  Classical.choose (Finset.exists_subset_card_eq (Nat.min_le_right q B.card))

theorem chosenPart_subset (q : ℕ) (B : Finset ℕ) : chosenPart q B ⊆ B :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_right q B.card))).1

theorem card_chosenPart (q : ℕ) (B : Finset ℕ) :
    (chosenPart q B).card = min q B.card :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_right q B.card))).2

noncomputable def remainingPart (q : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B \ chosenPart q B

theorem remainingPart_subset (q : ℕ) (B : Finset ℕ) :
    remainingPart q B ⊆ B := Finset.sdiff_subset

theorem disjoint_chosenPart_remainingPart (q : ℕ) (B : Finset ℕ) :
    Disjoint (chosenPart q B) (remainingPart q B) := by
  exact Finset.disjoint_sdiff

theorem chosenPart_union_remainingPart (q : ℕ) (B : Finset ℕ) :
    chosenPart q B ∪ remainingPart q B = B := by
  rw [remainingPart, Finset.union_sdiff_of_subset (chosenPart_subset q B)]

theorem card_chosenPart_of_le (q : ℕ) (B : Finset ℕ) (hq : q ≤ B.card) :
    (chosenPart q B).card = q := by
  rw [card_chosenPart, min_eq_left hq]

theorem card_remainingPart_of_two_mul (q : ℕ) (B : Finset ℕ)
    (hcard : B.card = 2 * q) : (remainingPart q B).card = q := by
  rw [remainingPart, Finset.card_sdiff, Finset.inter_eq_left.mpr (chosenPart_subset q B),
    card_chosenPart_of_le q B (by omega), hcard]
  omega

/-- Every part of the equal partition is contained in the original set. -/
theorem mem_equipartition_subset {U : Finset ℕ} {l : List (Finset ℕ)}
    (hunion : l.toFinset.biUnion id = U) {B : Finset ℕ} (hBl : B ∈ l) :
    B ⊆ U := by
  intro a ha
  rw [← hunion]
  exact Finset.mem_biUnion.mpr ⟨B, by simpa, ha⟩

/-! ## Numerical estimates for the forty-piece argument -/

/-- All floor-sensitive inequalities needed by Lev and Graham are valid
with ample room once `x ≥ 200` and `q ≥ 1`. -/
theorem robustBlock_numeric {x q : ℕ} (hx : 200 ≤ x) (hq : 1 ≤ q) :
    let n := q * (x / 4)
    let Q := 4 * q * x
    3 ≤ n ∧
      Q - 1 ≤ 17 * (n - 2) ∧
      Q < 18 * (n - 1) ∧
      2 * x ≤ 40 * (n - 1) + 1 := by
  dsimp only
  let h := x / 4
  change 3 ≤ q * h ∧
    4 * q * x - 1 ≤ 17 * (q * h - 2) ∧
    4 * q * x < 18 * (q * h - 1) ∧
    2 * x ≤ 40 * (q * h - 1) + 1
  have hh : 50 ≤ h := by
    dsimp only [h]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by omega)
  have hxupper : x ≤ 4 * h + 3 := by
    dsimp only [h]
    omega
  have hqh : 50 * q ≤ q * h := by nlinarith
  have hQupper : 4 * q * x ≤ 16 * (q * h) + 12 * q := by nlinarith
  have hn3 : 3 ≤ q * h := by nlinarith
  have hhqh : h ≤ q * h := by
    calc
      h = 1 * h := by simp
      _ ≤ q * h := Nat.mul_le_mul_right h hq
  refine ⟨hn3, ?_, ?_, ?_⟩
  · have hmargin : 12 * q + 34 ≤ q * h := by nlinarith
    omega
  · have hmargin : 12 * q + 18 < 2 * (q * h) := by nlinarith
    omega
  · omega

/-- The additive data supplied by one `2*q`-element piece of a universally
modular-good rough block. -/
theorem modularGood_piece_data
    {x w q : ℕ} {S B : Finset ℕ}
    (hx : 200 ≤ x) (hq : 1 ≤ q) (hw : 17 ≤ w)
    (hSrough : S ⊆ roughNumbersAt x w)
    (hgood : UniversallyModularGood q (x / 4) S)
    (hBS : B ⊆ S) (hBcard : B.card = 2 * q) :
    let n := q * (x / 4)
    let Q := 4 * q * x
    n ≤ (subsetSumValues B).card ∧
      subsetSumValues B ⊆ Finset.Icc 0 Q ∧
      IsPrimitive (subsetSumValues B) := by
  dsimp only
  let P := chosenPart q B
  let R := remainingPart q B
  have hPsubB : P ⊆ B := chosenPart_subset q B
  have hRsubB : R ⊆ B := remainingPart_subset q B
  have hPsubS : P ⊆ S := hPsubB.trans hBS
  have hRsubS : R ⊆ S := hRsubB.trans hBS
  have hPcard : P.card = q := card_chosenPart_of_le q B (by omega)
  have hRcard : R.card = q := card_remainingPart_of_two_mul q B hBcard
  have hdisj : Disjoint P R := disjoint_chosenPart_remainingPart q B
  have hxpos : 0 < x := by omega
  have hRpos : ∀ m ∈ R, 0 < m := by
    intro m hm
    have hmrough := mem_roughNumbersAt.mp (hSrough (hRsubS hm))
    omega
  have hpair := card_subsetSumValues_pair_lower hgood hPsubS hRsubS
    hPcard hRcard hdisj hRpos
  have hBeq : P ∪ R = B := chosenPart_union_remainingPart q B
  rw [hBeq] at hpair
  have hBico : B ⊆ Finset.Ico x (2 * x) := by
    intro b hb
    have hbr := mem_roughNumbersAt.mp (hSrough (hBS hb))
    exact Finset.mem_Ico.mpr ⟨hbr.1, hbr.2.1⟩
  have hspan0 := subsetSumValues_subset_Icc_of_lt hBico hBcard
  have hspan : subsetSumValues B ⊆ Finset.Icc 0 (4 * q * x) := by
    have heq : 2 * x * (2 * q) = 4 * q * x := by ring
    simpa only [heq] using hspan0
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  have hnumeric := robustBlock_numeric hx hq
  have hprim := subsetSumValues_isPrimitive_of_rough
    (hBrough := hBS.trans hSrough) hBne hpair hspan hw hnumeric.2.2.1
  exact ⟨hpair, hspan, hprim⟩

/-! ## Graham extension from the forty-piece core -/

theorem card_mul_le_sum_of_Ico_subset {x y : ℕ} {R : Finset ℕ}
    (hR : R ⊆ Finset.Ico x y) : x * R.card ≤ ∑ r ∈ R, r := by
  calc
    x * R.card = ∑ _r ∈ R, x := by simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ R, r := by
      apply Finset.sum_le_sum
      intro r hr
      exact (Finset.mem_Ico.mp (hR hr)).1

/-- Once the first `80*q` elements supply an interval of length at least
`2*x`, adjoining the remaining `560*q` elements reaches the robust target
interval. -/
theorem covers_robust_interval_of_core
    {x q n L : ℕ} {U T : Finset ℕ}
    (hUT : U ⊆ T) (hUcard : U.card = 80 * q) (hTcard : T.card = 640 * q)
    (hTico : T ⊆ Finset.Ico x (2 * x))
    (hlength : 2 * x ≤ 40 * (n - 1) + 1)
    (hcore : CoversInterval U L (L + 40 * (n - 1)))
    (hcoreUpper : L + 40 * (n - 1) ≤ 160 * q * x) :
    CoversInterval T (160 * q * x) (560 * q * x) := by
  classical
  let R := T \ U
  have hRico : R ⊆ Finset.Ico x (2 * x) :=
    Finset.sdiff_subset.trans hTico
  have hRcard : R.card = 560 * q := by
    dsimp only [R]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUT, hTcard, hUcard]
    omega
  have hnodup : R.toList.Nodup := R.nodup_toList
  have hdisj : Disjoint R.toList.toFinset U := by
    simpa [R] using (Finset.disjoint_sdiff : Disjoint U (T \ U)).symm
  have hsmall : ∀ (i : ℕ) (hi : i < R.toList.length),
      R.toList[i] ≤
        (L + 40 * (n - 1)) - L + 1 + (R.toList.take i).sum := by
    intro i hi
    have hmem : R.toList[i] ∈ R := by
      have := List.getElem_mem (l := R.toList) hi
      exact Finset.mem_toList.mp this
    have hlt : R.toList[i] < 2 * x := (Finset.mem_Ico.mp (hRico hmem)).2
    have hbase : 2 * x ≤ (L + 40 * (n - 1)) - L + 1 := by omega
    omega
  have hext := coversInterval_add_list (s := U) (L := L)
    (U := L + 40 * (n - 1)) R.toList (by omega) hnodup hdisj hsmall hcore
  have hRunion : U ∪ R.toList.toFinset = T := by
    simp only [Finset.toList_toFinset, R]
    exact Finset.union_sdiff_of_subset hUT
  rw [hRunion] at hext
  have hRsum : 560 * q * x ≤ R.toList.sum := by
    have hsum := card_mul_le_sum_of_Ico_subset hRico
    rw [hRcard] at hsum
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum
  intro z hz
  apply hext
  apply Finset.mem_Icc.mpr
  have hz' := Finset.mem_Icc.mp hz
  constructor
  · exact (Nat.le_add_right L (40 * (n - 1))).trans (hcoreUpper.trans hz'.1)
  · calc
      z ≤ 560 * q * x := hz'.2
      _ ≤ R.toList.sum := hRsum
      _ ≤ L + 40 * (n - 1) + R.toList.sum := Nat.le_add_left _ _

/-- The subset-sum operation respects a disjoint finite union in the
direction needed to combine the forty Lev pieces. -/
theorem listSum_subset_subsetSumValues_biUnion
    {l : List (Finset ℕ)} (hdisj : l.Pairwise Disjoint) :
    listSum (l.map subsetSumValues) ⊆
      subsetSumValues (l.toFinset.biUnion id) := by
  induction l with
  | nil => simp [subsetSumValues]
  | cons B l ih =>
      have hhead : ∀ C ∈ l, Disjoint B C := (List.pairwise_cons.mp hdisj).1
      have hBdisj : Disjoint B (l.toFinset.biUnion id) := by
        rw [Finset.disjoint_left]
        intro a haB haU
        simp only [Finset.mem_biUnion, List.mem_toFinset] at haU
        obtain ⟨C, hCl, haC⟩ := haU
        exact (Finset.disjoint_left.mp (hhead C hCl)) haB haC
      intro z hz
      rw [List.map_cons, listSum_cons] at hz
      rcases Finset.mem_add.mp hz with ⟨u, hu, v, hv, rfl⟩
      have hv' := ih hdisj.tail hv
      have hadd := add_mem_subsetSumValues_union hBdisj hu hv'
      simpa using hadd

/-! ## Deterministic robust-block implication -/

/-- The exact forty-summand specialization of Lev's theorem needed here. -/
def FortySetIntervalPrinciple : Prop :=
  ∀ (As : List (Finset ℕ)) (n Q : ℕ),
    As.length = 40 →
    3 ≤ n →
    (∀ A ∈ As, n ≤ A.card) →
    (∀ A ∈ As, A ⊆ Finset.Icc 0 Q) →
    (∀ A ∈ As, 0 ∈ A) →
    (∀ A ∈ As, IsPrimitive A) →
    Q - 1 ≤ 17 * (n - 2) →
    ∃ L : ℕ, Finset.Icc L (L + 40 * (n - 1)) ⊆ listSum As

/-- The deterministic part of CFP Lemma 2.8.  The sole theorem-valued input
is the finite Lev principle stated immediately above. -/
theorem isRobustBlock_of_modularGood
    (hlev : FortySetIntervalPrinciple)
    {x w q : ℕ} {S : Finset ℕ}
    (hx : 200 ≤ x) (hq : 1 ≤ q) (hw : 17 ≤ w)
    (hSrough : S ⊆ roughNumbersAt x w)
    (hScard : S.card = 1280 * q)
    (hgood : UniversallyModularGood q (x / 4) S) :
    IsRobustBlock x q S := by
  classical
  have hSIco : S ⊆ Finset.Ico x (2 * x) := by
    intro s hs
    have hsr := mem_roughNumbersAt.mp (hSrough hs)
    exact Finset.mem_Ico.mpr ⟨hsr.1, hsr.2.1⟩
  refine ⟨hSIco, hScard, ?_⟩
  intro T hTS hTcardLower
  obtain ⟨T₀, hT₀T, hT₀card⟩ := Finset.exists_subset_card_eq hTcardLower
  have h80 : 80 * q ≤ T₀.card := by rw [hT₀card]; nlinarith
  obtain ⟨U, hUT₀, hUcard⟩ := Finset.exists_subset_card_eq h80
  have hpartitionCard : U.card = 40 * (2 * q) := by rw [hUcard]; ring
  obtain ⟨l, hllen, hlpair, hlcard, hlunion⟩ :=
    exists_equipartition U 40 (2 * q) hpartitionCard
  let n := q * (x / 4)
  let Q := 4 * q * x
  let As := l.map subsetSumValues
  have hnumeric := robustBlock_numeric hx hq
  have hAslen : As.length = 40 := by simp [As, hllen]
  have hpieceS : ∀ B ∈ l, B ⊆ S := by
    intro B hBl
    exact (mem_equipartition_subset hlunion hBl).trans
      (hUT₀.trans (hT₀T.trans hTS))
  have hAscard : ∀ A ∈ As, n ≤ A.card := by
    intro A hA
    rcases List.mem_map.mp hA with ⟨B, hBl, rfl⟩
    exact (modularGood_piece_data hx hq hw hSrough hgood
      (hpieceS B hBl) (hlcard B hBl)).1
  have hAsbound : ∀ A ∈ As, A ⊆ Finset.Icc 0 Q := by
    intro A hA
    rcases List.mem_map.mp hA with ⟨B, hBl, rfl⟩
    exact (modularGood_piece_data hx hq hw hSrough hgood
      (hpieceS B hBl) (hlcard B hBl)).2.1
  have hAszero : ∀ A ∈ As, 0 ∈ A := by
    intro A hA
    rcases List.mem_map.mp hA with ⟨B, -, rfl⟩
    exact zero_mem_subsetSumValues B
  have hAsprimitive : ∀ A ∈ As, IsPrimitive A := by
    intro A hA
    rcases List.mem_map.mp hA with ⟨B, hBl, rfl⟩
    exact (modularGood_piece_data hx hq hw hSrough hgood
      (hpieceS B hBl) (hlcard B hBl)).2.2
  obtain ⟨L, hL⟩ := hlev As n Q hAslen hnumeric.1 hAscard hAsbound
    hAszero hAsprimitive hnumeric.2.1
  have hsumsub : listSum As ⊆ subsetSumValues U := by
    have h := listSum_subset_subsetSumValues_biUnion hlpair
    rw [hlunion] at h
    exact h
  have hcore : CoversInterval U L (L + 40 * (n - 1)) :=
    fun z hz ↦ hsumsub (hL hz)
  have hUico : U ⊆ Finset.Ico x (2 * x) :=
    hUT₀.trans (hT₀T.trans (hTS.trans hSIco))
  have hUspan := subsetSumValues_subset_Icc_of_lt hUico hUcard
  have hcoreUpper : L + 40 * (n - 1) ≤ 160 * q * x := by
    have hend : L + 40 * (n - 1) ∈ subsetSumValues U := by
      apply hcore
      exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    have hendBound := (Finset.mem_Icc.mp (hUspan hend)).2
    calc
      L + 40 * (n - 1) ≤ 2 * x * (80 * q) := hendBound
      _ = 160 * q * x := by ring
  have hT₀ico : T₀ ⊆ Finset.Ico x (2 * x) :=
    hT₀T.trans (hTS.trans hSIco)
  have hT₀cover := covers_robust_interval_of_core hUT₀ hUcard hT₀card
    hT₀ico hnumeric.2.2.2 hcore hcoreUpper
  exact hT₀cover.mono hT₀T

/-- Complete finite robust-block packaging from the Lev principle and a
uniform cyclic bad-tuple count. -/
theorem exists_robustBlock_of_bad_bound
    (hlev : FortySetIntervalPrinciple)
    {x q B : ℕ}
    (hx : 200 ≤ x) (hq : 1 ≤ q) (hw : 17 ≤ roughCutoff x)
    (hbad : ∀ m ∈ roughNumbers x, (badCyclicTuples x m q).card ≤ B)
    (hsmall :
      Fintype.card (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) *
          (B * (roughNumbers x).card ^ ((1280 * q) - q)) +
        (1280 * q) * (1280 * q) *
            ((roughNumbers x).card ^ ((1280 * q) - 1)) <
          (roughNumbers x).card ^ (1280 * q)) :
    ∃ S : Finset ℕ, IsRobustBlock x q S := by
  classical
  obtain ⟨f, hf, hgood⟩ :=
    exists_universallyModularGood_sample_of_bad_bound hbad hsmall
  let S := sampleValueSet f
  have hfNat : Function.Injective (fun i ↦ (f i : ℕ)) := by
    intro i j hij
    exact hf (Subtype.ext hij)
  have hScard : S.card = 1280 * q := by
    calc
      S.card = (Finset.univ : Finset (Fin (1280 * q))).card := by
        exact Finset.card_image_of_injective _ hfNat
      _ = 1280 * q := by simp
  have hSrough : S ⊆ roughNumbersAt x (roughCutoff x) := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨i, -, rfl⟩
    exact (f i).property
  refine ⟨S, isRobustBlock_of_modularGood hlev hx hq hw hSrough hScard ?_⟩
  simpa [S] using hgood

/-- The rough cutoff tends to infinity. -/
theorem tendsto_roughCutoff :
    Filter.Tendsto roughCutoff Filter.atTop Filter.atTop := by
  apply tendsto_nat_floor_atTop.comp
  exact (Real.tendsto_log_atTop.atTop_div_const (by norm_num)).comp
    tendsto_natCast_atTop_atTop

/-- One sufficiently large instance of the rounded cyclic parameter bundle
produces the exact robust finite block. -/
theorem exists_robustBlock_of_parameterBounds
    (hlev : FortySetIntervalPrinciple) {x : ℕ}
    (hp : CyclicGrowthParameterBounds x)
    (hx : 200 ≤ x) (hcut : 17 ≤ roughCutoff x)
    (hlarge : 2 ^ 16008 ≤ cyclicLogScale x)
    (hcollision :
      2 * (1280 * cyclicTupleLength x) *
          (1280 * cyclicTupleLength x) < (roughNumbers x).card) :
    ∃ S : Finset ℕ, IsRobustBlock x (cyclicTupleLength x) S := by
  let q := cyclicTupleLength x
  let u := cyclicLogScale x
  let M := (roughNumbers x).card
  let scale := u ^ (u / 2)
  let B := M ^ q / scale
  have hM : 0 < M := by
    dsimp [M]
    by_contra hzero
    have : (roughNumbers x).card = 0 := Nat.eq_zero_of_not_pos hzero
    have hrough := hp.rough_card_lower
    rw [this, Nat.mul_zero] at hrough
    omega
  have hscale : 0 < scale := by
    exact pow_pos hp.logScale_pos _
  have hfactor :
      2 * Fintype.card
          (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) ≤ scale := by
    exact coordinate_modulus_factor_le_logScale_power
      hp.tupleLength_le_six_scale hp.scale_le_three_pow hlarge
  have hscaledBad : ∀ m ∈ roughNumbers x,
      scale * (badCyclicTuples x m q).card ≤ M ^ q := by
    intro m hm
    exact rough_cyclic_failure_scaled_card_le hp.two_le_x hm
      hp.logScale_pos hp.secondaryScale_pos hp.reciprocalScale_two_le
      hp.reciprocalScale_le_logScale hp.reciprocalScale_le_cutoff
      hp.scale_le_three_pow hp.scale_le_two_pow_secondary
      hp.reciprocal_mul_secondary_le hp.five_scale_le_tupleLength
      hp.tupleLength_le_six_scale hp.scale_le_sixteen_mul
      hp.rough_card_lower hp.secondary_fourth_le
  have hbad : ∀ m ∈ roughNumbers x, (badCyclicTuples x m q).card ≤ B := by
    intro m hm
    apply (Nat.le_div_iff_mul_le hscale).mpr
    simpa [Nat.mul_comm] using hscaledBad m hm
  have hevent :
      2 * Fintype.card
          (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) * B ≤
        M ^ q := by
    calc
      2 * Fintype.card
          (CoordinateSubset (1280 * q) q × ↑(roughNumbers x)) * B ≤
          scale * B := Nat.mul_le_mul_right B hfactor
      _ ≤ M ^ q := by
        exact Nat.mul_div_le (M ^ q) scale
  have hqpos : 0 < q := by
    have : 0 < 5 * cyclicLogScale x :=
      Nat.mul_pos (by omega) hp.logScale_pos
    exact this.trans_le hp.five_scale_le_tupleLength
  have hqone : 1 ≤ q := hqpos
  have hqN : q ≤ 1280 * q := by omega
  have hN : 1 ≤ 1280 * q := by
    omega
  have hsmall := sample_counting_inequality_of_two_budgets
    (x := x) (N := 1280 * q) (q := q) (B := B)
    hqN hN hM hevent hcollision
  exact exists_robustBlock_of_bad_bound hlev hx (by simpa [q] using hqone)
    hcut hbad (by simpa [q, M, B, scale] using hsmall)

/-- For all sufficiently large scales, the finite probabilistic selection
produces an exact CFP robust block. -/
theorem eventually_exists_robustBlock
    (hlev : FortySetIntervalPrinciple) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∃ S : Finset ℕ, IsRobustBlock x (ceilSixLog x) S := by
  filter_upwards [eventually_cyclicGrowthParameterBounds,
    eventually_cyclic_collision_supply,
    Filter.eventually_ge_atTop 200,
    tendsto_roughCutoff.eventually (Filter.eventually_ge_atTop 17),
    tendsto_cyclicLogScale.eventually
      (Filter.eventually_ge_atTop (2 ^ 16008))]
      with x hp hcollision hx hcut hlarge
  have hcollision' :
      2 * (1280 * cyclicTupleLength x) *
          (1280 * cyclicTupleLength x) < (roughNumbers x).card := by
    simpa [pow_two, Nat.mul_assoc] using hcollision
  simpa [cyclicTupleLength, ceilSixLog] using
    exists_robustBlock_of_parameterBounds hlev hp hx hcut hlarge hcollision'

/-! ## Conversion to the dyadic assembly interface -/

/-- Eventual robust blocks with the exact integerized CFP constants imply the
raw dyadic-block interface.  The deliberately slack dyadic constants absorb
all ceiling errors using `4*k ≤ ceilSixLog (2^k) ≤ 6*k`. -/
theorem hasRobustDyadicBlocks_of_eventually_robustBlocks
    (hblocks : ∀ᶠ x : ℕ in Filter.atTop,
      ∃ S : Finset ℕ, IsRobustBlock x (ceilSixLog x) S) :
    HasRobustDyadicBlocks := by
  rw [Filter.eventually_atTop] at hblocks
  obtain ⟨K, hK⟩ := hblocks
  refine ⟨1000, 2200, 8000, K, by omega, by omega, by omega, ?_⟩
  intro k hk
  have hkleAux : ∀ j : ℕ, j ≤ 2 ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Nat.pow_succ]
        have hone : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
  have hkle := hkleAux k
  obtain ⟨S, hS⟩ := hK (2 ^ k) (hk.trans hkle)
  refine ⟨S, ?_⟩
  rcases hS with ⟨hSIco, hScard, hcover⟩
  have hqUpper := ceilSixLog_two_pow_le k
  have hqLower := ceilSixLog_two_pow_ge k
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hn' := Finset.mem_Ico.mp (hSIco hn)
    rw [Nat.pow_succ]
    omega
  · rw [hScard]
    omega
  · intro T hTS hmajor
    have hTcard : 640 * ceilSixLog (2 ^ k) ≤ T.card := by
      rw [hScard] at hmajor
      omega
    have hfull := hcover T hTS hTcard
    intro n hn
    apply hfull
    rw [Finset.mem_Icc] at hn ⊢
    constructor
    · calc
        160 * ceilSixLog (2 ^ k) * 2 ^ k ≤
            1000 * k * 2 ^ k := by
          apply Nat.mul_le_mul_right
          omega
        _ ≤ n := hn.1
    · calc
        n ≤ 2200 * k * 2 ^ k := hn.2
        _ ≤ 560 * ceilSixLog (2 ^ k) * 2 ^ k := by
          apply Nat.mul_le_mul_right
          omega

/-- The complete probabilistic construction, packaged conditionally only on
the forty-summand Lev theorem. -/
theorem robust_blocks_of_fortySetIntervalPrinciple
    (hlev : FortySetIntervalPrinciple) : HasRobustDyadicBlocks :=
  hasRobustDyadicBlocks_of_eventually_robustBlocks
    (eventually_exists_robustBlock hlev)

/-- Lev's forty-summand interval theorem, specialized to the normalized
finite sets produced by the modular-growth argument. -/
theorem fortySetIntervalPrinciple : FortySetIntervalPrinciple := by
  intro As n Q hlen hn hcard hbound hzero hprim hratio
  exact lev_forty_interval As n Q hlen hn hcard hbound hzero hprim hratio

/-- The unconditional integerized Conlon--Fox--Pham robust dyadic-block
theorem for two colours. -/
theorem robust_blocks : HasRobustDyadicBlocks :=
  robust_blocks_of_fortySetIntervalPrinciple fortySetIntervalPrinciple

end Erdos54
