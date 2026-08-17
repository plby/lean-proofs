/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 903

Erdős--Fowler--Sós--Wilson proved that a pairwise balanced design on
`p^2 + p + 1` points has either exactly that many blocks or at least `p`
more blocks.  The proof below formalizes their incidence-matrix argument.

The detailed mathematical reconstruction is in `tex/903.tex`.
-/

namespace Erdos903

open scoped BigOperators

/-- An indexed family of blocks is a pairwise balanced design of index one.
The lower bound of two on block size is part of the standard definition of a
linear space and rules out irrelevant empty or singleton blocks. -/
def PairwiseBalanced {v b : ℕ} (block : Fin b → Finset (Fin v)) : Prop :=
  (∀ i, 2 ≤ (block i).card) ∧
    ∀ x y, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

/-- The set of block indices incident with a point. -/
def through {v b : ℕ} (block : Fin b → Finset (Fin v)) (x : Fin v) : Finset (Fin b) :=
  Finset.univ.filter fun i ↦ x ∈ block i

/-- The replication number (point degree). -/
def degree {v b : ℕ} (block : Fin b → Finset (Fin v)) (x : Fin v) : ℕ :=
  (through block x).card

@[simp] lemma mem_through {v b : ℕ} {block : Fin b → Finset (Fin v)}
    {x : Fin v} {i : Fin b} : i ∈ through block x ↔ x ∈ block i := by
  simp [through]

lemma degree_eq_sum_indicator {v b : ℕ} (block : Fin b → Finset (Fin v)) (x : Fin v) :
    degree block x = ∑ i : Fin b, (if x ∈ block i then (1 : ℕ) else 0) := by
  classical
  simp [degree, through, Finset.sum_boole]

lemma blocks_inter_card_le_one {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) {i j : Fin b} (hij : i ≠ j) :
    ((block i) ∩ (block j)).card ≤ 1 := by
  classical
  by_contra h
  have htwo : 2 ≤ ((block i) ∩ (block j)).card := by omega
  have hne : ((block i) ∩ (block j)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < ((block i) ∩ (block j)).card) x
  have hxy : x ≠ y := hyx.symm
  have hxi : x ∈ block i := (Finset.mem_inter.mp hx).1
  have hxj : x ∈ block j := (Finset.mem_inter.mp hx).2
  have hyi : y ∈ block i := (Finset.mem_inter.mp hy).1
  have hyj : y ∈ block j := (Finset.mem_inter.mp hy).2
  obtain ⟨k, hk, huniq⟩ := hpb.2 x y hxy
  exact hij ((huniq i ⟨hxi, hyi⟩).trans (huniq j ⟨hxj, hyj⟩).symm)

lemma unique_pair_count {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) {x y : Fin v} (hxy : x ≠ y) :
    ∑ i : Fin b, (if (x ∈ block i ∧ y ∈ block i) then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨i, hi, huniq⟩ := hpb.2 x y hxy
  have hfilter : (Finset.univ.filter fun j : Fin b ↦ x ∈ block j ∧ y ∈ block j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj ↦ huniq j hj, fun hji ↦ hji ▸ hi⟩
  simpa [Finset.sum_boole, hfilter]

lemma partners_sum {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) (x : Fin v) :
    ∑ i : Fin b, (if x ∈ block i then (block i).card - 1 else (0 : ℕ)) = v - 1 := by
  classical
  calc
    ∑ i : Fin b, (if x ∈ block i then (block i).card - 1 else (0 : ℕ)) =
        ∑ i : Fin b, ∑ y : Fin v,
          (if (x ∈ block i ∧ y ∈ block i ∧ y ≠ x) then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hxi : x ∈ block i
            · simp only [hxi, true_and, if_true]
              rw [← Finset.card_erase_of_mem hxi]
              have hfilter :
                  (Finset.univ.filter fun y : Fin v ↦ y ∈ block i ∧ y ≠ x) =
                    (block i).erase x := by
                ext y
                simp [and_comm]
              calc
                ((block i).erase x).card =
                    (Finset.univ.filter fun y : Fin v ↦ y ∈ block i ∧ y ≠ x).card := by
                      rw [hfilter]
                _ = ∑ y : Fin v, (if (y ∈ block i ∧ y ≠ x) then (1 : ℕ) else 0) := by
                      simpa [Finset.sum_boole]
            · simp [hxi]
    _ = ∑ y : Fin v, ∑ i : Fin b,
          (if (x ∈ block i ∧ y ∈ block i ∧ y ≠ x) then (1 : ℕ) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ y : Fin v, (if y ≠ x then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases hyx : y = x
            · subst y
              simp
            · simpa [hyx] using unique_pair_count hpb (fun h ↦ hyx h.symm)
    _ = v - 1 := by
            have hfilter : (Finset.univ.filter fun y : Fin v ↦ y ≠ x) = Finset.univ.erase x := by
              ext y
              simp [ne_comm]
            calc
              ∑ y : Fin v, (if y ≠ x then (1 : ℕ) else 0) =
                  (Finset.univ.filter fun y : Fin v ↦ y ≠ x).card := by
                    change (∑ y ∈ (Finset.univ : Finset (Fin v)),
                      if y ≠ x then (1 : ℕ) else 0) = _
                    exact Finset.sum_boole (R := ℕ) (fun y : Fin v ↦ y ≠ x) Finset.univ
              _ = (Finset.univ.erase x).card := by rw [hfilter]
              _ = v - 1 := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ x)]
                simp

lemma flags_sum {v b : ℕ} (block : Fin b → Finset (Fin v)) :
    ∑ i : Fin b, (block i).card = ∑ x : Fin v, degree block x := by
  classical
  simp_rw [degree_eq_sum_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.sum_boole]

/-- A point outside a block lies on at least as many blocks as that block has
points: join it to every point of the block. -/
lemma block_card_le_degree_of_not_mem {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) {i : Fin b} {x : Fin v} (hxi : x ∉ block i) :
    (block i).card ≤ degree block x := by
  classical
  let f : Fin v → Fin b := fun y ↦ if hy : y ∈ block i then
    Classical.choose (hpb.2 x y (fun h ↦ hxi (h ▸ hy))).exists else i
  have hf_mem (y : Fin v) (hy : y ∈ block i) : f y ∈ through block x := by
    simp only [f, dif_pos hy, mem_through]
    exact (Classical.choose_spec (hpb.2 x y (fun h ↦ hxi (h ▸ hy))).exists).1
  have hf_inj : Set.InjOn f ↑(block i) := by
    intro y hy z hz hyz
    have hy' : y ∈ block i := hy
    have hz' : z ∈ block i := hz
    have hjy := Classical.choose_spec (hpb.2 x y (fun h ↦ hxi (h ▸ hy'))).exists
    have hjz := Classical.choose_spec (hpb.2 x z (fun h ↦ hxi (h ▸ hz'))).exists
    have : y = z := by
      by_contra hyz'
      obtain ⟨k, hk, huniq⟩ := hpb.2 y z hyz'
      have hfy : f y = Classical.choose (hpb.2 x y (fun h ↦ hxi (h ▸ hy'))).exists := by
        dsimp [f]
        rw [dif_pos hy']
      have hfz : f z = Classical.choose (hpb.2 x z (fun h ↦ hxi (h ▸ hz'))).exists := by
        dsimp [f]
        rw [dif_pos hz']
      have hxyf : x ∈ block (f y) := by simpa [hfy] using hjy.1
      have hyyf : y ∈ block (f y) := by simpa [hfy] using hjy.2
      have hzyf : z ∈ block (f y) := by
        rw [hyz]
        simpa [hfz] using hjz.2
      have hfi : f y ≠ i := by
        intro h
        exact hxi (h ▸ hxyf)
      exact hfi ((huniq (f y) ⟨hyyf, hzyf⟩).trans (huniq i ⟨hy', hz'⟩).symm)
    exact this
  have himage : (block i).image f ⊆ through block x := by
    intro j hj
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
    exact hf_mem y hy
  calc
    (block i).card = ((block i).image f).card := (Finset.card_image_iff.mpr hf_inj).symm
    _ ≤ (through block x).card := Finset.card_le_card himage
    _ = degree block x := rfl

lemma ordered_pairs_ne_card {α : Type*} [DecidableEq α] (s : Finset α) :
    (∑ x ∈ s, ∑ y ∈ s, if x ≠ y then (1 : ℕ) else 0) = s.card * (s.card - 1) := by
  calc
    (∑ x ∈ s, ∑ y ∈ s, if x ≠ y then (1 : ℕ) else 0) =
        ∑ x ∈ s, (s.erase x).card := by
          apply Finset.sum_congr rfl
          intro x hx
          have hfilter : (s.filter fun y ↦ x ≠ y) = s.erase x := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_erase]
            tauto
          calc
            (∑ y ∈ s, if x ≠ y then (1 : ℕ) else 0) =
                (s.filter fun y ↦ x ≠ y).card := Finset.sum_boole (R := ℕ) _ s
            _ = (s.erase x).card := by rw [hfilter]
    _ = ∑ _x ∈ s, (s.card - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.card_erase_of_mem hx]
    _ = s.card * (s.card - 1) := by simp

lemma sum_if_mem_eq_sum_nat {m : Type*} [Fintype m] [DecidableEq m]
    (A : Finset m) (f : m → ℕ) :
    ∑ x, (if x ∈ A then f x else 0) = ∑ x ∈ A, f x := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

lemma global_ordered_pair_count {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) :
    ∑ i, (block i).card * ((block i).card - 1) = v * (v - 1) := by
  classical
  calc
    ∑ i, (block i).card * ((block i).card - 1) =
        ∑ i, ∑ x ∈ block i, ∑ y ∈ block i,
          (if x ≠ y then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (ordered_pairs_ne_card (block i)).symm
    _ = ∑ i, ∑ x, ∑ y,
          (if x ∈ block i ∧ y ∈ block i ∧ x ≠ y then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        ∑ x ∈ block i, ∑ y ∈ block i, (if x ≠ y then (1 : ℕ) else 0) =
            ∑ x ∈ block i, ∑ y,
              (if y ∈ block i then (if x ≠ y then (1 : ℕ) else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact (sum_if_mem_eq_sum_nat (block i)
            (fun y ↦ if x ≠ y then (1 : ℕ) else 0)).symm
        _ = ∑ x, (if x ∈ block i then
              (∑ y, if y ∈ block i then (if x ≠ y then (1 : ℕ) else 0) else 0) else 0) :=
          (sum_if_mem_eq_sum_nat (block i) _).symm
        _ = ∑ x, ∑ y,
              (if x ∈ block i ∧ y ∈ block i ∧ x ≠ y then (1 : ℕ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hxi : x ∈ block i
          · simp only [hxi, if_true, true_and]
            apply Finset.sum_congr rfl
            intro y _hy
            by_cases hyi : y ∈ block i <;> by_cases hxy : x = y <;>
              simp [hyi, hxy]
          · simp [hxi]
    _ = ∑ x, ∑ y, ∑ i,
          (if x ≠ y ∧ x ∈ block i ∧ y ∈ block i then (1 : ℕ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hxy : x = y <;> by_cases hxi : x ∈ block i <;>
        by_cases hyi : y ∈ block i <;> simp [hxy, hxi, hyi]
    _ = ∑ x : Fin v, ∑ y : Fin v, (if x ≠ y then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hxy : x = y
      · subst y
        simp
      · simp only [ne_eq, hxy, not_false_eq_true, true_and, if_true]
        exact unique_pair_count hpb hxy
    _ = v * (v - 1) := by
      simpa using ordered_pairs_ne_card (Finset.univ : Finset (Fin v))

/-- The cross-multiplied Stanton--Kalbfleisch inequality. -/
theorem stanton_kalbfleisch {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) {j₀ : Fin b} (hproper : (block j₀).card < v) :
    (block j₀).card ^ 2 * (v - (block j₀).card) ≤ (b - 1) * (v - 1) := by
  classical
  let A := block j₀
  let O : Finset (Fin v) := Finset.univ \ A
  let I : Finset (Fin b) := Finset.univ.erase j₀
  let s : Fin b → ℕ := fun i ↦ (block i \ A).card
  let n := O.card
  let k := A.card
  let S := ∑ i ∈ I, s i
  have hOcard : n = v - k := by
    dsimp [n, O, k]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp
  have hIcard : I.card = b - 1 := by
    simp [I]
  have hnpos : 0 < n := by
    have hkproper : k < v := by simpa [k, A] using hproper
    rw [hOcard]
    omega
  have hpair_count (x y : Fin v) (hx : x ∈ O) (hy : y ∈ O) (hxy : x ≠ y) :
      (∑ i ∈ I, if (x ∈ block i ∧ y ∈ block i) then (1 : ℕ) else 0) = 1 := by
    obtain ⟨j, hj, huniq⟩ := hpb.2 x y hxy
    have hjne : j ≠ j₀ := by
      intro h
      have hxA : x ∈ A := by simpa [A, h] using hj.1
      exact (Finset.mem_sdiff.mp hx).2 hxA
    have hfilter : (I.filter fun i ↦ x ∈ block i ∧ y ∈ block i) = {j} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hi ↦ huniq i hi.2
      · intro hij
        subst i
        exact ⟨by simp [I, hjne], hj⟩
    calc
      (∑ i ∈ I, if (x ∈ block i ∧ y ∈ block i) then (1 : ℕ) else 0) =
          (I.filter fun i ↦ x ∈ block i ∧ y ∈ block i).card := by
            exact Finset.sum_boole (R := ℕ) _ I
      _ = 1 := by simp [hfilter]
  have hpairs : ∑ i ∈ I, s i * (s i - 1) = n * (n - 1) := by
    calc
      ∑ i ∈ I, s i * (s i - 1) =
          ∑ i ∈ I, ∑ x ∈ O, ∑ y ∈ O,
            if (x ∈ block i ∧ y ∈ block i ∧ x ≠ y) then (1 : ℕ) else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hset : block i \ A = O ∩ block i := by
                ext x
                simp [O, and_comm]
              change (block i \ A).card * ((block i \ A).card - 1) = _
              rw [hset]
              have hinter : O ∩ block i = O.filter fun x ↦ x ∈ block i := by
                ext x
                simp
              rw [hinter]
              rw [← ordered_pairs_ne_card (O.filter fun x ↦ x ∈ block i)]
              simp only [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases hxi : x ∈ block i
              · simp only [hxi, if_true]
                apply Finset.sum_congr rfl
                intro y hy
                by_cases hyi : y ∈ block i <;> simp [hxi, hyi, and_assoc]
              · simp [hxi]
      _ = ∑ x ∈ O, ∑ y ∈ O, ∑ i ∈ I,
            if (x ∈ block i ∧ y ∈ block i ∧ x ≠ y) then (1 : ℕ) else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
      _ = ∑ x ∈ O, ∑ y ∈ O, if x ≠ y then (1 : ℕ) else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hxy : x = y
              · subst y
                simp
              · simpa [hxy] using hpair_count x y hx hy hxy
      _ = n * (n - 1) := by
              simpa [n] using ordered_pairs_ne_card O
  have hflags : S = ∑ x ∈ O, degree block x := by
    calc
      S = ∑ i ∈ I, ∑ x ∈ O, if x ∈ block i then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hset : block i \ A = O.filter fun x ↦ x ∈ block i := by
          ext x
          simp [O, and_comm]
        change (block i \ A).card = _
        rw [hset]
        exact (Finset.sum_boole (R := ℕ) (fun x ↦ x ∈ block i) O).symm
      _ = ∑ x ∈ O, ∑ i ∈ I, if x ∈ block i then (1 : ℕ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ O, degree block x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [degree_eq_sum_indicator]
        have hxA : x ∉ A := (Finset.mem_sdiff.mp hx).2
        have hxj : x ∉ block j₀ := by simpa [A] using hxA
        simpa [I, hxj] using
          (Finset.sum_erase_add Finset.univ
            (fun i : Fin b ↦ if x ∈ block i then (1 : ℕ) else 0)
            (Finset.mem_univ j₀))
  have hS_lower : k * n ≤ S := by
    rw [hflags]
    calc
      k * n = ∑ _x ∈ O, k := by simp [n, Nat.mul_comm]
      _ ≤ ∑ x ∈ O, degree block x := by
        gcongr with x hx
        apply block_card_le_degree_of_not_mem hpb
        exact (Finset.mem_sdiff.mp hx).2
  have hsquares : ∑ i ∈ I, (s i) ^ 2 = n * (n - 1) + S := by
    rw [← hpairs]
    simp only [S]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases hsi : s i with
    | zero => simp [hsi]
    | succ q => simp [hsi, pow_two]; ring
  have hcauchy : S ^ 2 ≤ I.card * ∑ i ∈ I, (s i) ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  rw [hsquares] at hcauchy
  let C : ℚ := ((n * (n - 1) : ℕ) : ℚ)
  have hkn : ((k * n : ℕ) : ℚ) ≤ S := by exact_mod_cast hS_lower
  have hC : (0 : ℚ) ≤ C := by positivity
  have hk : 2 ≤ k := hpb.1 j₀
  have hknpos : (0 : ℚ) < (k * n : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < k) hnpos
  have hSpos : (0 : ℚ) < S := hknpos.trans_le hkn
  have hden1 : (0 : ℚ) < C + (k * n : ℕ) := by linarith
  have hden2 : (0 : ℚ) < C + S := by linarith
  have hratio : (((k * n : ℕ) : ℚ) ^ 2) / (C + (k * n : ℕ)) ≤
      ((S : ℚ) ^ 2) / (C + S) := by
    rw [div_le_div_iff₀ hden1 hden2]
    have hfac : (0 : ℚ) ≤ ((S : ℚ) - (k * n : ℕ)) *
        (C * ((S : ℚ) + (k * n : ℕ)) + ((k * n : ℕ) : ℚ) * S) := by
      apply mul_nonneg (sub_nonneg.mpr hkn)
      apply add_nonneg
      · exact mul_nonneg hC (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith
  have hcauchyQ : (S : ℚ) ^ 2 ≤ (I.card : ℚ) * (C + S) := by
    dsimp [C]
    exact_mod_cast hcauchy
  have hupper : (S : ℚ) ^ 2 / (C + S) ≤ I.card := by
    rw [div_le_iff₀ hden2]
    simpa [mul_comm] using hcauchyQ
  have hdenN : n * (n - 1) + k * n = n * (n + k - 1) := by
    rw [Nat.mul_comm k n, ← Nat.mul_add]
    congr 1
    omega
  have hdenQ : C + ((k * n : ℕ) : ℚ) = ((n * (n + k - 1) : ℕ) : ℚ) := by
    dsimp [C]
    exact_mod_cast hdenN
  have hcancel : (((k * n : ℕ) : ℚ) ^ 2) / ((n * (n + k - 1) : ℕ) : ℚ) =
      ((k ^ 2 * n : ℕ) : ℚ) / ((n + k - 1 : ℕ) : ℚ) := by
    have hnQ : (0 : ℚ) < n := by exact_mod_cast hnpos
    have hsumpos : 0 < n + k - 1 := by omega
    have hsumQ : (0 : ℚ) < (n + k - 1 : ℕ) := by exact_mod_cast hsumpos
    push_cast
    field_simp [hnQ.ne', hsumQ.ne']
  have hmainQ : ((k ^ 2 * n : ℕ) : ℚ) ≤ ((I.card * (n + k - 1) : ℕ) : ℚ) := by
    have h := hratio.trans hupper
    rw [hdenQ, hcancel] at h
    have hsumpos : 0 < n + k - 1 := by omega
    rw [div_le_iff₀ (by exact_mod_cast hsumpos : (0 : ℚ) < (n + k - 1 : ℕ))] at h
    simpa only [Nat.cast_mul, Nat.cast_pow] using h
  have hmainN : k ^ 2 * n ≤ I.card * (n + k - 1) := by exact_mod_cast hmainQ
  have hnk : n + k - 1 = v - 1 := by rw [hOcard]; omega
  rw [hOcard, hIcard] at hmainN
  have hkproper : k < v := by simpa [k, A] using hproper
  have hsubadd : v - k + k - 1 = v - 1 := by omega
  rw [hsubadd] at hmainN
  simpa [k, A] using hmainN

lemma through_inter_card_eq_one {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) {x y : Fin v} (hxy : x ≠ y) :
    ((through block x) ∩ (through block y)).card = 1 := by
  classical
  obtain ⟨i, hi, huniq⟩ := hpb.2 x y hxy
  have hset : (through block x) ∩ (through block y) = {i} := by
    ext j
    simp only [Finset.mem_inter, mem_through, Finset.mem_singleton]
    exact ⟨fun hj ↦ huniq j hj, fun hji ↦ hji ▸ hi⟩
  simp [hset]

lemma two_degree_sub_one_le_blocks {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) {x y : Fin v} (hxy : x ≠ y) :
    degree block x + degree block y - 1 ≤ b := by
  classical
  have hinter := through_inter_card_eq_one hpb hxy
  have hunion : ((through block x) ∪ (through block y)).card ≤ b := by
    calc
      _ ≤ (Finset.univ : Finset (Fin b)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = b := by simp only [Finset.card_univ, Fintype.card_fin]
  have hcard := Finset.card_union_add_card_inter (through block x) (through block y)
  dsimp [degree]
  omega

lemma cubic_mono {V x y : ℚ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 3 * y ≤ 2 * V) :
    x ^ 2 * (V - x) ≤ y ^ 2 * (V - y) := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have h₁ : 0 ≤ (2 * V - 3 * y) * (x + y) :=
    mul_nonneg (by linarith) (by linarith)
  have h₂ : 0 ≤ (y - x) * (y + 2 * x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
  have hmid : 0 ≤ V * (x + y) - (x ^ 2 + x * y + y ^ 2) := by
    nlinarith
  have hprod : 0 ≤ (y - x) * (V * (x + y) - (x ^ 2 + x * y + y ^ 2)) :=
    mul_nonneg (sub_nonneg.mpr hxy) hmid
  nlinarith [hprod]

lemma block_card_lt_points {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) (hmore : v < b) (i : Fin b) : (block i).card < v := by
  classical
  have hki : (block i).card ≤ v := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (block i)
  have hv2 : 2 ≤ v := (hpb.1 i).trans hki
  have hb2 : 2 ≤ b := hv2.trans hmore.le
  by_contra hnot
  have hkeq : (block i).card = v := by omega
  have hiuniv : block i = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [hkeq]
  have hunivtwo : 1 < (Finset.univ : Finset (Fin b)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using (show 1 < b by omega)
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hunivtwo i
  have hinter := blocks_inter_card_le_one hpb hji
  have hjtwo := hpb.1 j
  simp [hiuniv] at hinter
  omega

/-- EFSW's preliminary reduction: in a hypothetical design in the forbidden
interval every block has at most `p + 1` points. -/
lemma block_card_le_order_add_one {p v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hp : 2 ≤ p) (hv : v = p ^ 2 + p + 1) (hpb : PairwiseBalanced block)
    (hmore : v < b) (hless : b < v + p) (i : Fin b) :
    (block i).card ≤ p + 1 := by
  classical
  let k := (block i).card
  have hkproper : k < v := by simpa [k] using block_card_lt_points hpb hmore i
  by_contra hbad
  have hklarge : p + 2 ≤ k := by omega
  by_cases hsmall : 3 * k ≤ 2 * v
  · have hSK := stanton_kalbfleisch hpb (j₀ := i) (by simpa [k] using hkproper)
    have hkle : k ≤ v := hkproper.le
    have hv1 : 1 ≤ v := by omega
    have hSKQ : (k : ℚ) ^ 2 * ((v : ℚ) - k) ≤
        ((b : ℚ) - 1) * ((v : ℚ) - 1) := by
      have hvksub : (((v - k : ℕ) : ℚ)) = (v : ℚ) - k := Nat.cast_sub hkle
      have hbsub : (((b - 1 : ℕ) : ℚ)) = (b : ℚ) - 1 :=
        Nat.cast_sub (by omega)
      have hvsub : (((v - 1 : ℕ) : ℚ)) = (v : ℚ) - 1 := Nat.cast_sub hv1
      rw [← hvksub, ← hbsub, ← hvsub]
      exact_mod_cast hSK
    have hmono := cubic_mono (V := (v : ℚ)) (x := (p + 2 : ℕ)) (y := k)
      (by positivity) (by exact_mod_cast hklarge) (by exact_mod_cast hsmall)
    have hbup : b - 1 ≤ v + p - 2 := by omega
    have hbupQ : ((b : ℚ) - 1) ≤ (v + p - 2 : ℕ) := by
      have hbsub : (((b - 1 : ℕ) : ℚ)) = (b : ℚ) - 1 :=
        Nat.cast_sub (by omega)
      rw [← hbsub]
      exact_mod_cast hbup
    have hvQ : (v : ℚ) = p ^ 2 + p + 1 := by exact_mod_cast hv
    have hpQ : (2 : ℚ) ≤ p := by exact_mod_cast hp
    have hnonneg : (0 : ℚ) ≤ (v : ℚ) - 1 := sub_nonneg.mpr (by exact_mod_cast hv1)
    have hupper : ((b : ℚ) - 1) * ((v : ℚ) - 1) ≤
        (v + p - 2 : ℕ) * ((v : ℚ) - 1) :=
      mul_le_mul_of_nonneg_right hbupQ hnonneg
    push_cast at hmono hupper
    have hvp2 : (((v + p - 2 : ℕ) : ℚ)) = (v : ℚ) + p - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ v + p)]
      push_cast
      rfl
    rw [hvp2] at hupper
    have hpoly : (0 : ℚ) < ((p : ℚ) + 1) * ((p : ℚ) ^ 2 + p - 4) := by
      apply mul_pos
      · linarith
      · nlinarith [sq_nonneg ((p : ℚ) - 2)]
    have hstrict : ((v : ℚ) + p - 2) * ((v : ℚ) - 1) <
        ((p : ℚ) + 2) ^ 2 * ((v : ℚ) - (p + 2)) := by
      calc
        ((v : ℚ) + p - 2) * ((v : ℚ) - 1) =
            ((p : ℚ) + 2) ^ 2 * ((v : ℚ) - (p + 2)) -
              ((p : ℚ) + 1) * ((p : ℚ) ^ 2 + p - 4) := by rw [hvQ]; ring
        _ < ((p : ℚ) + 2) ^ 2 * ((v : ℚ) - (p + 2)) := sub_lt_self _ hpoly
    nlinarith [hmono, hSKQ, hupper, hstrict]
  · have hbig : 2 * v < 3 * k := by omega
    let O : Finset (Fin v) := Finset.univ \ block i
    have hOcard : O.card = v - k := by
      dsimp [O, k]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ (block i))]
      simp
    by_cases htwo : 2 ≤ O.card
    · have hne : O.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hne
      obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < O.card) x
      have hxi : x ∉ block i := (Finset.mem_sdiff.mp hx).2
      have hyi : y ∉ block i := (Finset.mem_sdiff.mp hy).2
      have hdx := block_card_le_degree_of_not_mem hpb hxi
      have hdy := block_card_le_degree_of_not_mem hpb hyi
      have hdeg := two_degree_sub_one_le_blocks hpb hyx.symm
      have h2k : 2 * k - 1 ≤ b := by
        change k ≤ degree block x at hdx
        change k ≤ degree block y at hdy
        omega
      by_cases hp2 : p = 2
      · subst p
        norm_num at hv
        omega
      have hp3 : 3 ≤ p := by omega
      have hvQ : (v : ℚ) = p ^ 2 + p + 1 := by exact_mod_cast hv
      have hpQ : (2 : ℚ) ≤ p := by exact_mod_cast hp
      have hbigQ : (2 : ℚ) * v < 3 * k := by exact_mod_cast hbig
      have h2kQ : (2 : ℚ) * k - 1 ≤ b := by
        have hsub : (((2 * k - 1 : ℕ) : ℚ)) = (2 : ℚ) * k - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
          push_cast
          rfl
        rw [← hsub]
        exact_mod_cast h2k
      have hlessQ : (b : ℚ) < v + p := by exact_mod_cast hless
      have hp3Q : (3 : ℚ) ≤ p := by exact_mod_cast hp3
      nlinarith [mul_nonneg (sub_nonneg.mpr hp3Q) (by linarith : (0 : ℚ) ≤ p + 1)]
    · have hOsmall : O.card ≤ 1 := by omega
      have hOpos : 0 < O.card := by rw [hOcard]; omega
      have hOone : O.card = 1 := by omega
      obtain ⟨z, hOeq⟩ := Finset.card_eq_one.mp hOone
      have hzO : z ∈ O := by simp [hOeq]
      have hznot : z ∉ block i := (Finset.mem_sdiff.mp hzO).2
      have hother (j : Fin b) (hji : j ≠ i) : z ∈ block j ∧ (block j).card = 2 := by
        have hinter := blocks_inter_card_le_one hpb hji.symm
        have hjtwo := hpb.1 j
        have hzmem : z ∈ block j := by
          by_contra hzj
          have hsub : block j ⊆ block i := by
            intro x hxj
            by_contra hxi
            have hxO : x ∈ O := by simp [O, hxj, hxi]
            have : x = z := by simpa [hOeq] using hxO
            exact hzj (this ▸ hxj)
          have heq : block i ∩ block j = block j := Finset.inter_eq_right.mpr hsub
          rw [heq] at hinter
          omega
        have herase : (block j).erase z ⊆ block i ∩ block j := by
          intro x hx
          have hxj : x ∈ block j := (Finset.mem_erase.mp hx).2
          have hxz : x ≠ z := (Finset.mem_erase.mp hx).1
          have hxA : x ∈ block i := by
            by_contra hxi
            have hxO : x ∈ O := by simp [O, hxj, hxi]
            have : x = z := by simpa [hOeq] using hxO
            exact hxz this
          exact Finset.mem_inter.mpr ⟨hxA, hxj⟩
        have herasecard : ((block j).erase z).card ≤ 1 :=
          (Finset.card_le_card herase).trans hinter
        have hcard : (block j).card ≤ 2 := by
          rw [← Finset.card_erase_add_one hzmem]
          omega
        exact ⟨hzmem, by omega⟩
      have hdegz : degree block z = b - 1 := by
        have hset : through block z = Finset.univ.erase i := by
          ext j
          by_cases hji : j = i
          · subst j
            simp [hznot]
          · simp [hji, (hother j hji).1]
        simp [degree, hset]
      have hpartner := partners_sum hpb z
      have hdegv : degree block z = v - 1 := by
        rw [degree_eq_sum_indicator]
        rw [← hpartner]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hzj : z ∈ block j
        · have hji : j ≠ i := fun h ↦ hznot (h ▸ hzj)
          simp [hzj, (hother j hji).2]
        · simp [hzj]
      omega

lemma degree_ge_order_add_one {p v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hp : 2 ≤ p) (hv : v = p ^ 2 + p + 1) (hpb : PairwiseBalanced block)
    (hmax : ∀ i, (block i).card ≤ p + 1) (x : Fin v) :
    p + 1 ≤ degree block x := by
  classical
  have hsum : v - 1 ≤ p * degree block x := by
    rw [← partners_sum hpb x, degree_eq_sum_indicator, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    by_cases hxi : x ∈ block i
    · simp only [hxi, if_pos, mul_one]
      have := hmax i
      omega
    · simp [hxi]
  have hvsub : v - 1 = p ^ 2 + p := by omega
  rw [hvsub] at hsum
  by_contra hbad
  have hdeg : degree block x ≤ p := by omega
  have hmul := Nat.mul_le_mul_left p hdeg
  simp only [pow_two] at hsum
  omega

lemma sum_indicator_mem_eq_card_inter {v : ℕ} (A B : Finset (Fin v)) :
    ∑ x ∈ A, (if x ∈ B then 1 else 0) = (A ∩ B).card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert x A hx ih =>
      by_cases hxb : x ∈ B
      · simp [hx, hxb, ih]
      · simp [hx, hxb, ih]

lemma sum_degrees_on_block {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (i : Fin b) :
    ∑ x ∈ block i, degree block x = ∑ j, (block i ∩ block j).card := by
  classical
  calc
    ∑ x ∈ block i, degree block x =
        ∑ x ∈ block i, ∑ j, (if x ∈ block j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact degree_eq_sum_indicator block x
    _ = ∑ j, ∑ x ∈ block i, (if x ∈ block j then 1 else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ j, (block i ∩ block j).card := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact sum_indicator_mem_eq_card_inter (block i) (block j)

lemma sum_degrees_on_block_le {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) (i : Fin b) :
    ∑ x ∈ block i, degree block x ≤ (block i).card + b - 1 := by
  classical
  rw [sum_degrees_on_block i]
  calc
    ∑ j, (block i ∩ block j).card ≤
        ∑ j, (if j = i then (block i).card else 1) := by
          apply Finset.sum_le_sum
          intro j _hj
          by_cases hji : j = i
          · subst j
            simp
          · simp only [hji, if_false]
            exact blocks_inter_card_le_one hpb (Ne.symm hji)
    _ = (block i).card + b - 1 := by
          rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin b))
            (fun j ↦ if j = i then (block i).card else 1) (Finset.mem_univ i)]
          have hsumone :
              ∑ j ∈ (Finset.univ : Finset (Fin b)).erase i,
                  (if j = i then (block i).card else 1) =
                ∑ _j ∈ (Finset.univ : Finset (Fin b)).erase i, 1 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [if_neg (Finset.mem_erase.mp hj).1]
          rw [hsumone]
          have hones :
              ∑ _j ∈ (Finset.univ : Finset (Fin b)).erase i, (1 : ℕ) = b - 1 := by
            calc
              _ = ((Finset.univ : Finset (Fin b)).erase i).card * 1 :=
                Finset.sum_const_nat (fun _j _hj ↦ rfl)
              _ = b - 1 := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
                simp only [Finset.card_univ, Fintype.card_fin, mul_one]
          rw [hones]
          simp only [if_pos]
          have hbpos : 0 < b := (Nat.zero_le i.val).trans_lt i.isLt
          omega

/-- In a putative counterexample, at least one point has the minimum possible
degree `p + 1`. -/
lemma exists_degree_eq_order_add_one {p v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hp : 2 ≤ p) (hv : v = p ^ 2 + p + 1) (hpb : PairwiseBalanced block)
    (hmore : v < b) (hless : b < v + p)
    (hmax : ∀ i, (block i).card ≤ p + 1) :
    ∃ x, degree block x = p + 1 := by
  classical
  have hmin : ∀ x, p + 1 ≤ degree block x :=
    degree_ge_order_add_one hp hv hpb hmax
  by_contra hnone
  have hstrict : ∀ x, p + 2 ≤ degree block x := by
    intro x
    have hx := hmin x
    have hne : degree block x ≠ p + 1 := by
      intro heq
      exact hnone ⟨x, heq⟩
    omega
  by_cases hlarge : ∃ i, (block i).card = p + 1
  · obtain ⟨i, hi⟩ := hlarge
    have hlower : (p + 1) * (p + 2) ≤ ∑ x ∈ block i, degree block x := by
      calc
        (p + 1) * (p + 2) = ∑ _x ∈ block i, (p + 2) := by simp [hi]
        _ ≤ ∑ x ∈ block i, degree block x := by
          apply Finset.sum_le_sum
          intro x _hx
          exact hstrict x
    have hupper := sum_degrees_on_block_le hpb i
    rw [hi] at hupper
    have hvQ : (v : ℚ) = p ^ 2 + p + 1 := by exact_mod_cast hv
    have hlowerQ : ((p : ℚ) + 1) * (p + 2) ≤
        (∑ x ∈ block i, degree block x : ℕ) := by exact_mod_cast hlower
    have hupperQ : (∑ x ∈ block i, degree block x : ℕ) ≤
        (p : ℚ) + b := by exact_mod_cast (show
          ∑ x ∈ block i, degree block x ≤ p + b by omega)
    have hlessQ : (b : ℚ) < v + p := by exact_mod_cast hless
    nlinarith
  · have hsmall : ∀ i, (block i).card ≤ p := by
      intro i
      have := hmax i
      have hne : (block i).card ≠ p + 1 := by
        intro heq
        exact hlarge ⟨i, heq⟩
      omega
    have hcount : (p + 2) * v ≤ p * b := by
      calc
        (p + 2) * v = ∑ _x : Fin v, (p + 2) := by simp [Nat.mul_comm]
        _ ≤ ∑ x, degree block x := by
          apply Finset.sum_le_sum
          intro x _hx
          exact hstrict x
        _ = ∑ i, (block i).card := (flags_sum block).symm
        _ ≤ ∑ _i : Fin b, p := by
          apply Finset.sum_le_sum
          intro i _hi
          exact hsmall i
        _ = p * b := by simp [Nat.mul_comm]
    have hvQ : (v : ℚ) = p ^ 2 + p + 1 := by exact_mod_cast hv
    have hpQ : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
    have hcountQ : ((p : ℚ) + 2) * v ≤ p * b := by exact_mod_cast hcount
    have hlessQ : (b : ℚ) < v + p := by exact_mod_cast hless
    nlinarith

lemma matrix_rank_add_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℚ) : (A + B).rank ≤ A.rank + B.rank := by
  classical
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  have hrange : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin + LinearMap.range B.mulVecLin := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    change (A + B).mulVec x ∈ LinearMap.range A.mulVecLin + LinearMap.range B.mulVecLin
    rw [Matrix.add_mulVec]
    change A.mulVec x + B.mulVec x ∈ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A.mulVecLin x)
      (LinearMap.mem_range_self B.mulVecLin x)
  exact (Submodule.finrank_mono hrange).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_diagonal_add_pos_vecMulVec {m : Type*} [Fintype m] [DecidableEq m]
    (beta u : m → ℚ) (a : ℚ) (hbeta : ∀ i, 0 < beta i) (ha : 0 ≤ a) :
    (Matrix.diagonal beta + a • Matrix.vecMulVec u u).rank = Fintype.card m := by
  classical
  rw [Matrix.rank]
  refine (LinearMap.finrank_range_of_inj ?_).trans
    (Module.finrank_eq_card_basis (Pi.basisFun ℚ m))
  intro c d hcd
  suffices hzero : c - d = 0 by exact sub_eq_zero.mp hzero
  let z : m → ℚ := c - d
  let S : ℚ := ∑ i, u i * z i
  have hz : (Matrix.diagonal beta + a • Matrix.vecMulVec u u).mulVec z = 0 := by
    dsimp [z]
    change (Matrix.diagonal beta + a • Matrix.vecMulVec u u).mulVec c =
      (Matrix.diagonal beta + a • Matrix.vecMulVec u u).mulVec d at hcd
    rw [Matrix.mulVec_sub, hcd]
    simp
  have hzcoord (i : m) : beta i * z i + a * u i * S = 0 := by
    have hi := congr_fun hz i
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec] at hi
    have hdiag : (Matrix.diagonal beta).mulVec z i = beta i * z i := by
      simp [Matrix.diagonal, Matrix.mulVec, dotProduct]
    simpa [hdiag, S, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hi
  have hweighted : ∑ i, z i * (beta i * z i + a * u i * S) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    rw [hzcoord]
    simp
  have hfirst : ∑ i, z i * (beta i * z i) = ∑ i, beta i * (z i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hsecond : ∑ i, z i * (a * u i * S) = a * S ^ 2 := by
    calc
      _ = (a * S) * ∑ i, u i * z i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = a * S ^ 2 := by dsimp [S]; ring
  have hquad : (∑ i, beta i * (z i) ^ 2) + a * S ^ 2 = 0 := by
    rw [← hfirst, ← hsecond, ← Finset.sum_add_distrib]
    simpa only [mul_add] using hweighted
  have hterm_nonneg (i : m) : 0 ≤ beta i * (z i) ^ 2 :=
    mul_nonneg (hbeta i).le (sq_nonneg _)
  have hsum_nonneg : 0 ≤ ∑ i, beta i * (z i) ^ 2 :=
    Finset.sum_nonneg fun i _hi ↦ hterm_nonneg i
  have halast : 0 ≤ a * S ^ 2 := mul_nonneg ha (sq_nonneg _)
  have hsum_zero : ∑ i, beta i * (z i) ^ 2 = 0 := by linarith
  funext i
  have hi_zero : beta i * (z i) ^ 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j (_hj : j ∈ (Finset.univ : Finset m)) ↦
      hterm_nonneg j).mp hsum_zero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hi_zero with hbi | hzi
  · exact False.elim ((hbeta i).ne' hbi)
  · exact sq_eq_zero_iff.mp hzi

def incidenceMatrix {v b : ℕ} (block : Fin b → Finset (Fin v)) :
    Matrix (Fin v) (Fin b) ℚ := fun x i ↦ if x ∈ block i then 1 else 0

lemma incidence_gram_apply {v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hpb : PairwiseBalanced block) (x y : Fin v) :
    (incidenceMatrix block * (incidenceMatrix block).transpose) x y =
      if x = y then (degree block x : ℚ) else 1 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.mul_apply, incidenceMatrix, Matrix.transpose_apply, if_true]
    have hdegree := degree_eq_sum_indicator block x
    norm_num [ite_mul, mul_ite]
    have hdegreeQ :
        (∑ i : Fin b, (if x ∈ block i then (1 : ℚ) else 0)) = degree block x := by
      exact_mod_cast hdegree.symm
    rw [← hdegreeQ]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hxi : x ∈ block i
    · simp only [hxi, if_true, mul_one]
    · simp only [hxi, if_false, zero_mul]
  · simp only [Matrix.mul_apply, incidenceMatrix, Matrix.transpose_apply, hxy, if_false]
    have hcount := unique_pair_count hpb hxy
    norm_num [ite_mul, mul_ite]
    have hcountQ :
        (∑ i : Fin b, (if (x ∈ block i ∧ y ∈ block i) then (1 : ℚ) else 0)) = 1 := by
      exact_mod_cast hcount
    calc
      _ = ∑ i : Fin b,
          (if (x ∈ block i ∧ y ∈ block i) then (1 : ℚ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hxi : x ∈ block i <;> by_cases hyi : y ∈ block i <;>
          simp only [hxi, hyi, if_true, if_false, and_self, true_and, false_and]
      _ = 1 := hcountQ

lemma diag_add_one_mul_inverse {m : Type*} [Fintype m] [DecidableEq m]
    (d : m → ℚ) (hd : ∀ i, 0 < d i) :
    let w : m → ℚ := fun i ↦ 1 / d i
    let a : ℚ := 1 / (1 + ∑ i, w i)
    ∀ x z, ∑ y, ((if x = y then d x else 0) + 1) *
        ((if y = z then w y else 0) - a * w y * w z) = if x = z then 1 else 0 := by
  classical
  dsimp only
  let w : m → ℚ := fun i ↦ 1 / d i
  let a : ℚ := 1 / (1 + ∑ i, w i)
  have hw (i : m) : 0 < w i := by exact one_div_pos.mpr (hd i)
  have hden : 0 < 1 + ∑ i, w i := by
    have : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _hi ↦ (hw i).le
    linarith
  intro x z
  change (∑ y, ((if x = y then d x else 0) + 1) *
      ((if y = z then w y else 0) - a * w y * w z)) = if x = z then 1 else 0
  have hdw (i : m) : d i * w i = 1 := by
    dsimp [w]
    field_simp [(hd i).ne']
  have ha : a * (1 + ∑ i, w i) = 1 := by
    dsimp [a]
    field_simp [hden.ne']
  have sum_ite_left (q : m → ℚ) (i : m) :
      ∑ j, (if i = j then q j else 0) = q i := by
    calc
      _ = ∑ j, (if j = i then q j else 0) := by
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hji : j = i
        · subst j; simp
        · have hij : i ≠ j := Ne.symm hji
          simp [hji, hij]
      _ = q i := by simp
  have sum_factor (i : m) :
      ∑ j, a * w j * w i = a * w i * ∑ j, w j := by
    calc
      _ = ∑ j, (a * w i) * w j := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = a * w i * ∑ j, w j := by rw [Finset.mul_sum]
  by_cases hxz : x = z
  · subst z
    simp only [mul_sub, add_mul, ite_mul, mul_ite, zero_mul, one_mul, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [sum_ite_left, sum_factor]
    have hcalc :
        d x * (a * w x * w x) + a * w x * ∑ i, w i = w x := by
      calc
        _ = a * w x * (d x * w x + ∑ i, w i) := by ring
        _ = a * w x * (1 + ∑ i, w i) := by
          rw [show d x * w x = 1 from hdw x]
        _ = w x * (a * (1 + ∑ i, w i)) := by ring
        _ = w x * 1 := congrArg (fun q : ℚ ↦ w x * q) ha
        _ = w x := by ring
    rw [hcalc, show d x * w x = 1 from hdw x]
    ring
  · simp only [mul_sub, add_mul, ite_mul, mul_ite, zero_mul, one_mul, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hxz, if_false]
    rw [sum_ite_left, sum_factor]
    have hcalc :
        d x * (a * w x * w z) + a * w z * ∑ i, w i = w z := by
      calc
        _ = a * w z * (d x * w x + ∑ i, w i) := by ring
        _ = a * w z * (1 + ∑ i, w i) := by
          rw [show d x * w x = 1 from hdw x]
        _ = w z * (a * (1 + ∑ i, w i)) := by ring
        _ = w z * 1 := congrArg (fun q : ℚ ↦ w z * q) ha
        _ = w z := by ring
    rw [hcalc]
    ring

lemma projection_rank_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (N : Matrix m n ℚ) (R : Matrix m m ℚ)
    (hR : (N * N.transpose) * R = 1) :
    let Q : Matrix n n ℚ := 1 - N.transpose * R * N
    Fintype.card m + Q.rank ≤ Fintype.card n := by
  classical
  dsimp only
  let Q : Matrix n n ℚ := 1 - N.transpose * R * N
  have hNrank_lower : Fintype.card m ≤ N.rank := by
    calc
      Fintype.card m = (1 : Matrix m m ℚ).rank := Matrix.rank_one.symm
      _ = ((N * N.transpose) * R).rank := by rw [hR]
      _ = (N * (N.transpose * R)).rank := by rw [Matrix.mul_assoc]
      _ ≤ N.rank := Matrix.rank_mul_le_left _ _
  have hNrank : N.rank = Fintype.card m :=
    le_antisymm (Matrix.rank_le_card_height N) hNrank_lower
  have hNQ : N * Q = 0 := by
    dsimp [Q]
    calc
      N * (1 - N.transpose * R * N) = N - ((N * N.transpose) * R) * N := by
        simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = N - (1 : Matrix m m ℚ) * N := by rw [hR]
      _ = 0 := by rw [Matrix.one_mul, sub_self]
  have hrank := Matrix.rank_add_rank_le_card_of_mul_eq_zero hNQ
  rw [hNrank] at hrank
  exact hrank

lemma sum_if_mem_eq_sum {m : Type*} [Fintype m] [DecidableEq m]
    (A : Finset m) (f : m → ℚ) :
    ∑ x, (if x ∈ A then f x else 0) = ∑ x ∈ A, f x := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

lemma weighted_incidence_product {v b : ℕ} (block : Fin b → Finset (Fin v))
    (w : Fin v → ℚ) (a : ℚ) (i j : Fin b) :
    let N := incidenceMatrix block
    let R : Matrix (Fin v) (Fin v) ℚ :=
      fun x y ↦ (if x = y then w x else 0) - a * w x * w y
    (N.transpose * R * N) i j =
      (∑ x ∈ block i ∩ block j, w x) -
        a * (∑ x ∈ block i, w x) * (∑ x ∈ block j, w x) := by
  classical
  dsimp only
  let N := incidenceMatrix block
  let R : Matrix (Fin v) (Fin v) ℚ :=
    fun x y ↦ (if x = y then w x else 0) - a * w x * w y
  change (N.transpose * R * N) i j = _
  have hinner (y : Fin v) :
      ∑ x, N.transpose i x * R x y =
        (if y ∈ block i then w y else 0) - a * (∑ x ∈ block i, w x) * w y := by
    dsimp only [N, R, incidenceMatrix, Matrix.transpose_apply]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hdiag :
        ∑ x : Fin v, (if x ∈ block i then (1 : ℚ) else 0) *
            (if x = y then w x else 0) = if y ∈ block i then w y else 0 := by
      by_cases hyi : y ∈ block i <;> simp [hyi]
    rw [hdiag]
    have hweighted :
        ∑ x : Fin v, (if x ∈ block i then (1 : ℚ) else 0) *
            (a * w x * w y) = a * (∑ x ∈ block i, w x) * w y := by
      calc
        _ = ∑ x, (if x ∈ block i then a * w x * w y else 0) := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hxi : x ∈ block i <;> simp [hxi]
        _ = ∑ x ∈ block i, a * w x * w y := sum_if_mem_eq_sum (block i) _
        _ = a * (∑ x ∈ block i, w x) * w y := by
          rw [Finset.mul_sum, Finset.sum_mul]
    rw [hweighted]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, hinner]
  dsimp only [N, incidenceMatrix]
  simp only [Matrix.transpose_apply, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib]
  have hinter :
      ∑ y : Fin v, (if y ∈ block i then w y else 0) *
          (if y ∈ block j then (1 : ℚ) else 0) =
        ∑ y ∈ block i ∩ block j, w y := by
    calc
      _ = ∑ y, (if y ∈ block i ∩ block j then w y else 0) := by
        apply Finset.sum_congr rfl
        intro y _hy
        by_cases hyi : y ∈ block i <;> by_cases hyj : y ∈ block j <;>
          simp [hyi, hyj]
      _ = _ := sum_if_mem_eq_sum (block i ∩ block j) w
  have hfirst :
      ∑ x : Fin v, (if x ∈ block i then w x *
          (if x ∈ block j then (1 : ℚ) else 0) else 0) =
        ∑ x ∈ block i ∩ block j, w x := by
    calc
      _ = ∑ x : Fin v, (if x ∈ block i then w x else 0) *
          (if x ∈ block j then (1 : ℚ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxi : x ∈ block i <;> simp [hxi]
      _ = _ := hinter
  rw [hfirst]
  have hlast :
      ∑ y : Fin v, (a * (∑ x ∈ block i, w x) * w y) *
          (if y ∈ block j then (1 : ℚ) else 0) =
        a * (∑ x ∈ block i, w x) * (∑ y ∈ block j, w y) := by
    calc
      _ = ∑ y, (if y ∈ block j then a * (∑ x ∈ block i, w x) * w y else 0) := by
        apply Finset.sum_congr rfl
        intro y _hy
        by_cases hyj : y ∈ block j <;> simp [hyj]
      _ = ∑ y ∈ block j, a * (∑ x ∈ block i, w x) * w y :=
        sum_if_mem_eq_sum (block j) _
      _ = _ := by rw [← Finset.mul_sum]
  rw [hlast]

lemma projection_principal_obstruction {m n f : Type*}
    [Fintype m] [Fintype n] [Fintype f]
    [DecidableEq m] [DecidableEq n] [DecidableEq f]
    (N : Matrix m n ℚ) (R : Matrix m m ℚ) (inc : f → n)
    (beta u : f → ℚ) (a w₀ : ℚ)
    (hR : (N * N.transpose) * R = 1)
    (hformula :
      (1 - N.transpose * R * N).submatrix inc inc =
        Matrix.diagonal beta + a • Matrix.vecMulVec u u -
          Matrix.vecMulVec (fun _ ↦ w₀) (fun _ ↦ 1))
    (hbeta : ∀ i, 0 < beta i) (ha : 0 ≤ a) :
    Fintype.card m + Fintype.card f ≤ Fintype.card n + 1 := by
  classical
  let Q : Matrix n n ℚ := 1 - N.transpose * R * N
  let Qf : Matrix f f ℚ := Q.submatrix inc inc
  let H : Matrix f f ℚ := Matrix.diagonal beta + a • Matrix.vecMulVec u u
  let J₀ : Matrix f f ℚ := Matrix.vecMulVec (fun _ ↦ w₀) (fun _ ↦ 1)
  have hQbound : Fintype.card m + Q.rank ≤ Fintype.card n :=
    projection_rank_bound N R hR
  have hHrank : H.rank = Fintype.card f := by
    exact rank_diagonal_add_pos_vecMulVec beta u a hbeta ha
  have hH : H = Qf + J₀ := by
    dsimp only [H, Qf, Q, J₀]
    rw [hformula]
    abel
  have hQfrank : Qf.rank ≤ Q.rank := Matrix.rank_submatrix_le Q inc inc
  have hJrank : J₀.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hlow : Fintype.card f ≤ Q.rank + 1 := by
    rw [← hHrank, hH]
    exact (matrix_rank_add_le Qf J₀).trans (Nat.add_le_add hQfrank hJrank)
  omega

lemma block_weight_defect {p v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hp : 2 ≤ p) (hmin : ∀ x, p + 1 ≤ degree block x)
    (hmax : ∀ i, (block i).card ≤ p + 1)
    {x₀ : Fin v} (hx₀ : degree block x₀ = p + 1)
    {i : Fin b} (hx₀i : x₀ ∈ block i) :
    let d : Fin v → ℚ := fun x ↦ (degree block x : ℚ) - 1
    let w : Fin v → ℚ := fun x ↦ 1 / d x
    let beta := 1 - (∑ x ∈ block i, w x) + w x₀
    0 ≤ beta ∧
      (beta = 0 → (block i).card = p + 1 ∧
        ∀ x ∈ block i, degree block x = p + 1) := by
  classical
  dsimp only
  let d : Fin v → ℚ := fun x ↦ (degree block x : ℚ) - 1
  let w : Fin v → ℚ := fun x ↦ 1 / d x
  let E := (block i).erase x₀
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have hdpos (x : Fin v) : 0 < d x := by
    dsimp [d]
    have hminQ : ((p + 1 : ℕ) : ℚ) ≤ degree block x := by exact_mod_cast hmin x
    have hp2Q : (2 : ℚ) ≤ p := by exact_mod_cast hp
    push_cast at hminQ
    linarith
  have hdge (x : Fin v) : (p : ℚ) ≤ d x := by
    dsimp [d]
    have hminQ : ((p + 1 : ℕ) : ℚ) ≤ degree block x := by exact_mod_cast hmin x
    push_cast at hminQ
    linarith
  have hwle (x : Fin v) : w x ≤ 1 / (p : ℚ) := by
    dsimp [w]
    rw [div_le_div_iff₀ (hdpos x) hpQ]
    simpa using hdge x
  have hwpos (x : Fin v) : 0 < w x := by dsimp [w]; exact one_div_pos.mpr (hdpos x)
  have hEcard : E.card ≤ p := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hx₀i]
    have := hmax i
    omega
  have hsumle : ∑ x ∈ E, w x ≤ 1 := by
    calc
      _ ≤ ∑ _x ∈ E, (1 / (p : ℚ)) := by
        apply Finset.sum_le_sum
        intro x _hx
        exact hwle x
      _ = (E.card : ℚ) * (1 / (p : ℚ)) := by simp
      _ ≤ (p : ℚ) * (1 / (p : ℚ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hEcard
        · exact (one_div_pos.mpr hpQ).le
      _ = 1 := by field_simp [hpQ.ne']
  have hsplit : ∑ x ∈ block i, w x = (∑ x ∈ E, w x) + w x₀ := by
    dsimp [E]
    exact ((block i).sum_erase_add w hx₀i).symm
  constructor
  · rw [hsplit]
    linarith
  · intro hbeta
    have hEsum : ∑ x ∈ E, w x = 1 := by rw [hsplit] at hbeta; linarith
    have hEcardge : p ≤ E.card := by
      by_contra hbad
      have hcardlt : (E.card : ℚ) < p := by exact_mod_cast (show E.card < p by omega)
      have hstrict : (E.card : ℚ) * (1 / (p : ℚ)) < 1 := by
        calc
          _ < (p : ℚ) * (1 / (p : ℚ)) :=
            mul_lt_mul_of_pos_right hcardlt (one_div_pos.mpr hpQ)
          _ = 1 := by field_simp [hpQ.ne']
      have hupper : ∑ x ∈ E, w x ≤ (E.card : ℚ) * (1 / (p : ℚ)) := by
        calc
          _ ≤ ∑ _x ∈ E, (1 / (p : ℚ)) := by
            apply Finset.sum_le_sum
            intro x _hx
            exact hwle x
          _ = _ := by simp
      linarith
    have hEcardeq : E.card = p := by omega
    have hdefsum : ∑ x ∈ E, ((1 / (p : ℚ)) - w x) = 0 := by
      rw [Finset.sum_sub_distrib]
      simp [hEcardeq, hEsum]
      field_simp [hpQ.ne']
      ring
    have hweq (x : Fin v) (hxE : x ∈ E) : w x = 1 / (p : ℚ) := by
      have hzero : (1 / (p : ℚ)) - w x = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun y (hy : y ∈ E) ↦
          sub_nonneg.mpr (hwle y)).mp hdefsum x hxE
      linarith
    have hcard : (block i).card = p + 1 := by
      dsimp [E] at hEcardeq
      rw [Finset.card_erase_of_mem hx₀i] at hEcardeq
      omega
    refine ⟨hcard, ?_⟩
    intro x hxi
    by_cases hxx₀ : x = x₀
    · simpa [hxx₀] using hx₀
    · have hxE : x ∈ E := by simp [E, hxx₀, hxi]
      have hwe := hweq x hxE
      have hdEq : d x = p := by
        dsimp [w] at hwe
        field_simp [(hdpos x).ne', hpQ.ne'] at hwe
        linarith
      dsimp [d] at hdEq
      have hdegQ : (degree block x : ℚ) = (p : ℚ) + 1 := by linarith
      exact_mod_cast hdegQ

/-- The EFSW projection argument produces a block of size `p + 1` all of
whose points have the minimum degree `p + 1`. -/
lemma exists_minimal_degree_block {p v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hp : 2 ≤ p) (hpb : PairwiseBalanced block)
    (hless : b < v + p) (hmax : ∀ i, (block i).card ≤ p + 1)
    (hmin : ∀ x, p + 1 ≤ degree block x)
    {x₀ : Fin v} (hx₀ : degree block x₀ = p + 1) :
    ∃ i, (block i).card = p + 1 ∧
      ∀ x ∈ block i, degree block x = p + 1 := by
  classical
  let d : Fin v → ℚ := fun x ↦ (degree block x : ℚ) - 1
  let w : Fin v → ℚ := fun x ↦ 1 / d x
  let a : ℚ := 1 / (1 + ∑ x, w x)
  let N : Matrix (Fin v) (Fin b) ℚ := incidenceMatrix block
  let R : Matrix (Fin v) (Fin v) ℚ :=
    fun x y ↦ (if x = y then w x else 0) - a * w x * w y
  let F := ↑(through block x₀)
  let bw : F → ℚ := fun i ↦ ∑ x ∈ block i.1, w x
  let beta : F → ℚ := fun i ↦ 1 - bw i + w x₀
  have hdpos (x : Fin v) : 0 < d x := by
    dsimp [d]
    have hminQ : ((p + 1 : ℕ) : ℚ) ≤ degree block x := by exact_mod_cast hmin x
    have hp2Q : (2 : ℚ) ≤ p := by exact_mod_cast hp
    push_cast at hminQ
    linarith
  have hwpos (x : Fin v) : 0 < w x := by dsimp [w]; exact one_div_pos.mpr (hdpos x)
  have haden : 0 < 1 + ∑ x, w x := by
    have : 0 ≤ ∑ x, w x := Finset.sum_nonneg fun x _hx ↦ (hwpos x).le
    linarith
  have ha : 0 ≤ a := by dsimp [a]; exact (one_div_pos.mpr haden).le
  have hgram (x y : Fin v) :
      (N * N.transpose) x y = (if x = y then d x else 0) + 1 := by
    dsimp only [N]
    rw [incidence_gram_apply hpb]
    by_cases hxy : x = y
    · subst y
      simp only [if_true]
      dsimp [d]
      ring
    · simp [hxy]
  have hR : (N * N.transpose) * R = 1 := by
    ext x z
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp_rw [hgram]
    dsimp only [R]
    exact diag_add_one_mul_inverse d hdpos x z
  have hthrough (i : F) : x₀ ∈ block i.1 := by
    have hi : i.1 ∈ through block x₀ := by exact i.2
    exact mem_through.mp hi
  have hinter (i j : F) :
      ∑ x ∈ block i.1 ∩ block j.1, w x = if i = j then bw i else w x₀ := by
    by_cases hij : i = j
    · subst j
      simp [bw]
    · have hijval : i.1 ≠ j.1 := by
        intro heq
        exact hij (Subtype.ext heq)
      have hxmem : x₀ ∈ block i.1 ∩ block j.1 := by
        exact Finset.mem_inter.mpr ⟨hthrough i, hthrough j⟩
      have hcard := blocks_inter_card_le_one hpb hijval
      have hset : block i.1 ∩ block j.1 = {x₀} := by
        ext x
        constructor
        · intro hx
          have := Finset.card_le_one.mp hcard x hx x₀ hxmem
          simpa using this
        · intro hx
          have hxx₀ : x = x₀ := Finset.mem_singleton.mp hx
          simpa [hxx₀] using hxmem
      simp [hij, hset]
  have hformula :
      (1 - N.transpose * R * N).submatrix (fun i : F ↦ i.1) (fun i : F ↦ i.1) =
        Matrix.diagonal beta + a • Matrix.vecMulVec bw bw -
          Matrix.vecMulVec (fun _ : F ↦ w x₀) (fun _ : F ↦ 1) := by
    ext i j
    have hprod := weighted_incidence_product block w a i.1 j.1
    dsimp only at hprod
    change (N.transpose * R * N) i.1 j.1 = _ at hprod
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Matrix.diagonal_apply]
    rw [hprod, hinter]
    by_cases hij : i = j
    · subst j
      simp [beta, bw]
      ring
    · simp [hij, beta]
      ring
  by_contra hnone
  have hbeta_pos (i : F) : 0 < beta i := by
    have hi := block_weight_defect hp hmin hmax hx₀ (hthrough i)
    dsimp only at hi
    change 0 ≤ beta i ∧
      (beta i = 0 → (block i.1).card = p + 1 ∧
        ∀ x ∈ block i.1, degree block x = p + 1) at hi
    rcases hi with ⟨hinonneg, hizero⟩
    exact lt_of_le_of_ne hinonneg (fun h ↦ hnone ⟨i.1, hizero h.symm⟩)
  have hob := projection_principal_obstruction N R (fun i : F ↦ i.1)
    beta bw a (w x₀) hR hformula hbeta_pos ha
  have hFcard : Fintype.card F = p + 1 := by
    dsimp [F]
    rw [Fintype.card_coe]
    exact hx₀
  simp only [Fintype.card_fin, hFcard] at hob
  omega

lemma block_size_eq_order_add_one_of_min_degree_point
    {p v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hv : v = p ^ 2 + p + 1) (hpb : PairwiseBalanced block)
    (hmax : ∀ i, (block i).card ≤ p + 1)
    {x : Fin v} (hxdeg : degree block x = p + 1)
    {j : Fin b} (hxj : x ∈ block j) : (block j).card = p + 1 := by
  classical
  let T := through block x
  let q : Fin b → ℕ := fun i ↦ (block i).card - 1
  have hjT : j ∈ T := by simpa [T, mem_through] using hxj
  have hTcard : T.card = p + 1 := by exact hxdeg
  have hsum : ∑ i ∈ T, q i = v - 1 := by
    calc
      _ = ∑ i, (if i ∈ T then q i else 0) :=
        (sum_if_mem_eq_sum_nat T q).symm
      _ = ∑ i, (if x ∈ block i then (block i).card - 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [T, mem_through, q]
      _ = v - 1 := partners_sum hpb x
  by_contra hne
  have hjsmall : (block j).card ≤ p := by
    have := hmax j
    omega
  have hqj : q j ≤ p - 1 := by dsimp [q]; omega
  have hp1 : 1 ≤ p := by
    have hjtwo := hpb.1 j
    have hjmax := hmax j
    omega
  have hTerasecard : (T.erase j).card = p := by
    rw [Finset.card_erase_of_mem hjT, hTcard]
    omega
  have hrest : ∑ i ∈ T.erase j, q i ≤ p * p := by
    calc
      _ ≤ ∑ _i ∈ T.erase j, p := by
        apply Finset.sum_le_sum
        intro i _hi
        dsimp [q]
        have := hmax i
        omega
      _ = (T.erase j).card * p := by simp
      _ = p * p := by rw [hTerasecard]
  have hsplit := T.sum_erase_add q hjT
  have hvsub : v - 1 = p * p + p := by rw [hv]; simp [pow_two]
  rw [hvsub] at hsum
  omega

lemma number_of_blocks_eq_points_of_minimal_block
    {p v b : ℕ} {block : Fin b → Finset (Fin v)}
    (hv : v = p ^ 2 + p + 1) (hpb : PairwiseBalanced block)
    (hmax : ∀ i, (block i).card ≤ p + 1)
    {i₀ : Fin b} (hi₀card : (block i₀).card = p + 1)
    (hi₀deg : ∀ x ∈ block i₀, degree block x = p + 1) : b = v := by
  classical
  let M : Finset (Fin b) := Finset.univ.filter fun j ↦ (block i₀ ∩ block j).Nonempty
  have hi₀M : i₀ ∈ M := by
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
    have hnonempty : (block i₀).Nonempty := Finset.card_pos.mp (by rw [hi₀card]; omega)
    simpa using hnonempty
  have hMsize (j : Fin b) (hjM : j ∈ M) : (block j).card = p + 1 := by
    have hne : (block i₀ ∩ block j).Nonempty := (Finset.mem_filter.mp hjM).2
    obtain ⟨x, hx⟩ := hne
    have ⟨hxi₀, hxj⟩ := Finset.mem_inter.mp hx
    exact block_size_eq_order_add_one_of_min_degree_point hv hpb hmax
      (hi₀deg x hxi₀) hxj
  have hintercard (j : Fin b) :
      (block i₀ ∩ block j).card =
        if j = i₀ then p + 1 else if j ∈ M then 1 else 0 := by
    by_cases hji : j = i₀
    · subst j
      simp [hi₀card, hi₀M]
    · have hle := blocks_inter_card_le_one hpb (Ne.symm hji)
      by_cases hjM : j ∈ M
      · have hpos : 0 < (block i₀ ∩ block j).card :=
          Finset.card_pos.mpr (Finset.mem_filter.mp hjM).2
        simp [hji, hjM]
        omega
      · have hempty : ¬(block i₀ ∩ block j).Nonempty := by
          intro hn
          exact hjM (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩)
        have hzero : (block i₀ ∩ block j).card = 0 := by
          rw [Finset.card_eq_zero]
          exact Finset.not_nonempty_iff_eq_empty.mp hempty
        simp [hji, hjM, hzero]
  have hsuminter : ∑ j, (block i₀ ∩ block j).card = (p + 1) * (p + 1) := by
    rw [← sum_degrees_on_block i₀]
    calc
      _ = ∑ _x ∈ block i₀, (p + 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hi₀deg x hx
      _ = _ := by simp [hi₀card]
  have hMcard : M.card = v := by
    have hsumform : ∑ j, (block i₀ ∩ block j).card = M.card + p := by
      calc
        _ = ∑ j, (if j = i₀ then p + 1 else if j ∈ M then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact hintercard j
        _ = (p + 1) + ∑ j ∈ (Finset.univ : Finset (Fin b)).erase i₀,
              (if j ∈ M then 1 else 0) := by
          have herase :
              ∑ j ∈ (Finset.univ : Finset (Fin b)).erase i₀,
                  (if j = i₀ then p + 1 else if j ∈ M then 1 else 0) =
                ∑ j ∈ (Finset.univ : Finset (Fin b)).erase i₀,
                  (if j ∈ M then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [(Finset.mem_erase.mp hj).1]
          calc
            _ = (∑ j ∈ (Finset.univ : Finset (Fin b)).erase i₀,
                  (if j = i₀ then p + 1 else if j ∈ M then 1 else 0)) + (p + 1) := by
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
              simp
            _ = _ := by rw [herase]; omega
        _ = (p + 1) + (M.erase i₀).card := by
          congr 1
          have hfilter : ((Finset.univ : Finset (Fin b)).erase i₀).filter
              (fun j ↦ j ∈ M) = M.erase i₀ := by
            ext j
            simp [and_comm]
          simpa [Finset.sum_boole, hfilter]
        _ = M.card + p := by
          rw [Finset.card_erase_of_mem hi₀M]
          have hMpos : 0 < M.card := Finset.card_pos.mpr ⟨i₀, hi₀M⟩
          omega
    rw [hsuminter] at hsumform
    simp only [pow_two] at hv
    nlinarith [hsumform]
  have hMsum : ∑ j ∈ M, (block j).card * ((block j).card - 1) = v * (v - 1) := by
    calc
      _ = ∑ _j ∈ M, (p + 1) * p := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hMsize j hj]
        have : p + 1 - 1 = p := by omega
        rw [this]
      _ = M.card * ((p + 1) * p) := by simp
      _ = v * (v - 1) := by rw [hMcard, hv]; simp [pow_two]; ring
  have hall := global_ordered_pair_count hpb
  have hcomp : ∑ j ∈ (Finset.univ : Finset (Fin b)) \ M,
      (block j).card * ((block j).card - 1) = 0 := by
    have hsplit := Finset.sum_sdiff (f := fun j ↦
      (block j).card * ((block j).card - 1)) (Finset.subset_univ M)
    rw [hMsum, hall] at hsplit
    omega
  have hMfull : M = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hjM
    have hjdiff : j ∈ (Finset.univ : Finset (Fin b)) \ M := by simp [hjM]
    have hjzero : (block j).card * ((block j).card - 1) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun k (_hk : k ∈
        (Finset.univ : Finset (Fin b)) \ M) ↦ Nat.zero_le _).mp hcomp j hjdiff
    have hjtwo := hpb.1 j
    have hjpos : 0 < (block j).card * ((block j).card - 1) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  rw [hMfull, Finset.card_univ, Fintype.card_fin] at hMcard
  exact hMcard

/-- Erdős Problem 903, in the slightly stronger form proved by
Erdős--Fowler--Sós--Wilson: primality of `p` is not needed. -/
theorem erdos_903_general (p b : ℕ)
    (block : Fin b → Finset (Fin (p ^ 2 + p + 1))) (hp : 2 ≤ p)
    (hpb : PairwiseBalanced block) (hmore : p ^ 2 + p + 1 < b) :
    p ^ 2 + p + 1 + p ≤ b := by
  by_contra hbad
  have hless : b < (p ^ 2 + p + 1) + p := by omega
  have hmax : ∀ i, (block i).card ≤ p + 1 :=
    block_card_le_order_add_one hp rfl hpb hmore hless
  have hmin : ∀ x, p + 1 ≤ degree block x :=
    degree_ge_order_add_one hp rfl hpb hmax
  obtain ⟨x₀, hx₀⟩ := exists_degree_eq_order_add_one hp rfl hpb hmore hless hmax
  obtain ⟨i₀, hi₀card, hi₀deg⟩ :=
    exists_minimal_degree_block hp hpb hless hmax hmin hx₀
  have hb := number_of_blocks_eq_points_of_minimal_block rfl hpb hmax hi₀card hi₀deg
  omega

/-- The resolution of Erdős Problem 903 for a prime power `p`.  The family
is indexed, so `b` is exactly the number `t` of blocks. -/
theorem erdos_903 (p b : ℕ) (hp : IsPrimePow p)
    (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (hpb : PairwiseBalanced block) (hmore : p ^ 2 + p + 1 < b) :
    p ^ 2 + p + 1 + p ≤ b :=
  erdos_903_general p b block (IsPrimePow.two_le hp) hpb hmore

end Erdos903

#print axioms Erdos903.erdos_903
