import ErdosProblems.Erdos783.PrimeKernel

open MeasureTheory Set Finset Filter
open scoped BigOperators Topology

namespace Erdos783

noncomputable section

variable {α : Type*} [DecidableEq α]

def atomMass (A : Finset α) (w : α → ℝ) : ℝ :=
  ∑ a ∈ A, w a

def atomMoment (A : Finset α) (w x : α → ℝ) : ℕ → ℝ → ℝ
  | 0, _u => 1
  | n + 1, u =>
      ∑ a ∈ A, if x a ≤ u then w a * atomMoment A w x n (u - x a) else 0

def distinctAtomMoment (w x : α → ℝ) : Finset α → ℕ → ℝ → ℝ
  | _A, 0, _u => 1
  | A, n + 1, u =>
      ∑ a ∈ A,
        if x a ≤ u then
          w a * distinctAtomMoment w x (A.erase a) n (u - x a)
        else 0

@[simp] lemma atomMoment_zero (A : Finset α) (w x : α → ℝ) (u : ℝ) :
    atomMoment A w x 0 u = 1 := rfl

@[simp] lemma distinctAtomMoment_zero (A : Finset α) (w x : α → ℝ) (u : ℝ) :
    distinctAtomMoment w x A 0 u = 1 := rfl

lemma atomMass_nonneg {A : Finset α} {w : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) : 0 ≤ atomMass A w := by
  unfold atomMass
  exact Finset.sum_nonneg hw

lemma atomMass_mono {A B : Finset α} {w : α → ℝ}
    (hAB : A ⊆ B) (hw : ∀ a ∈ B, 0 ≤ w a) :
    atomMass A w ≤ atomMass B w := by
  unfold atomMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB
    (fun a haB _haA ↦ hw a haB)

lemma atomMoment_nonneg {A : Finset α} {w x : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) (n : ℕ) (u : ℝ) :
    0 ≤ atomMoment A w x n u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment]
      apply Finset.sum_nonneg
      intro a ha
      split_ifs
      · exact mul_nonneg (hw a ha) (ih _)
      · exact le_rfl

lemma distinctAtomMoment_nonneg {A : Finset α} {w x : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) (n : ℕ) (u : ℝ) :
    0 ≤ distinctAtomMoment w x A n u := by
  induction n generalizing A u with
  | zero => simp
  | succ n ih =>
      rw [distinctAtomMoment]
      apply Finset.sum_nonneg
      intro a ha
      split_ifs
      · exact mul_nonneg (hw a ha)
          (ih (fun b hb ↦ hw b (Finset.mem_of_mem_erase hb)) _)
      · exact le_rfl

lemma atomMoment_mono_endpoint {A : Finset α} {w x : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) (hx : ∀ a ∈ A, 0 ≤ x a)
    (n : ℕ) : Monotone (atomMoment A w x n) := by
  induction n with
  | zero => exact monotone_const
  | succ n ih =>
      intro u v huv
      rw [atomMoment, atomMoment]
      apply Finset.sum_le_sum
      intro a ha
      by_cases hau : x a ≤ u
      · have hav : x a ≤ v := hau.trans huv
        rw [if_pos hau, if_pos hav]
        exact mul_le_mul_of_nonneg_left (ih (sub_le_sub_right huv _)) (hw a ha)
      · rw [if_neg hau]
        split_ifs
        · exact mul_nonneg (hw a ha) (atomMoment_nonneg hw _ _)
        · exact le_rfl

lemma atomMoment_le_mass_pow {A : Finset α} {w x : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) (n : ℕ) (u : ℝ) :
    atomMoment A w x n u ≤ atomMass A w ^ n := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, pow_succ']
      calc
        (∑ a ∈ A, if x a ≤ u then
            w a * atomMoment A w x n (u - x a) else 0) ≤
            ∑ a ∈ A, w a * atomMass A w ^ n := by
          apply Finset.sum_le_sum
          intro a ha
          split_ifs
          · exact mul_le_mul_of_nonneg_left (ih _) (hw a ha)
          · exact mul_nonneg (hw a ha) (pow_nonneg (atomMass_nonneg hw) n)
        _ = atomMass A w ^ n * atomMass A w := by
          rw [atomMass, ← Finset.sum_mul]
          ring
        _ = atomMass A w * atomMass A w ^ n := by ring

lemma atomMoment_mono_finset {A B : Finset α} {w x : α → ℝ}
    (hAB : A ⊆ B) (hw : ∀ a ∈ B, 0 ≤ w a) (n : ℕ) (u : ℝ) :
    atomMoment A w x n u ≤ atomMoment B w x n u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, atomMoment]
      calc
        (∑ a ∈ A, if x a ≤ u then
            w a * atomMoment A w x n (u - x a) else 0) ≤
            ∑ a ∈ A, if x a ≤ u then
              w a * atomMoment B w x n (u - x a) else 0 := by
          apply Finset.sum_le_sum
          intro a haA
          split_ifs
          · exact mul_le_mul_of_nonneg_left (ih _) (hw a (hAB haA))
          · exact le_rfl
        _ ≤ ∑ a ∈ B, if x a ≤ u then
              w a * atomMoment B w x n (u - x a) else 0 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hAB
          intro a haB _haA
          split_ifs
          · exact mul_nonneg (hw a haB) (atomMoment_nonneg hw _ _)
          · exact le_rfl

lemma distinctAtomMoment_le_atomMoment {A : Finset α} {w x : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) (n : ℕ) (u : ℝ) :
    distinctAtomMoment w x A n u ≤ atomMoment A w x n u := by
  induction n generalizing A u with
  | zero => simp
  | succ n ih =>
      rw [distinctAtomMoment, atomMoment]
      apply Finset.sum_le_sum
      intro a ha
      split_ifs
      · apply mul_le_mul_of_nonneg_left _ (hw a ha)
        exact (ih (fun b hb ↦ hw b (Finset.mem_of_mem_erase hb)) _).trans
          (atomMoment_mono_finset (Finset.erase_subset _ _) hw _ _)
      · exact le_rfl

lemma atomMoment_erase_sub_le
    {A : Finset α} {w x : α → ℝ} {p : α}
    (hp : p ∈ A) (hw : ∀ a ∈ A, 0 ≤ w a)
    {M : ℝ} (hM1 : 1 ≤ M) (hmass : atomMass A w ≤ M)
    (n : ℕ) (u : ℝ) :
    atomMoment A w x n u - atomMoment (A.erase p) w x n u ≤
      (n : ℝ) * w p * M ^ n := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hwp : 0 ≤ w p := hw p hp
  have hwErase : ∀ a ∈ A.erase p, 0 ≤ w a :=
    fun a ha ↦ hw a (Finset.mem_of_mem_erase ha)
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      let B := A.erase p
      let fA : α → ℝ := fun a ↦
        if x a ≤ u then w a * atomMoment A w x n (u - x a) else 0
      let fB : α → ℝ := fun a ↦
        if x a ≤ u then w a * atomMoment B w x n (u - x a) else 0
      have hrewrite :
          atomMoment A w x (n + 1) u - atomMoment B w x (n + 1) u =
            fA p + ∑ a ∈ B, (fA a - fB a) := by
        rw [atomMoment, atomMoment]
        change (∑ a ∈ A, fA a) - ∑ a ∈ B, fB a = _
        have hsum := Finset.sum_erase_add A fA hp
        dsimp only [B]
        calc
          (∑ a ∈ A, fA a) - ∑ a ∈ A.erase p, fB a =
              ((∑ a ∈ A.erase p, fA a) + fA p) -
                ∑ a ∈ A.erase p, fB a := by rw [hsum]
          _ = fA p + ∑ a ∈ A.erase p, (fA a - fB a) := by
            rw [Finset.sum_sub_distrib]
            ring
      have hfp : fA p ≤ w p * M ^ (n + 1) := by
        dsimp only [fA]
        split_ifs
        · calc
            w p * atomMoment A w x n (u - x p) ≤
                w p * atomMass A w ^ n :=
              mul_le_mul_of_nonneg_left (atomMoment_le_mass_pow hw n _) hwp
            _ ≤ w p * M ^ n := by
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (atomMass_nonneg hw) hmass n) hwp
            _ ≤ w p * M ^ (n + 1) := by
              apply mul_le_mul_of_nonneg_left _ hwp
              rw [pow_succ]
              nlinarith [pow_nonneg hM0 n]
        · exact mul_nonneg hwp (pow_nonneg hM0 _)
      have hterm : ∀ a ∈ B,
          fA a - fB a ≤ w a * ((n : ℝ) * w p * M ^ n) := by
        intro a ha
        dsimp only [fA, fB]
        by_cases hau : x a ≤ u
        · rw [if_pos hau, if_pos hau, ← mul_sub]
          exact mul_le_mul_of_nonneg_left (ih _) (hwErase a ha)
        · simp only [tsub_le_iff_right]
          exact mul_nonneg (hwErase a ha) (by positivity)
      rw [hrewrite]
      calc
        fA p + ∑ a ∈ B, (fA a - fB a) ≤
            w p * M ^ (n + 1) +
              ∑ a ∈ B, w a * ((n : ℝ) * w p * M ^ n) := by
          exact add_le_add hfp (Finset.sum_le_sum hterm)
        _ = w p * M ^ (n + 1) +
              atomMass B w * ((n : ℝ) * w p * M ^ n) := by
          rw [atomMass, Finset.sum_mul]
        _ ≤ w p * M ^ (n + 1) +
              M * ((n : ℝ) * w p * M ^ n) := by
          have hcoef : 0 ≤ (n : ℝ) * w p * M ^ n := by positivity
          have hmassB : atomMass B w ≤ M := by
            dsimp only [B]
            exact (atomMass_mono (Finset.erase_subset p A) hw).trans hmass
          have hmul := mul_le_mul_of_nonneg_right
            hmassB hcoef
          exact add_le_add le_rfl hmul
        _ = ((n + 1 : ℕ) : ℝ) * w p * M ^ (n + 1) := by
          push_cast
          rw [pow_succ]
          ring

lemma atomMoment_sub_distinct_le
    {A : Finset α} {w x : α → ℝ}
    (hw0 : ∀ a ∈ A, 0 ≤ w a) {delta M : ℝ}
    (hdelta : 0 ≤ delta) (hwdelta : ∀ a ∈ A, w a ≤ delta)
    (hM1 : 1 ≤ M) (hmass : atomMass A w ≤ M)
    (n : ℕ) (u : ℝ) :
    atomMoment A w x n u - distinctAtomMoment w x A n u ≤
      (n : ℝ) ^ 2 * delta * M ^ n := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  induction n generalizing A u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, distinctAtomMoment, ← Finset.sum_sub_distrib]
      let Q : ℝ := ((n : ℝ) ^ 2 + n) * delta * M ^ n
      have hterm : ∀ a ∈ A,
          (if x a ≤ u then w a * atomMoment A w x n (u - x a) else 0) -
            (if x a ≤ u then
              w a * distinctAtomMoment w x (A.erase a) n (u - x a) else 0) ≤
            w a * Q := by
        intro a ha
        by_cases hau : x a ≤ u
        · rw [if_pos hau, if_pos hau, ← mul_sub]
          have hwErase : ∀ b ∈ A.erase a, 0 ≤ w b :=
            fun b hb ↦ hw0 b (Finset.mem_of_mem_erase hb)
          have hwdeltaErase : ∀ b ∈ A.erase a, w b ≤ delta :=
            fun b hb ↦ hwdelta b (Finset.mem_of_mem_erase hb)
          have hmassErase : atomMass (A.erase a) w ≤ M :=
            (atomMass_mono (Finset.erase_subset a A) hw0).trans hmass
          have hremove := atomMoment_erase_sub_le (x := x) ha hw0
            hM1 hmass n (u - x a)
          have hcollision := ih hwErase hwdeltaErase hmassErase (u - x a)
          have hremove' : (n : ℝ) * w a * M ^ n ≤
              (n : ℝ) * delta * M ^ n := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hwdelta a ha) (by positivity))
              (pow_nonneg hM0 n)
          have hinner :
              atomMoment A w x n (u - x a) -
                  distinctAtomMoment w x (A.erase a) n (u - x a) ≤ Q := by
            dsimp only [Q]
            have hid :
                atomMoment A w x n (u - x a) -
                    distinctAtomMoment w x (A.erase a) n (u - x a) =
                  (atomMoment A w x n (u - x a) -
                    atomMoment (A.erase a) w x n (u - x a)) +
                  (atomMoment (A.erase a) w x n (u - x a) -
                    distinctAtomMoment w x (A.erase a) n (u - x a)) := by ring
            rw [hid]
            calc
              _ ≤ (n : ℝ) * delta * M ^ n +
                    (n : ℝ) ^ 2 * delta * M ^ n :=
                add_le_add (hremove.trans hremove') hcollision
              _ = ((n : ℝ) ^ 2 + n) * delta * M ^ n := by ring
          exact mul_le_mul_of_nonneg_left hinner (hw0 a ha)
        · simp only [tsub_le_iff_right]
          exact mul_nonneg (hw0 a ha) (by
            dsimp only [Q]
            positivity)
      calc
        (∑ a ∈ A,
            ((if x a ≤ u then w a * atomMoment A w x n (u - x a) else 0) -
              (if x a ≤ u then
                w a * distinctAtomMoment w x (A.erase a) n (u - x a) else 0))) ≤
            ∑ a ∈ A, w a * Q := Finset.sum_le_sum hterm
        _ = atomMass A w * Q := by rw [atomMass, Finset.sum_mul]
        _ ≤ M * Q := by
          apply mul_le_mul_of_nonneg_right hmass
          dsimp only [Q]
          positivity
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * delta * M ^ (n + 1) := by
          dsimp only [Q]
          push_cast
          have hpoly : (n : ℝ) ^ 2 + n ≤ ((n : ℝ) + 1) ^ 2 := by
            nlinarith
          calc
            M * (((n : ℝ) ^ 2 + n) * delta * M ^ n) =
                ((n : ℝ) ^ 2 + n) * (delta * M ^ (n + 1)) := by
              rw [pow_succ]
              ring
            _ ≤ ((n : ℝ) + 1) ^ 2 * (delta * M ^ (n + 1)) :=
              mul_le_mul_of_nonneg_right hpoly
                (mul_nonneg hdelta (pow_nonneg hM0 _))
            _ = ((n : ℝ) + 1) ^ 2 * delta * M ^ (n + 1) := by ring

end

end Erdos783
