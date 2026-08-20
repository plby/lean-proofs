import ErdosProblems.Erdos783.PrimeAtomMoment

open MeasureTheory Set Finset Filter
open scoped BigOperators Topology

namespace Erdos783

noncomputable section

variable {α : Type*} [DecidableEq α]

lemma sum_powersetCard_erase_insert
    (A : Finset α) (a : α) (ha : a ∈ A) (n : ℕ) (g : Finset α → ℝ) :
    ∑ S ∈ (A.erase a).powersetCard n, g (insert a S) =
      ∑ T ∈ A.powersetCard (n + 1), if a ∈ T then g T else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun S _hS ↦ insert a S)
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    have hSa : a ∉ S := fun h ↦ by simpa using hS.1 h
    exact ⟨⟨by
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ha
      · exact Finset.mem_of_mem_erase (hS.1 hb), by simp [hSa, hS.2]⟩, by simp⟩
  · intro S₁ hS₁ S₂ hS₂ heq
    have hS₁a : a ∉ S₁ := by
      rw [Finset.mem_powersetCard] at hS₁
      exact fun h ↦ by simpa using hS₁.1 h
    have hS₂a : a ∉ S₂ := by
      rw [Finset.mem_powersetCard] at hS₂
      exact fun h ↦ by simpa using hS₂.1 h
    simpa [hS₁a, hS₂a] using congrArg (Finset.erase · a) heq
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    refine ⟨T.erase a, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      constructor
      · intro b hb
        rw [Finset.mem_erase] at hb
        exact Finset.mem_erase.mpr ⟨hb.1, hT.1.1 hb.2⟩
      · rw [Finset.card_erase_of_mem hT.2]
        omega
    · exact Finset.insert_erase hT.2
  · intro S hS
    rfl

lemma sum_insert_over_powersetCard
    (A : Finset α) (n : ℕ) (g : Finset α → ℝ) :
    ∑ a ∈ A, ∑ S ∈ (A.erase a).powersetCard n, g (insert a S) =
      ((n + 1 : ℕ) : ℝ) * ∑ T ∈ A.powersetCard (n + 1), g T := by
  calc
    _ = ∑ a ∈ A, ∑ T ∈ A.powersetCard (n + 1),
          if a ∈ T then g T else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_powersetCard_erase_insert A a ha n g
    _ = ∑ T ∈ A.powersetCard (n + 1), ∑ a ∈ A,
          if a ∈ T then g T else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ T ∈ A.powersetCard (n + 1), ((n + 1 : ℕ) : ℝ) * g T := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      rw [← Finset.sum_filter]
      have hfilter : A.filter (fun a ↦ a ∈ T) = T := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · exact fun h ↦ h.2
        · exact fun h ↦ ⟨hT.1 h, h⟩
      rw [hfilter, Finset.sum_const, hT.2, nsmul_eq_mul]
    _ = _ := by
      rw [Finset.mul_sum]

def atomSubsetMoment (A : Finset α) (w x : α → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ S ∈ A.powersetCard n,
    if n = 0 ∨ (∑ a ∈ S, x a) ≤ u then ∏ a ∈ S, w a else 0

@[simp] lemma atomSubsetMoment_zero (A : Finset α) (w x : α → ℝ) (u : ℝ) :
    atomSubsetMoment A w x 0 u = 1 := by
  simp [atomSubsetMoment]

lemma distinctAtomMoment_eq_factorial_mul_subset
    {A : Finset α} {w x : α → ℝ}
    (hx : ∀ a ∈ A, 0 ≤ x a) (n : ℕ) (u : ℝ) :
    distinctAtomMoment w x A n u =
      (n.factorial : ℝ) * atomSubsetMoment A w x n u := by
  induction n generalizing A u with
  | zero =>
      rw [distinctAtomMoment_zero, atomSubsetMoment_zero]
      simp
  | succ n ih =>
      rw [distinctAtomMoment]
      simp_rw [ih (fun b hb ↦ hx b (Finset.mem_of_mem_erase hb))]
      let g : Finset α → ℝ := fun T ↦
        if (∑ b ∈ T, x b) ≤ u then ∏ b ∈ T, w b else 0
      have hterm : ∀ a ∈ A,
          (if x a ≤ u then
              w a * ((n.factorial : ℝ) *
                atomSubsetMoment (A.erase a) w x n (u - x a))
            else 0) =
            (n.factorial : ℝ) *
              ∑ S ∈ (A.erase a).powersetCard n, g (insert a S) := by
        intro a ha
        unfold atomSubsetMoment
        by_cases hau : x a ≤ u
        · rw [if_pos hau]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.mem_powersetCard] at hS
          have haS : a ∉ S := fun h ↦ by simpa using hS.1 h
          dsimp only [g]
          rw [Finset.sum_insert haS, Finset.prod_insert haS]
          by_cases hn : n = 0
          · subst n
            have hSempty : S = ∅ := Finset.card_eq_zero.mp hS.2
            subst S
            simp [hau]
          · simp only [hn, false_or]
            by_cases hSu : (∑ b ∈ S, x b) ≤ u - x a
            · rw [if_pos hSu, if_pos (by linarith)]
              ring
            · rw [if_neg hSu, if_neg (by linarith)]
              ring
        · rw [if_neg hau]
          symm
          apply mul_eq_zero_of_right
          apply Finset.sum_eq_zero
          intro S hS
          rw [Finset.mem_powersetCard] at hS
          have haS : a ∉ S := fun h ↦ by simpa using hS.1 h
          have hxS : 0 ≤ ∑ b ∈ S, x b := by
            apply Finset.sum_nonneg
            intro b hb
            exact hx b (Finset.mem_of_mem_erase (hS.1 hb))
          dsimp only [g]
          rw [Finset.sum_insert haS, if_neg (by linarith)]
      calc
        (∑ a ∈ A,
            if x a ≤ u then
              w a * ((n.factorial : ℝ) *
                atomSubsetMoment (A.erase a) w x n (u - x a))
            else 0) =
            ∑ a ∈ A, (n.factorial : ℝ) *
              ∑ S ∈ (A.erase a).powersetCard n, g (insert a S) := by
          exact Finset.sum_congr rfl hterm
        _ = (n.factorial : ℝ) *
              (∑ a ∈ A, ∑ S ∈ (A.erase a).powersetCard n,
                g (insert a S)) := by
          rw [Finset.mul_sum]
        _ = (n.factorial : ℝ) * (((n + 1 : ℕ) : ℝ) *
              ∑ T ∈ A.powersetCard (n + 1), g T) := by
          rw [sum_insert_over_powersetCard]
        _ = (((n + 1).factorial : ℕ) : ℝ) *
              atomSubsetMoment A w x (n + 1) u := by
          rw [Nat.factorial_succ]
          push_cast
          unfold atomSubsetMoment
          dsimp only [g]
          simp only [Nat.succ_ne_zero, false_or]
          ring

lemma sum_log_div_eq_log_subsetProduct_div
    {S : Finset ℕ} (hpos : ∀ p ∈ S, 0 < p) {y : ℕ} :
    (∑ p ∈ S, Real.log p / Real.log y) =
      Real.log (subsetProduct S) / Real.log y := by
  rw [← Finset.sum_div]
  congr 1
  rw [← Real.log_prod]
  · congr 1
    exact (cast_subsetProduct S).symm
  · intro p hp
    exact_mod_cast (hpos p hp).ne'

lemma sum_primeLogDiv_le_iff_subsetProduct_le
    {P S : Finset ℕ} (hSP : S ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    {y N : ℕ} (hy : 2 ≤ y) (hN : 0 < N) :
    (∑ p ∈ S, Real.log p / Real.log y) ≤
        Real.log N / Real.log y ↔
      subsetProduct S ≤ N := by
  have hpos : ∀ p ∈ S, 0 < p := fun p hp ↦ (hP p (hSP hp)).pos
  have hprod : 0 < subsetProduct S := subsetProduct_pos hSP
    (fun p hp ↦ (hP p hp).pos)
  have hylog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy)
  have hprodR : (subsetProduct S : ℝ) ∈ Set.Ioi 0 := by
    change 0 < (subsetProduct S : ℝ)
    exact_mod_cast hprod
  have hNR : (N : ℝ) ∈ Set.Ioi 0 := by
    change 0 < (N : ℝ)
    exact_mod_cast hN
  rw [sum_log_div_eq_log_subsetProduct_div hpos,
    div_le_div_iff_of_pos_right hylog]
  rw [Real.strictMonoOn_log.le_iff_le hprodR hNR]
  norm_cast

lemma atomSubsetMoment_primeLogDiv_eq_cutoff
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y N j : ℕ} (hy : 2 ≤ y) (hN : 0 < N) :
    atomSubsetMoment P (fun p : ℕ ↦ (p : ℝ)⁻¹)
        (fun p : ℕ ↦ Real.log p / Real.log y) j
        (Real.log N / Real.log y) =
      cutoffElementaryReciprocalMass N P j := by
  unfold atomSubsetMoment cutoffElementaryReciprocalMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mem_powersetCard] at hS
  have hcut := sum_primeLogDiv_le_iff_subsetProduct_le hS.1 hP hy hN
  by_cases hj : j = 0
  · subst j
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hS.2
    subst S
    have h1N : 1 ≤ N := hN
    simp [subsetProduct, h1N]
  · simp only [hj, false_or]
    rw [if_congr hcut]
    · exact (inv_cast_subsetProduct S).symm
    · rfl

lemma atomMoment_mono_location
    {A : Finset α} {w x y : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) (hx : ∀ a ∈ A, 0 ≤ x a)
    (hxy : ∀ a ∈ A, x a ≤ y a) (n : ℕ) (u : ℝ) :
    atomMoment A w y n u ≤ atomMoment A w x n u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, atomMoment]
      apply Finset.sum_le_sum
      intro a ha
      by_cases hyu : y a ≤ u
      · have hxu : x a ≤ u := (hxy a ha).trans hyu
        rw [if_pos hyu, if_pos hxu]
        apply mul_le_mul_of_nonneg_left _ (hw a ha)
        have hfirst := ih (u - y a)
        have hmono := atomMoment_mono_endpoint hw hx n
          (show u - y a ≤ u - x a by linarith [hxy a ha])
        exact hfirst.trans hmono
      · rw [if_neg hyu]
        split_ifs
        · exact mul_nonneg (hw a ha) (atomMoment_nonneg hw n _)
        · exact le_rfl

lemma atomMoment_bij
    {β : Type*} [DecidableEq β]
    {A : Finset α} {B : Finset β} (f : α → β)
    (hf : ∀ a ∈ A, f a ∈ B)
    (hinj : ∀ a₁ ∈ A, ∀ a₂ ∈ A, f a₁ = f a₂ → a₁ = a₂)
    (hsurj : ∀ b ∈ B, ∃ a ∈ A, f a = b)
    {wA xA : α → ℝ} {wB xB : β → ℝ}
    (hw : ∀ a ∈ A, wA a = wB (f a))
    (hx : ∀ a ∈ A, xA a = xB (f a))
    (n : ℕ) (u : ℝ) :
    atomMoment A wA xA n u = atomMoment B wB xB n u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, atomMoment]
      apply Finset.sum_bij (fun a _ha ↦ f a)
      · exact hf
      · exact hinj
      · intro b hb
        obtain ⟨a, ha, hab⟩ := hsurj b hb
        exact ⟨a, ha, hab⟩
      · intro a ha
        rw [hw a ha, hx a ha]
        split_ifs
        · rw [ih]
        · rfl

def atomIntervalMass (A : Finset α) (w x : α → ℝ) (v delta : ℝ) : ℝ :=
  ∑ a ∈ A, if v < x a ∧ x a ≤ v + delta then w a else 0

lemma atomMoment_endpoint_increment_le
    {A : Finset α} {w x : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) {delta B M : ℝ}
    (hdelta : 0 ≤ delta) (hB : 0 ≤ B)
    (hinterval : ∀ v : ℝ, atomIntervalMass A w x v delta ≤ B)
    (hM : atomMass A w ≤ M) (hM1 : 1 ≤ M)
    (n : ℕ) (u : ℝ) :
    atomMoment A w x n (u + delta) - atomMoment A w x n u ≤
      (n : ℝ) * B * M ^ (n - 1) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, atomMoment, ← Finset.sum_sub_distrib]
      let D : ℝ := (n : ℝ) * B * M ^ (n - 1)
      let E : α → ℝ := fun a ↦
        if u < x a ∧ x a ≤ u + delta then w a * M ^ n else 0
      have hterm : ∀ a ∈ A,
          (if x a ≤ u + delta then
              w a * atomMoment A w x n (u + delta - x a) else 0) -
            (if x a ≤ u then w a * atomMoment A w x n (u - x a) else 0) ≤
          w a * D + E a := by
        intro a ha
        by_cases hau : x a ≤ u
        · have hauδ : x a ≤ u + delta := hau.trans (le_add_of_nonneg_right hdelta)
          rw [if_pos hau, if_pos hauδ, ← mul_sub]
          have harg : u + delta - x a = (u - x a) + delta := by ring
          rw [harg]
          have hd := ih (u - x a)
          have hnot : ¬(u < x a ∧ x a ≤ u + delta) := fun h ↦
            (not_lt_of_ge hau) h.1
          dsimp only [E]
          rw [if_neg hnot]
          simpa only [D, add_zero] using
            (mul_le_mul_of_nonneg_left hd (hw a ha))
        · have hua : u < x a := lt_of_not_ge hau
          rw [if_neg hau]
          by_cases hauδ : x a ≤ u + delta
          · rw [if_pos hauδ]
            have hmoment := atomMoment_le_mass_pow (x := x) hw n (u + delta - x a)
            have hmasspow : atomMass A w ^ n ≤ M ^ n :=
              pow_le_pow_left₀ (atomMass_nonneg hw) hM n
            have hbound : atomMoment A w x n (u + delta - x a) ≤ M ^ n :=
              hmoment.trans hmasspow
            dsimp only [E]
            rw [if_pos ⟨hua, hauδ⟩]
            have hD0 : 0 ≤ D := by
              dsimp only [D]
              positivity
            rw [sub_zero]
            calc
              w a * atomMoment A w x n (u + delta - x a) ≤
                  w a * M ^ n := mul_le_mul_of_nonneg_left hbound (hw a ha)
              _ ≤ w a * D + w a * M ^ n :=
                le_add_of_nonneg_left (mul_nonneg (hw a ha) hD0)
          · rw [if_neg hauδ]
            dsimp only [E]
            rw [if_neg (fun h ↦ hauδ h.2)]
            have hD0 : 0 ≤ D := by
              dsimp only [D]
              positivity
            simpa using add_nonneg (mul_nonneg (hw a ha) hD0) le_rfl
      calc
        (∑ a ∈ A,
            ((if x a ≤ u + delta then
                w a * atomMoment A w x n (u + delta - x a) else 0) -
              (if x a ≤ u then
                w a * atomMoment A w x n (u - x a) else 0))) ≤
            ∑ a ∈ A, (w a * D + E a) := Finset.sum_le_sum hterm
        _ = atomMass A w * D + atomIntervalMass A w x u delta * M ^ n := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [atomMass, Finset.sum_mul]
          · unfold atomIntervalMass E
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a ha
            split_ifs <;> ring
        _ ≤ M * D + B * M ^ n := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hM (by
              dsimp only [D]
              positivity))
            (mul_le_mul_of_nonneg_right (hinterval u) (pow_nonneg hM0 n))
        _ ≤ (((n + 1 : ℕ) : ℝ) * B * M ^ ((n + 1) - 1)) := by
          dsimp only [D]
          push_cast
          by_cases hn : n = 0
          · subst n
            norm_num
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            have hpow : M ^ n = M * M ^ (n - 1) := by
              rw [← pow_succ']
              congr
              omega
            rw [hpow]
            apply le_of_eq
            ring

lemma atomMoment_location_shift_le
    {A : Finset α} {w x y : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a)
    (hx : ∀ a ∈ A, 0 ≤ x a) (hy : ∀ a ∈ A, 0 ≤ y a)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hxy : ∀ a ∈ A, y a ≤ x a + delta)
    (n : ℕ) (u : ℝ) :
    atomMoment A w x n u ≤ atomMoment A w y n (u + n * delta) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, atomMoment]
      apply Finset.sum_le_sum
      intro a ha
      by_cases hxu : x a ≤ u
      · have hyu : y a ≤ u + ((n + 1 : ℕ) : ℝ) * delta := by
          push_cast
          have := hxy a ha
          nlinarith
        rw [if_pos hxu, if_pos hyu]
        apply mul_le_mul_of_nonneg_left _ (hw a ha)
        have hfirst := ih (u - x a)
        have hendpoint :
            (u - x a) + (n : ℝ) * delta ≤
              u + ((n + 1 : ℕ) : ℝ) * delta - y a := by
          push_cast
          nlinarith [hxy a ha]
        exact hfirst.trans
          (atomMoment_mono_endpoint hw hy n hendpoint)
      · rw [if_neg hxu]
        split_ifs
        · exact mul_nonneg (hw a ha) (atomMoment_nonneg hw n _)
        · exact le_rfl

lemma atomIntervalMass_location_shift_le
    {A : Finset α} {w x y : α → ℝ}
    (hw : ∀ a ∈ A, 0 ≤ w a) {shift delta : ℝ}
    (hxy : ∀ a ∈ A, x a ≤ y a)
    (hyx : ∀ a ∈ A, y a ≤ x a + shift)
    (v : ℝ) :
    atomIntervalMass A w y v delta ≤
      atomIntervalMass A w x (v - shift) (delta + shift) := by
  unfold atomIntervalMass
  apply Finset.sum_le_sum
  intro a ha
  by_cases hay : v < y a ∧ y a ≤ v + delta
  · rw [if_pos hay, if_pos]
    constructor
    · nlinarith [hyx a ha]
    · nlinarith [hxy a ha]
  · rw [if_neg hay]
    split_ifs
    · exact hw a ha
    · exact le_rfl

lemma atomMoment_const_mul_weight
    (A : Finset α) (w x : α → ℝ) (lambda : ℝ) (n : ℕ) (u : ℝ) :
    atomMoment A (fun a ↦ lambda * w a) x n u =
      lambda ^ n * atomMoment A w x n u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [atomMoment, atomMoment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs
      · rw [ih, pow_succ']
        ring
      · ring

lemma distinctAtomMoment_const_mul_weight
    (A : Finset α) (w x : α → ℝ) (lambda : ℝ) (n : ℕ) (u : ℝ) :
    distinctAtomMoment (fun a ↦ lambda * w a) x A n u =
      lambda ^ n * distinctAtomMoment w x A n u := by
  induction n generalizing A u with
  | zero => simp
  | succ n ih =>
      rw [distinctAtomMoment, distinctAtomMoment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs
      · rw [ih, pow_succ']
        ring
      · ring

end

end Erdos783
