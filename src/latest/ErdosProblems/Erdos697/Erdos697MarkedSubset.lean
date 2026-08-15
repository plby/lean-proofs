import ErdosProblems.Erdos697.Erdos697WeightedSubset

/-!
# Marked subset-product upper bounds for Erdős 697

This file contains the finite estimate used in the density-zero direction.
One coordinate of a witnessing subproduct is required to lie in a marked
set.  Removing that coordinate leaves an exact Bernoulli configuration;
the marked coordinate costs only the largest odds-mass of one residue
class.  Thus a cardinality cutoff `K` costs `2^K`, rather than the much
larger first-moment factor obtained by summing over all subproducts.
-/

open scoped BigOperators

namespace Erdos697.MarkedSubset

noncomputable section

open Erdos697

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [CommGroup G]

/-- A selected set has a target-hitting subproduct which uses at least one
coordinate from `J`. -/
def hitsUsing (f : I → G) (J : Finset I) (B : Finset G)
    (S : Finset I) : Prop :=
  ∃ T : Finset I, T ⊆ S ∧ T.Nonempty ∧
    (∏ i ∈ T, f i) ∈ B ∧ ∃ i ∈ T, i ∈ J

/-- The exact Bernoulli configurations of cardinality at most `K` which
have a marked target-hitting subproduct. -/
noncomputable def event (f : I → G) (J : Finset I) (B : Finset G)
    (K : ℕ) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S ↦ S.card ≤ K ∧ hitsUsing f J B S

private theorem weight_insert_of_not_mem
    (p : I → ℝ) (hp : ∀ i, p i < 1)
    (R : Finset I) {q : I} (hq : q ∉ R) :
    Bernoulli.weight (Finset.univ : Finset I) p (insert q R) =
      Bernoulli.zeroBase (Finset.univ : Finset I) p *
        Bernoulli.odds p q * ∏ i ∈ R, Bernoulli.odds p i := by
  rw [Bernoulli.weight_eq_zeroBase_mul_prod_odds _ _ _
    (fun i _ ↦ Finset.mem_univ i) (fun i _ ↦ hp i)]
  rw [Finset.prod_insert hq]
  ring

private theorem sum_mul_mem_le_card_mul
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (f : I → G)
    (J : Finset I) (B : Finset G) (c : G) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g : G, (∑ i ∈ J.filter (fun i ↦ f i = g), w i) ≤ M) :
    (∑ i ∈ J.filter (fun i ↦ f i * c ∈ B), w i) ≤
      (B.card : ℝ) * M := by
  classical
  let A := J.filter (fun i ↦ f i * c ∈ B)
  let T := (B ×ˢ J).filter (fun x ↦ f x.2 = x.1 * c⁻¹)
  let enc : I → G × I := fun i ↦ (f i * c, i)
  have hencinj : Function.Injective enc := by
    intro i j h
    exact congrArg Prod.snd h
  have himage : Finset.image enc A ⊆ T := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_filter.mp hi
    simp only [T, Finset.mem_filter, Finset.mem_product, enc]
    refine ⟨⟨hi'.2, hi'.1⟩, ?_⟩
    simp
  calc
    (∑ i ∈ J.filter (fun i ↦ f i * c ∈ B), w i) =
        ∑ i ∈ A, w i := by rfl
    _ = ∑ x ∈ Finset.image enc A, w x.2 := by
      rw [Finset.sum_image hencinj.injOn]
    _ ≤ ∑ x ∈ T, w x.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro x hxT hx
        exact hw x.2)
    _ = ∑ b ∈ B, ∑ i ∈ J.filter (fun i ↦ f i = b * c⁻¹), w i := by
      simp only [T, Finset.sum_filter, Finset.sum_product]
    _ ≤ ∑ _b ∈ B, M := by
      apply Finset.sum_le_sum
      intro b hb
      exact hM _
    _ = (B.card : ℝ) * M := by simp

/-- Sharp finite marked-hitting estimate.  `M` is an upper bound for the
odds-mass of every residue fiber among the marked coordinates. -/
theorem sum_weight_event_le
    [LinearOrder I]
    (p : I → ℝ) (f : I → G) (J : Finset I) (B : Finset G)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g : G,
      (∑ i ∈ J.filter (fun i ↦ f i = g), Bernoulli.odds p i) ≤ M)
    (K : ℕ) :
    (∑ S ∈ event f J B K,
        Bernoulli.weight (Finset.univ : Finset I) p S) ≤
      (2 : ℝ) ^ K * (B.card : ℝ) * M := by
  classical
  let E := event f J B K
  let z := Bernoulli.zeroBase (Finset.univ : Finset I) p
  have hw0 (i : I) : 0 ≤ Bernoulli.odds p i := by
    exact div_nonneg (hp0 i) (sub_nonneg.mpr (hp1 i).le)
  have hz0 : 0 ≤ z :=
    Bernoulli.zeroBase_nonneg _ _ (fun i _ ↦ (hp1 i).le)
  have hweight0 (S : Finset I) :
      0 ≤ Bernoulli.weight (Finset.univ : Finset I) p S := by
    apply Bernoulli.weight_nonneg
    · intro i _; exact hp0 i
    · intro i _; exact (hp1 i).le
    · simp
  let witness : ∀ S : {S // S ∈ E}, Finset I := fun S ↦
    (show hitsUsing f J B S.1 by
      simpa [E, event] using (Finset.mem_filter.mp S.2).2.2).choose
  have hwitness (S : {S // S ∈ E}) :
      witness S ⊆ S.1 ∧ (witness S).Nonempty ∧
        (∏ i ∈ witness S, f i) ∈ B ∧
          ∃ i ∈ witness S, i ∈ J := by
    exact (show hitsUsing f J B S.1 by
      simpa [E, event] using (Finset.mem_filter.mp S.2).2.2).choose_spec
  let marked : ∀ S : {S // S ∈ E}, I := fun S ↦
    (hwitness S).2.2.2.choose
  have hmarkedW (S : {S // S ∈ E}) : marked S ∈ witness S :=
    (hwitness S).2.2.2.choose_spec.1
  have hmarkedJ (S : {S // S ∈ E}) : marked S ∈ J :=
    (hwitness S).2.2.2.choose_spec.2
  have hmarkedS (S : {S // S ∈ E}) : marked S ∈ S.1 :=
    (hwitness S).1 (hmarkedW S)
  let rest (S : {S // S ∈ E}) := S.1.erase (marked S)
  let subrest (S : {S // S ∈ E}) := (witness S).erase (marked S)
  have hsubrest (S : {S // S ∈ E}) : subrest S ⊆ rest S := by
    intro i hi
    simp only [subrest, rest, Finset.mem_erase] at hi ⊢
    exact ⟨hi.1, (hwitness S).1 hi.2⟩
  have hrestcard (S : {S // S ∈ E}) : (rest S).card < K := by
    have hcard : S.1.card ≤ K := by
      simpa [E, event] using (Finset.mem_filter.mp S.2).2.1
    have hSpos : 0 < S.1.card := Finset.card_pos.mpr ⟨marked S, hmarkedS S⟩
    change (S.1.erase (marked S)).card < K
    rw [Finset.card_erase_of_mem (hmarkedS S)]
    omega
  have hprod (S : {S // S ∈ E}) :
      f (marked S) * ∏ i ∈ subrest S, f i ∈ B := by
    have h := (hwitness S).2.2.1
    have heq :
        (∏ i ∈ witness S, f i) =
          f (marked S) * ∏ i ∈ (witness S).erase (marked S), f i := by
      rw [mul_comm, Finset.prod_erase_mul _ _ (hmarkedW S)]
    rw [heq] at h
    exact h
  let D : Finset (Finset I × Finset I × I) :=
    Finset.univ.filter fun x ↦
      x.1.card < K ∧ x.2.1 ⊆ x.1 ∧ x.2.2 ∉ x.1 ∧
        x.2.2 ∈ J ∧
          f x.2.2 * ∏ i ∈ x.2.1, f i ∈ B
  let enc : {S // S ∈ E} → Finset I × Finset I × I := fun S ↦
    (rest S, subrest S, marked S)
  have hencD (S : {S // S ∈ E}) : enc S ∈ D := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, enc]
    exact ⟨hrestcard S, hsubrest S,
      Finset.notMem_erase _ _, hmarkedJ S, hprod S⟩
  have hencinj : Function.Injective enc := by
    intro S T h
    apply Subtype.ext
    have hR : rest S = rest T := congrArg Prod.fst h
    have hq : marked S = marked T := congrArg (fun x ↦ x.2.2) h
    calc
      S.1 = insert (marked S) (rest S) := by
        exact (Finset.insert_erase (hmarkedS S)).symm
      _ = insert (marked T) (rest T) := by rw [hq, hR]
      _ = T.1 := Finset.insert_erase (hmarkedS T)
  have hinjSum :
      (∑ S ∈ E, Bernoulli.weight (Finset.univ : Finset I) p S) ≤
        ∑ x ∈ D,
          Bernoulli.weight (Finset.univ : Finset I) p (insert x.2.2 x.1) := by
    let A : Finset {S // S ∈ E} := Finset.univ
    have himage : Finset.image enc A ⊆ D := by
      intro x hx
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hx
      exact hencD S
    calc
      (∑ S ∈ E, Bernoulli.weight (Finset.univ : Finset I) p S) =
          ∑ S : {S // S ∈ E},
            Bernoulli.weight (Finset.univ : Finset I) p S.1 := by
        exact Finset.sum_subtype E (fun _ ↦ Iff.rfl) _
      _ = ∑ S ∈ A,
            Bernoulli.weight (Finset.univ : Finset I) p S.1 := by simp [A]
      _ = ∑ x ∈ Finset.image enc A,
            Bernoulli.weight (Finset.univ : Finset I) p (insert x.2.2 x.1) := by
        rw [Finset.sum_image hencinj.injOn]
        apply Finset.sum_congr rfl
        intro S _
        rw [show insert (enc S).2.2 (enc S).1 = S.1 by
          simp only [enc]
          exact Finset.insert_erase (hmarkedS S)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro x hxD _
        exact hweight0 _)
  have hDsum :
      (∑ x ∈ D,
          Bernoulli.weight (Finset.univ : Finset I) p (insert x.2.2 x.1)) ≤
        (2 : ℝ) ^ K * (B.card : ℝ) * M := by
    -- Expand the finite witness space in the order `rest, subrest, marked`.
    calc
      (∑ x ∈ D,
          Bernoulli.weight (Finset.univ : Finset I) p (insert x.2.2 x.1)) =
          ∑ R ∈ (Finset.univ : Finset (Finset I)).filter (fun R ↦ R.card < K),
            ∑ A ∈ R.powerset,
              ∑ q ∈ J.filter (fun q ↦ q ∉ R ∧
                  f q * ∏ i ∈ A, f i ∈ B),
                Bernoulli.weight (Finset.univ : Finset I) p (insert q R) := by
        simp only [D, Finset.sum_filter, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro R hRuniv
        by_cases hRK : R.card < K
        · simp only [hRK, true_and, if_true]
          rw [show R.powerset =
              (Finset.univ : Finset (Finset I)).filter (fun A ↦ A ⊆ R) by
            ext A
            simp]
          simp only [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro A hAuniv
          by_cases hAR : A ⊆ R
          · simp only [hAR, true_and, if_true]
            rw [show J = (Finset.univ : Finset I).filter (fun q ↦ q ∈ J) by
              ext q
              simp]
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro q hquniv
            by_cases hqJ : q ∈ J <;> simp [hqJ, and_assoc]
          · simp [hAR]
        · simp [hRK]
      _ ≤ ∑ R ∈ (Finset.univ : Finset (Finset I)).filter (fun R ↦ R.card < K),
            ∑ A ∈ R.powerset,
              z * (∏ i ∈ R, Bernoulli.odds p i) *
                ((B.card : ℝ) * M) := by
        apply Finset.sum_le_sum
        intro R hR
        apply Finset.sum_le_sum
        intro A hA
        calc
          (∑ q ∈ J.filter (fun q ↦ q ∉ R ∧
              f q * ∏ i ∈ A, f i ∈ B),
              Bernoulli.weight (Finset.univ : Finset I) p (insert q R)) =
            z * (∏ i ∈ R, Bernoulli.odds p i) *
              ∑ q ∈ J.filter (fun q ↦ q ∉ R ∧
                f q * ∏ i ∈ A, f i ∈ B), Bernoulli.odds p q := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            have hqR : q ∉ R := (Finset.mem_filter.mp hq).2.1
            rw [weight_insert_of_not_mem p hp1 R hqR]
            ring
          _ ≤ z * (∏ i ∈ R, Bernoulli.odds p i) *
              ∑ q ∈ J.filter (fun q ↦
                f q * ∏ i ∈ A, f i ∈ B), Bernoulli.odds p q := by
            have hset :
                J.filter (fun q ↦ q ∉ R ∧ f q * ∏ i ∈ A, f i ∈ B) ⊆
                  J.filter (fun q ↦ f q * ∏ i ∈ A, f i ∈ B) := by
              intro q hq
              have hq' := Finset.mem_filter.mp hq
              exact Finset.mem_filter.mpr ⟨hq'.1, hq'.2.2⟩
            have hsubsum := Finset.sum_le_sum_of_subset_of_nonneg hset (by
                intro i hi hni
                exact hw0 i)
            exact mul_le_mul_of_nonneg_left hsubsum
              (mul_nonneg hz0 (Finset.prod_nonneg fun i hi ↦ hw0 i))
          _ ≤ z * (∏ i ∈ R, Bernoulli.odds p i) *
              ((B.card : ℝ) * M) := by
            exact mul_le_mul_of_nonneg_left
              (sum_mul_mem_le_card_mul (Bernoulli.odds p) hw0 f J B
                (∏ i ∈ A, f i) hM0 hM)
              (mul_nonneg hz0 (Finset.prod_nonneg fun i hi ↦ hw0 i))
      _ = ∑ R ∈ (Finset.univ : Finset (Finset I)).filter (fun R ↦ R.card < K),
            z * (∏ i ∈ R, Bernoulli.odds p i) *
              ((R.powerset.card : ℝ) * (B.card : ℝ) * M) := by
        apply Finset.sum_congr rfl
        intro R hR
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ R ∈ (Finset.univ : Finset (Finset I)).filter (fun R ↦ R.card < K),
            z * (∏ i ∈ R, Bernoulli.odds p i) *
              ((2 : ℝ) ^ K * (B.card : ℝ) * M) := by
        apply Finset.sum_le_sum
        intro R hR
        have hRK : R.card < K := (Finset.mem_filter.mp hR).2
        have hcard : (R.powerset.card : ℝ) ≤ (2 : ℝ) ^ K := by
          simp only [Finset.card_powerset]
          norm_cast
          exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hRK.le
        have hbase : 0 ≤ z * ∏ i ∈ R, Bernoulli.odds p i := by
          exact mul_nonneg hz0 (Finset.prod_nonneg fun i hi ↦ hw0 i)
        gcongr
      _ = ((∑ R ∈ (Finset.univ : Finset (Finset I)).filter (fun R ↦ R.card < K),
            z * ∏ i ∈ R, Bernoulli.odds p i)) *
              ((2 : ℝ) ^ K * (B.card : ℝ) * M) := by
        rw [Finset.sum_mul]
      _ ≤ ((∑ R : Finset I,
            z * ∏ i ∈ R, Bernoulli.odds p i)) *
              ((2 : ℝ) ^ K * (B.card : ℝ) * M) := by
        have hsumle :
            (∑ R ∈ (Finset.univ : Finset (Finset I)).filter
                (fun R ↦ R.card < K),
              z * ∏ i ∈ R, Bernoulli.odds p i) ≤
              ∑ R : Finset I, z * ∏ i ∈ R, Bernoulli.odds p i :=
          Finset.sum_le_sum_of_subset_of_nonneg (by
          intro R hR
          exact (Finset.mem_filter.mp hR).1) (by
            intro R hR hnot
            exact mul_nonneg hz0 (Finset.prod_nonneg fun i hi ↦ hw0 i))
        exact mul_le_mul_of_nonneg_right hsumle (by positivity)
      _ = (2 : ℝ) ^ K * (B.card : ℝ) * M := by
        have hsum :
            (∑ R : Finset I, z * ∏ i ∈ R, Bernoulli.odds p i) = 1 := by
          rw [← Bernoulli.sum_weight_powerset (Finset.univ : Finset I) p]
          apply Finset.sum_congr rfl
          intro R _
          rw [Bernoulli.weight_eq_zeroBase_mul_prod_odds _ _ _
            (fun i _ ↦ Finset.mem_univ i) (fun i _ ↦ hp1 i)]
        rw [hsum]
        ring
  exact hinjSum.trans hDsum

end

end Erdos697.MarkedSubset
