import ErdosProblems.Erdos856b.Blowup
import ErdosProblems.Erdos856b.Capacity
import ErdosProblems.Erdos856b.Squarefree

/-! # Choosing primes from disjoint buckets -/

namespace Erdos856b

open scoped BigOperators

abbrev Selections {t : ℕ} (P : Fin t → Finset ℕ) (F : Finset (Finset (Fin t))) :=
  Σ s : F, (i : s.val) → P i.val

noncomputable def selectionSupport {t : ℕ} {P : Fin t → Finset ℕ}
    {F : Finset (Finset (Fin t))} (q : Selections P F) : Finset ℕ :=
  Finset.univ.image (fun i => (q.2 i).val)

noncomputable def selectionNumber {t : ℕ} {P : Fin t → Finset ℕ}
    {F : Finset (Finset (Fin t))} (q : Selections P F) : ℕ :=
  ∏ i, (q.2 i).val

variable {t : ℕ} {P : Fin t → Finset ℕ} {F : Finset (Finset (Fin t))}

theorem selectedValue_injective
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (q : Selections P F) :
    Function.Injective (fun i => (q.2 i).val) := by
  intro i j hij
  dsimp at hij
  apply Subtype.ext
  by_contra hne
  apply Finset.disjoint_left.mp (hdis i.val j.val hne) (q.2 i).property
  rw [hij]
  exact (q.2 j).property

theorem selectionNumber_eq_prod_support
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (q : Selections P F) :
    selectionNumber q = ∏ p ∈ selectionSupport q, p := by
  rw [selectionSupport, Finset.prod_image]
  · rfl
  · intro i _ j _ hij
    exact selectedValue_injective hdis q hij

theorem selectionSupport_prime (hp : ∀ i p, p ∈ P i → p.Prime)
    (q : Selections P F) : ∀ p ∈ selectionSupport q, p.Prime := by
  intro p hmem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
  exact hp i.val (q.2 i).val (q.2 i).property

theorem selectionNumber_primeFactors
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) (q : Selections P F) :
    (selectionNumber q).primeFactors = selectionSupport q := by
  rw [selectionNumber_eq_prod_support hdis q]
  exact Nat.primeFactors_prod (selectionSupport_prime hp q)

theorem selectionNumber_squarefree
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) (q : Selections P F) :
    Squarefree (selectionNumber q) := by
  unfold selectionNumber
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply (Nat.coprime_primes (hp _ _ (q.2 i).property) (hp _ _ (q.2 j).property)).mpr
    intro h
    exact hij (selectedValue_injective hdis q h)
  · intro i _
    exact (hp _ _ (q.2 i).property).squarefree

theorem exists_bucketIndex (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    ∃ π : ℕ → Fin t, ∀ i p, p ∈ P i → π p = i := by
  classical
  let π (p : ℕ) : Fin t := if h : ∃ i, p ∈ P i then Classical.choose h else ⟨0, ht⟩
  refine ⟨π, fun i p hp => ?_⟩
  have hex : ∃ i, p ∈ P i := ⟨i, hp⟩
  dsimp [π]
  rw [dif_pos hex]
  by_contra hne
  exact Finset.disjoint_left.mp (hdis _ i hne) (Classical.choose_spec hex) hp

theorem selectionSupport_image {π : ℕ → Fin t}
    (hπ : ∀ i p, p ∈ P i → π p = i) (q : Selections P F) :
    (selectionSupport q).image π = q.1.val := by
  unfold selectionSupport
  rw [Finset.image_image]
  change Finset.univ.image (fun i : q.1.val => π (q.2 i).val) = q.1.val
  have heq : (fun i : q.1.val => π (q.2 i).val) = (fun i => i.val) := by
    funext i
    exact hπ i.val (q.2 i).val (q.2 i).property
  rw [heq]
  simpa only [Finset.attach_eq_univ] using (Finset.attach_image_val (s := q.1.val))

theorem selectionSupport_injOn {π : ℕ → Fin t}
    (hπ : ∀ i p, p ∈ P i → π p = i) (q : Selections P F) :
    Set.InjOn π (selectionSupport q) := by
  intro p hp q' hq heq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
  have hij : i = j := by
    apply Subtype.ext
    simpa only [hπ _ _ (q.2 i).property, hπ _ _ (q.2 j).property] using heq
  rw [hij]

theorem selectionSupport_injective {π : ℕ → Fin t}
    (hπ : ∀ i p, p ∈ P i → π p = i) :
    Function.Injective (selectionSupport (P := P) (F := F)) := by
  rintro ⟨s, a⟩ ⟨s', b⟩ heq
  have hs : s = s' := by
    apply Subtype.ext
    rw [← selectionSupport_image hπ ⟨s, a⟩, ← selectionSupport_image hπ ⟨s', b⟩, heq]
  subst s'
  have hab : a = b := by
    funext i
    apply Subtype.ext
    have hi : (a i).val ∈ selectionSupport (⟨s, b⟩ : Selections P F) := by
      rw [← heq]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
    have hindex : j = i := by
      apply Subtype.ext
      have h := congrArg π hji
      simpa only [hπ _ _ (b j).property, hπ _ _ (a i).property] using h
    subst j
    exact hji.symm
  subst b
  rfl

theorem selectionNumber_injective (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) :
    Function.Injective (selectionNumber (P := P) (F := F)) := by
  obtain ⟨π, hπ⟩ := exists_bucketIndex ht hdis
  intro q q' h
  apply selectionSupport_injective hπ
  have h' := congrArg Nat.primeFactors h
  simpa only [selectionNumber_primeFactors hdis hp] using h'

/-- The integers obtained by choosing one prime from every selected bucket. -/
noncomputable def realization (P : Fin t → Finset ℕ) (F : Finset (Finset (Fin t))) :
    Finset ℕ := Finset.univ.image (selectionNumber (P := P) (F := F))

theorem realization_squarefree
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) : ∀ a ∈ realization P F, Squarefree a := by
  intro a ha
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
  exact selectionNumber_squarefree hdis hp q

theorem realization_lcmFree {k : ℕ} (hk : 3 ≤ k) (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) (hF : UnionFree k F) :
    LcmFree k (realization P F) := by
  obtain ⟨π, hπ⟩ := exists_bucketIndex ht hdis
  apply (lcmFree_iff_unionFree_primeFactors (realization_squarefree hdis hp)).mpr
  intro a ha hmem hbad
  obtain ⟨u, hu⟩ := hbad
  have hpre : ∀ i, ∃ q : Selections P F, selectionSupport q = a i := by
    intro i
    obtain ⟨m, hm, heq⟩ := Finset.mem_image.mp (hmem i)
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨q, (selectionNumber_primeFactors hdis hp q).symm.trans heq⟩
  choose q hq using hpre
  have hpartial : ∀ i, Set.InjOn π (a i) := by
    intro i
    rw [← hq i]
    exact selectionSupport_injOn hπ _
  apply hF (fun i => (a i).image π) (common_union_image_injective hk ha π hpartial hu)
  · intro i
    rw [← hq i, selectionSupport_image hπ]
    exact (q i).1.property
  · exact ⟨u.image π, fun i j hij => by rw [← Finset.image_union, hu i j hij]⟩

theorem realization_weight (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) :
    (∑ a ∈ realization P F, (a : ℝ)⁻¹) =
      ∑ s ∈ F, ∏ i ∈ s, ∑ p ∈ P i, (p : ℝ)⁻¹ := by
  classical
  rw [realization, Finset.sum_image]
  · rw [Fintype.sum_sigma]
    simp only [selectionNumber, Nat.cast_prod, ← Finset.prod_inv_distrib]
    rw [← Finset.sum_coe_sort F]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Fintype.prod_sum (fun (i : s.val) (p : P i.val) => (p.val : ℝ)⁻¹)]
    calc
      (∏ i : s.val, ∑ p : P i.val, (p.val : ℝ)⁻¹) =
          ∏ i : s.val, ∑ p ∈ P i.val, (p : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i _
        exact Finset.sum_coe_sort (P i.val) (fun p => (p : ℝ)⁻¹)
      _ = ∏ i ∈ s.val, ∑ p ∈ P i, (p : ℝ)⁻¹ :=
        Finset.prod_coe_sort s.val (fun i => ∑ p ∈ P i, (p : ℝ)⁻¹)
  · intro q _ q' _ h
    exact selectionNumber_injective ht hdis hp h

theorem realization_weight_lower (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) {z : ℝ} (hz : 0 ≤ z)
    (hweight : ∀ i, z ≤ ∑ p ∈ P i, (p : ℝ)⁻¹) :
    partitionWeight F z ≤ (reciprocalWeight (realization P F) : ℝ) := by
  have heq : (reciprocalWeight (realization P F) : ℝ) =
      ∑ a ∈ realization P F, (a : ℝ)⁻¹ := by simp [reciprocalWeight]
  rw [heq, realization_weight ht hdis hp]
  apply Finset.sum_le_sum
  intro s _
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => hz) (fun i _ => hweight i)

theorem selectionNumber_le_pow {X : ℝ} (hX : 1 ≤ X)
    (hP : ∀ i p, p ∈ P i → (p : ℝ) ≤ X) (q : Selections P F) :
    (selectionNumber q : ℝ) ≤ X ^ t := by
  calc
    (selectionNumber q : ℝ) = ∏ i, ((q.2 i).val : ℝ) := by
      simp [selectionNumber]
    _ ≤ ∏ _i : q.1.val, X := Finset.prod_le_prod (fun _ _ => by positivity)
      (fun i _ => hP i.val (q.2 i).val (q.2 i).property)
    _ = X ^ q.1.val.card := by simp
    _ ≤ X ^ t := pow_le_pow_right₀ hX (by simpa using Finset.card_le_univ q.1.val)

theorem realization_subset_interval
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) {X : ℝ} (hX : 1 ≤ X)
    (hP : ∀ i p, p ∈ P i → (p : ℝ) ≤ X) {N : ℕ} (hN : X ^ t ≤ N) :
    realization P F ⊆ Finset.Icc 1 N := by
  intro a ha
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (selectionNumber_squarefree hdis hp q).ne_zero
  · exact_mod_cast (selectionNumber_le_pow hX hP q).trans hN

/-- Finite arithmetic transference from a weighted union-free family to `[1,N]`. -/
theorem partitionWeight_le_f_of_prime_buckets {k : ℕ} (hk : 3 ≤ k) (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) {X : ℝ} (hX : 1 ≤ X)
    (hP : ∀ i p, p ∈ P i → (p : ℝ) ≤ X) {N : ℕ} (hN : X ^ t ≤ N)
    {z : ℝ} (hz : 0 ≤ z) (hweight : ∀ i, z ≤ ∑ p ∈ P i, (p : ℝ)⁻¹)
    (hF : UnionFree k F) : partitionWeight F z ≤ f k N :=
  (realization_weight_lower ht hdis hp hz hweight).trans
    (reciprocalWeight_le_f (realization_subset_interval hdis hp hX hP hN)
      (realization_lcmFree hk ht hdis hp hF))

theorem C_le_f_of_prime_buckets {k : ℕ} (hk : 3 ≤ k) (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) {X : ℝ} (hX : 1 ≤ X)
    (hP : ∀ i p, p ∈ P i → (p : ℝ) ≤ X) {N : ℕ} (hN : X ^ t ≤ N)
    {z : ℝ} (hz : 0 ≤ z) (hweight : ∀ i, z ≤ ∑ p ∈ P i, (p : ℝ)⁻¹) :
    C k t z ≤ f k N := by
  classical
  unfold C
  apply Finset.sup'_le
  intro F hF
  have hfree : UnionFree k F := by
    simp only [allUnionFreeFamilies, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hF
    rcases hF with rfl | hF
    · exact unionFree_empty (by omega)
    · exact hF
  exact partitionWeight_le_f_of_prime_buckets hk ht hdis hp hX hP hN hz hweight hfree

end Erdos856b
