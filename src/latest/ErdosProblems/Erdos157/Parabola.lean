import Mathlib.Tactic

/-!
# Parabola tags for the elementary construction in Erdős problem 157

All arguments are algebraic. In characteristic seven the triple fiber admits
an explicit parametrization by a prescribed-product fiber. No point-count
estimate is used. All declarations use the default computational limits.
-/

namespace Erdos157.Elementary.Parabola

section PairDecoding

variable {K : Type*} [Field K]

/-- The sum and sum of squares recover an unordered pair. -/
theorem pair_eq_of_sum_and_sq_sum (h2 : (2 : K) ≠ 0)
    (a b c d : K) (hsum : a + b = c + d)
    (hsquares : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hsumsq : (a + b) ^ 2 = (c + d) ^ 2 := congrArg (fun x : K => x ^ 2) hsum
  have htwice : (2 : K) * (a * b - c * d) = 0 := by
    linear_combination hsumsq - hsquares
  have hprod : a * b = c * d :=
    sub_eq_zero.mp ((mul_eq_zero.mp htwice).resolve_left h2)
  have hroot : (a - c) * (a - d) = 0 := by
    linear_combination a * hsum - hprod
  rcases mul_eq_zero.mp hroot with hac | had
  · have hac' : a = c := sub_eq_zero.mp hac
    exact Or.inl ⟨hac', by simpa [hac'] using hsum⟩
  · have had' : a = d := sub_eq_zero.mp had
    refine Or.inr ⟨had', ?_⟩
    linear_combination hsum - had'

/-- Therefore arbitrary tag-dependent masks also have the same pair sum. -/
theorem mask_sum_eq {G : Type*} [AddCommMonoid G] (τ : K → G)
    (h2 : (2 : K) ≠ 0) {a b c d : K}
    (hsum : a + b = c + d) (hsquares : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    τ a + τ b = τ c + τ d := by
  rcases pair_eq_of_sum_and_sq_sum h2 a b c d hsum hsquares with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact add_comm _ _

end PairDecoding

section TripleParametrization

variable {K : Type*} [Field K] [CharP K 7]

/-- An ordered triple with the specified two tag sums. -/
def IsTriple (u v : K) (t : K × K × K) : Prop :=
  t.1 + t.2.1 + t.2.2 = u ∧
    t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = v

/-- The first prescribed-product coordinate of a triple. -/
def firstParameter (u : K) (t : K × K × K) : K :=
  3 * t.1 + t.2.1 + u

/-- An inverse linear change of coordinates, valid in characteristic seven. -/
def ofParameters (u r s : K) : K × K × K :=
  (3 * r + 2 * s + 5 * u, -r + s - 2 * u, -2 * r - 3 * s - 2 * u)

omit [CharP K 7] in
theorem ofParameters_sum (u r s : K) :
    (ofParameters u r s).1 + (ofParameters u r s).2.1 +
      (ofParameters u r s).2.2 = u := by
  simp only [ofParameters]
  ring

theorem firstParameter_ofParameters (u r s : K) :
    firstParameter u (ofParameters u r s) = r := by
  have h7 : (7 : K) = 0 := CharP.cast_eq_zero K 7
  simp only [firstParameter, ofParameters]
  linear_combination (r + s + 2 * u) * h7

theorem ofParameters_sq_sum (u r s : K) :
    (ofParameters u r s).1 ^ 2 + (ofParameters u r s).2.1 ^ 2 +
      (ofParameters u r s).2.2 ^ 2 = r * s + 5 * u ^ 2 := by
  have h7 : (7 : K) = 0 := CharP.cast_eq_zero K 7
  simp only [ofParameters]
  linear_combination (2 * r ^ 2 + 3 * r * s + 6 * r * u +
    2 * s ^ 2 + 4 * s * u + 4 * u ^ 2) * h7

theorem ofParameters_isTriple (u v r s : K) (hprod : r * s = v + 2 * u ^ 2) :
    IsTriple u v (ofParameters u r s) := by
  refine ⟨ofParameters_sum u r s, ?_⟩
  rw [ofParameters_sq_sum, hprod]
  have h7 : (7 : K) = 0 := CharP.cast_eq_zero K 7
  linear_combination u ^ 2 * h7

/-- A family of at least `|K|-1` ordered tag representations of each target. -/
def unitTriple (u v : K) (r : Kˣ) : K × K × K :=
  ofParameters u (r : K) ((v + 2 * u ^ 2) / (r : K))

theorem unitTriple_isTriple (u v : K) (r : Kˣ) :
    IsTriple u v (unitTriple u v r) := by
  apply ofParameters_isTriple
  exact mul_div_cancel₀ _ r.ne_zero

theorem firstParameter_unitTriple (u v : K) (r : Kˣ) :
    firstParameter u (unitTriple u v r) = (r : K) :=
  firstParameter_ofParameters _ _ _

theorem unitTriple_injective (u v : K) : Function.Injective (unitTriple u v) := by
  intro r s hrs
  apply Units.ext
  simpa only [firstParameter_unitTriple] using congrArg (firstParameter u) hrs

end TripleParametrization

section DisjointSupports

variable {K : Type*} [Field K] [DecidableEq K]

/-- The set of tags used by an ordered triple, allowing repeated tags. -/
def support (t : K × K × K) : Finset K := {t.1, t.2.1, t.2.2}

omit [Field K] in
theorem support_card_le (t : K × K × K) : (support t).card ≤ 3 := by
  simp only [support]
  calc
    _ ≤ ({t.2.1, t.2.2} : Finset K).card + 1 := Finset.card_insert_le _ _
    _ ≤ 3 := by
      have := Finset.card_insert_le t.2.1 ({t.2.2} : Finset K)
      simp only [Finset.card_singleton] at this
      omega

/-- A member of the support can be moved into the first coordinate. -/
theorem exists_first_of_mem_support {u v a : K} {t : K × K × K}
    (ht : IsTriple u v t) (ha : a ∈ support t) :
    ∃ b c, IsTriple u v (a, b, c) ∧ support (a, b, c) = support t := by
  rcases t with ⟨x, y, z⟩
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨y, z, ht, rfl⟩
  · refine ⟨x, z, ?_, ?_⟩
    · simpa only [IsTriple, add_comm a x, add_comm (a ^ 2) (x ^ 2)] using ht
    · ext a
      simp only [support, Finset.mem_insert, Finset.mem_singleton]
      tauto
  · refine ⟨x, y, ?_, ?_⟩
    · rcases ht with ⟨hsum, hsq⟩
      constructor <;> dsimp
      · linear_combination hsum
      · linear_combination hsq
    · ext a
      simp only [support, Finset.mem_insert, Finset.mem_singleton]
      tauto

/-- For one target, two triple supports either coincide or are disjoint. -/
theorem support_eq_or_disjoint (h2 : (2 : K) ≠ 0) {u v : K}
    {t w : K × K × K} (ht : IsTriple u v t) (hw : IsTriple u v w) :
    support t = support w ∨ Disjoint (support t) (support w) := by
  by_cases hd : Disjoint (support t) (support w)
  · exact Or.inr hd
  left
  obtain ⟨a, hat, haw⟩ := Finset.not_disjoint_iff.mp hd
  obtain ⟨b, c, habc, hst⟩ := exists_first_of_mem_support ht hat
  obtain ⟨d, e, hade, hsw⟩ := exists_first_of_mem_support hw haw
  have hsum : b + c = d + e := by
    linear_combination habc.1 - hade.1
  have hsq : b ^ 2 + c ^ 2 = d ^ 2 + e ^ 2 := by
    linear_combination habc.2 - hade.2
  rw [← hst, ← hsw]
  rcases pair_eq_of_sum_and_sq_sum h2 b c d e hsum hsq with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · ext x
    simp only [support, Finset.mem_insert, Finset.mem_singleton]
    tauto

omit [Field K] in
/-- A coarse count that avoids choosing an ordering of the support. -/
theorem card_le_twentyseven_mul_card_support_image (s : Finset (K × K × K)) :
    s.card ≤ 27 * (s.image support).card := by
  classical
  rw [Finset.card_eq_sum_card_image support s]
  calc
    _ ≤ ∑ a ∈ s.image support, 27 := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      have hsub : {w ∈ s | support w = support t} ⊆
          (support t) ×ˢ ((support t) ×ˢ (support t)) := by
        intro w hw
        have heq := (Finset.mem_filter.mp hw).2
        simp only [Finset.mem_product, ← heq]
        simp [support]
      calc
        _ ≤ ((support t) ×ˢ ((support t) ×ˢ (support t))).card :=
          Finset.card_le_card hsub
        _ = (support t).card * ((support t).card * (support t).card) := by
          simp only [Finset.card_product]
        _ ≤ 3 * (3 * 3) :=
          Nat.mul_le_mul (support_card_le t)
            (Nat.mul_le_mul (support_card_le t) (support_card_le t))
        _ = 27 := rfl
    _ = _ := by simp [Nat.mul_comm]

end DisjointSupports

section FiniteFamilies

variable {K : Type*} [Field K] [CharP K 7] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
private theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff K 7 2).mp h
  norm_num at this

omit [Fintype K] [DecidableEq K] in
private theorem three_ne_zero : (3 : K) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff K 7 3).mp h
  norm_num at this

/-- All supports furnished by the explicit prescribed-product parametrization. -/
noncomputable def allSupports (u v : K) : Finset (Finset K) :=
  (Finset.univ.image (unitTriple u v)).image support

/-- Remove the possible constant triple. Every remaining support contains a
tag which occurs exactly once, so its mask sum has a uniform free coordinate. -/
noncomputable def tagSupports (u v : K) : Finset (Finset K) :=
  (allSupports u v).erase {u / 3}

theorem mem_allSupports {u v : K} {s : Finset K} (hs : s ∈ allSupports u v) :
    ∃ t, IsTriple u v t ∧ support t = s := by
  obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hs
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨unitTriple u v r, unitTriple_isTriple u v r, hts⟩

theorem tagSupports_pairwise_disjoint (u v : K) :
    (↑(tagSupports u v) : Set (Finset K)).Pairwise Disjoint := by
  intro s hs t ht hst
  obtain ⟨a, ha, has⟩ := mem_allSupports (Finset.mem_of_mem_erase hs)
  obtain ⟨b, hb, hbt⟩ := mem_allSupports (Finset.mem_of_mem_erase ht)
  rcases support_eq_or_disjoint (two_ne_zero (K := K)) ha hb with heq | hd
  · exact False.elim (hst (has.symm.trans (heq.trans hbt)))
  · simpa only [has, hbt] using hd

theorem tagSupports_card_bounds {u v : K} {s : Finset K}
    (hs : s ∈ tagSupports u v) : 2 ≤ s.card ∧ s.card ≤ 3 := by
  have hne : s ≠ {u / 3} := (Finset.mem_erase.mp hs).1
  obtain ⟨t, ht, hts⟩ := mem_allSupports (Finset.mem_of_mem_erase hs)
  refine ⟨?_, hts ▸ support_card_le t⟩
  by_contra hn
  have hsmall : (support t).card ≤ 1 := by rw [hts]; omega
  have hxy : t.1 = t.2.1 := Finset.card_le_one.mp hsmall _ (by simp [support])
    _ (by simp [support])
  have hxz : t.1 = t.2.2 := Finset.card_le_one.mp hsmall _ (by simp [support])
    _ (by simp [support])
  have hx : t.1 = u / 3 := by
    apply (eq_div_iff (three_ne_zero (K := K))).mpr
    have hsum := ht.1
    rw [← hxy, ← hxz] at hsum
    linear_combination hsum
  apply hne
  rw [← hts]
  simp [support, ← hxy, ← hxz, hx]

/-- There are at least `(card K - 1) / 27 - 1` independent tag supports.
The factor 27 is deliberately coarse; it suffices for all subsequent bounds. -/
theorem card_field_le_twentyseven_mul_tagSupports (u v : K) :
    Fintype.card K - 1 ≤ 27 * ((tagSupports u v).card + 1) := by
  have h := card_le_twentyseven_mul_card_support_image
    (Finset.univ.image (unitTriple u v))
  rw [Finset.card_image_of_injective _ (unitTriple_injective u v),
    Finset.card_univ, Fintype.card_units] at h
  have herase : (allSupports u v).card ≤ (tagSupports u v).card + 1 := by
    by_cases hm : ({u / 3} : Finset K) ∈ allSupports u v
    · rw [tagSupports, Finset.card_erase_of_mem hm]
      have hpos := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · simp only [tagSupports, Finset.erase_eq_of_notMem hm]
      omega
  exact h.trans (Nat.mul_le_mul_left 27 herase)

omit [Field K] [CharP K 7] [Fintype K] in
/-- A nonconstant ordered triple has a coordinate occurring exactly once. -/
theorem singleton_coordinate_of_two_le_card {t : K × K × K}
    (ht : 2 ≤ (support t).card) :
    (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2) ∨
    (t.2.1 ≠ t.1 ∧ t.2.1 ≠ t.2.2) ∨
    (t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1) := by
  by_cases hxy : t.1 = t.2.1
  · by_cases hxz : t.1 = t.2.2
    · simp [support, ← hxy, ← hxz] at ht
    · exact Or.inr (Or.inr ⟨Ne.symm hxz, by simpa [← hxy] using Ne.symm hxz⟩)
  · by_cases hxz : t.1 = t.2.2
    · exact Or.inr (Or.inl ⟨Ne.symm hxy, by simpa [← hxz] using Ne.symm hxy⟩)
    · exact Or.inl ⟨hxy, hxz⟩

/-- Enough field elements give an indexed family of independent tag trials. -/
theorem exists_disjoint_triples (u v : K) (n : ℕ)
    (hn : 1 ≤ n) (hcard : 49 * n ≤ Fintype.card K) :
    ∃ T : Fin n → K × K × K,
      (∀ i, IsTriple u v (T i)) ∧
      (∀ i, 2 ≤ (support (T i)).card) ∧
      Pairwise (fun i j => Disjoint (support (T i)) (support (T j))) := by
  have hbound := card_field_le_twentyseven_mul_tagSupports u v
  have hncard : n ≤ (tagSupports u v).card := by omega
  have hle : Fintype.card (Fin n) ≤ Fintype.card ↥(tagSupports u v) := by
    simpa using hncard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  have hex : ∀ i : Fin n, ∃ t, IsTriple u v t ∧ support t = (e i).1 :=
    fun i => mem_allSupports (Finset.mem_of_mem_erase (e i).2)
  choose T hT hs using hex
  refine ⟨T, hT, ?_, ?_⟩
  · intro i
    rw [hs i]
    exact (tagSupports_card_bounds (e i).2).1
  · intro i j hij
    rw [hs i, hs j]
    apply tagSupports_pairwise_disjoint u v (e i).2 (e j).2
    intro heq
    exact hij (e.injective (Subtype.ext heq))

end FiniteFamilies

end Erdos157.Elementary.Parabola
