import ErdosProblems.Erdos556.StableProfileDecomposition
import ErdosProblems.Erdos556.ProfileCleaning

/-! Cube-tiling classes with uniform per-vertex missing-edge bounds. -/

namespace Erdos556

open SimpleGraph Finset

structure CleanProfileSystem {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (n : ℕ) (η : ℝ) where
  weight : CubeProfile → ℝ
  admissible : IsCubeWeight weight
  tiling : IsCubeTiling weight
  sets : CubeProfile → Finset V
  disjoint : ∀ p q, p ≠ q → Disjoint (sets p) (sets q)
  size_lower : ∀ p, (weight p - η) * n ≤ (sets p).card
  size_upper : ∀ p, ((sets p).card : ℝ) ≤ (weight p + η) * n
  defect : ℕ
  defect_le : (defect : ℝ) ≤ η * n
  dense : ∀ p q i, uniqueProfileSeparator p q i →
    BipartiteDefect (c.graph i) (sets p) (sets q) defect

theorem exists_clean_profile_system (η : ℝ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (c : ThreeColouring V) (n : ℕ), n₀ ≤ n → Odd n →
      Fintype.card V = 4 * n - 3 → (∀ i, ¬ cycleGraph n ⊑ c.graph i) →
      Nonempty (CleanProfileSystem c n η) := by
  let τ : ℝ := min (η / 4) (η ^ 2 / 100)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτη : τ ≤ η / 4 := min_le_left _ _
  have hτsq : τ ≤ η ^ 2 / 100 := min_le_right _ _
  obtain ⟨n₁, hstable⟩ := exists_stable_three_colour_decomposition τ hτ
  obtain ⟨m, hm⟩ := exists_nat_ge (8 / η)
  refine ⟨max 1 (max m n₁), ?_⟩
  intro V _ _ c n hn hodd hN hno
  classical
  have hn₁ : n₁ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hmn : m ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hηn : 8 ≤ η * n := by
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hh := (div_le_iff₀ hη).mp (hm.trans hmnR)
    nlinarith
  obtain ⟨E, D, h, v, hv, ht, hclose, hmissing⟩ := hstable c n hn₁ hodd hN hno
  let d : ℕ := ⌊η * n / 4⌋₊
  have hdle : (d : ℝ) ≤ η * n / 4 := Nat.floor_le (by positivity)
  have hdgt : η * n / 4 < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdlo : η * n / 8 ≤ (d : ℝ) := by linarith
  obtain ⟨Z, hZcount, hclean⟩ := h.exists_profile_cleaning d
  have hZcountR : (d : ℝ) * Z.card ≤ 2 * (Nat.card h.potentialMissing.edgeSet : ℝ) := by
    exact_mod_cast hZcount
  have hZnonneg : (0 : ℝ) ≤ Z.card := by positivity
  have hZ : (Z.card : ℝ) ≤ η * n / 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hdlo hZnonneg
    have hτscaled := mul_le_mul_of_nonneg_right hτsq (sq_nonneg (n : ℝ))
    have hpos : 0 < η * n := mul_pos hη hnpos
    nlinarith
  let A : CubeProfile → Finset V := fun p => h.profileClass p \ Z
  refine ⟨{
    weight := v
    admissible := hv
    tiling := ht
    sets := A
    disjoint := fun p q hpq => (h.profileClass_disjoint p q hpq).mono sdiff_subset sdiff_subset
    size_lower := ?_
    size_upper := ?_
    defect := d
    defect_le := by linarith
    dense := hclean }⟩
  · intro p
    have hp := (abs_lt.mp (hclose p)).1
    have hratio : v p - τ < ((h.profileClass p).card : ℝ) / n := by
      change -τ < ((h.profileClass p).card : ℝ) / n - v p at hp
      linarith
    have hraw := (lt_div_iff₀ hnpos).mp hratio
    have hc := card_sdiff_add_card_inter (h.profileClass p) Z
    have hi := card_le_card (inter_subset_right : h.profileClass p ∩ Z ⊆ Z)
    have hcard : ((h.profileClass p).card : ℝ) ≤ (A p).card + (Z.card : ℝ) := by
      exact_mod_cast (show (h.profileClass p).card ≤ (A p).card + Z.card by dsimp only [A]; omega)
    have hτηscaled := mul_le_mul_of_nonneg_right hτη hnpos.le
    nlinarith
  · intro p
    have hp := (abs_lt.mp (hclose p)).2
    have hratio : ((h.profileClass p).card : ℝ) / n < v p + τ := by
      change ((h.profileClass p).card : ℝ) / n - v p < τ at hp
      linarith
    have hraw := (div_lt_iff₀ hnpos).mp hratio
    have hcard : ((A p).card : ℝ) ≤ (h.profileClass p).card := by
      exact_mod_cast card_le_card (sdiff_subset : A p ⊆ h.profileClass p)
    have hτηscaled := mul_le_mul_of_nonneg_right hτη hnpos.le
    nlinarith

#print axioms exists_clean_profile_system

end Erdos556
