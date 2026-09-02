import ErdosProblems.Erdos652.OrderedPinnedDistances
import Mathlib.Data.Fin.VecNotation

open scoped Real
noncomputable section

namespace Erdos652

/-- Cartesian-coordinate constructor for the Euclidean plane. -/
def xyPoint (x y : ℝ) : Point := WithLp.toLp 2 ![x, y]

@[simp] lemma xyPoint_apply_zero (x y : ℝ) : xyPoint x y 0 = x := rfl
@[simp] lemma xyPoint_apply_one (x y : ℝ) : xyPoint x y 1 = y := rfl

lemma dist_xyPoint_sq (x y a b : ℝ) :
    dist (xyPoint x y) (xyPoint a b) ^ 2 =
      (x - a) ^ 2 + (y - b) ^ 2 := by
  rw [dist_eq_norm]
  change ‖xyPoint x y - xyPoint a b‖ ^ 2 = _
  have hnorm := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin 2 => ℝ) (xyPoint x y - xyPoint a b)
  rw [hnorm]
  norm_num

open Classical in
/-- The `k` distinguished pins on the horizontal axis. -/
def elekesCenters (k : ℕ) : Finset Point :=
  (Finset.Icc 1 k : Finset ℕ).image fun (a : ℕ) => xyPoint (a : ℝ) 0

lemma elekesCenters_card {k : ℕ} (_hk : 1 ≤ k) :
    (elekesCenters k).card = k := by
  rw [elekesCenters, Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have h0 := congrArg (fun p : Point => p 0) hab
    simp only [xyPoint_apply_zero] at h0
    exact_mod_cast h0

/-- Integer parameters for Elekes's circle grid. -/
def elekesParameters (k s : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 s).product (Finset.Icc 1 (k * s))

/-- The point indexed by `(i,c)` has ordinate
`sqrt(s² + c - i²)`. -/
def elekesGridPoint (s : ℕ) (u : ℕ × ℕ) : Point :=
  xyPoint u.1 (Real.sqrt ((s : ℝ) ^ 2 + u.2 - (u.1 : ℝ) ^ 2))

lemma elekesGrid_radicand_pos {k s : ℕ} {u : ℕ × ℕ}
    (hu : u ∈ elekesParameters k s) :
    0 < (s : ℝ) ^ 2 + u.2 - (u.1 : ℝ) ^ 2 := by
  rcases Finset.mem_product.mp hu with ⟨hi, hc⟩
  have hi' := Finset.mem_Icc.mp hi
  have hc' := Finset.mem_Icc.mp hc
  have hisq : (u.1 : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by
    gcongr
    exact_mod_cast hi'.2
  have hcpos : (0 : ℝ) < u.2 := by exact_mod_cast hc'.1
  linarith

lemma elekesGridPoint_injective {k s : ℕ} :
    Set.InjOn (elekesGridPoint s) (elekesParameters k s : Set (ℕ × ℕ)) := by
  intro u hu v hv huv
  have hfirst := congrArg (fun p : Point => p 0) huv
  simp only [elekesGridPoint, xyPoint_apply_zero] at hfirst
  have hui : u.1 = v.1 := by exact_mod_cast hfirst
  have hsecond := congrArg (fun p : Point => p 1) huv
  simp only [elekesGridPoint, xyPoint_apply_one] at hsecond
  have huRad := (elekesGrid_radicand_pos hu).le
  have hvRad := (elekesGrid_radicand_pos hv).le
  have huSq := Real.sq_sqrt huRad
  have hvSq := Real.sq_sqrt hvRad
  have hcReal : (u.2 : ℝ) = v.2 := by
    rw [hsecond] at huSq
    rw [hvSq] at huSq
    rw [hui] at huSq
    linarith
  have huc : u.2 = v.2 := by exact_mod_cast hcReal
  exact Prod.ext hui huc

open Classical in
/-- Elekes's circle grid. -/
def elekesGrid (k s : ℕ) : Finset Point :=
  (elekesParameters k s).image (elekesGridPoint s)

lemma elekesParameters_card {k s : ℕ} (_hk : 1 ≤ k) (_hs : 1 ≤ s) :
    (elekesParameters k s).card = k * s ^ 2 := by
  simp [elekesParameters]
  ring

lemma elekesGrid_card {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s) :
    (elekesGrid k s).card = k * s ^ 2 := by
  rw [elekesGrid, Finset.card_image_iff.mpr elekesGridPoint_injective]
  exact elekesParameters_card hk hs

lemma elekesCenters_disjoint_grid {k s : ℕ} :
    Disjoint (elekesCenters k) (elekesGrid k s) := by
  apply Finset.disjoint_left.mpr
  intro p hpC hpG
  rcases Finset.mem_image.mp hpC with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hpG with ⟨u, hu, hpoint⟩
  have hsecond := congrArg (fun p : Point => p 1) hpoint
  simp only [xyPoint_apply_one, elekesGridPoint] at hsecond
  have hpos := Real.sqrt_pos.2 (elekesGrid_radicand_pos hu)
  linarith

lemma card_image_le_card_image_of_eq_imp
    {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ x ∈ S, ∀ y ∈ S, g x = g y → f x = f y) :
    (S.image f).card ≤ (S.image g).card := by
  let rep (z : S.image f) : α :=
    Classical.choose (Finset.mem_image.mp z.2)
  have hrep_mem (z : S.image f) : rep z ∈ S :=
    (Classical.choose_spec (Finset.mem_image.mp z.2)).1
  have hrep_eq (z : S.image f) : f (rep z) = z.1 :=
    (Classical.choose_spec (Finset.mem_image.mp z.2)).2
  let φ (z : S.image f) : S.image g :=
    ⟨g (rep z), Finset.mem_image.mpr ⟨rep z, hrep_mem z, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro z w hzw
    apply Subtype.ext
    have hg : g (rep z) = g (rep w) := congrArg Subtype.val hzw
    calc
      z.1 = f (rep z) := (hrep_eq z).symm
      _ = f (rep w) := h (rep z) (hrep_mem z) (rep w) (hrep_mem w) hg
      _ = w.1 := hrep_eq w
  simpa using Fintype.card_le_of_injective φ hφ

/-- The integer which controls the squared distance from the `a`th pin.
It ranges over at most `3ks` values. -/
def elekesCode (a s : ℕ) (u : ℕ × ℕ) : ℕ :=
  u.2 + 2 * a * (s - u.1)

lemma elekesCode_mem_Icc {k s a : ℕ} {u : ℕ × ℕ}
    (ha : a ∈ Finset.Icc 1 k) (hu : u ∈ elekesParameters k s) :
    elekesCode a s u ∈ Finset.Icc 1 (3 * k * s) := by
  rcases Finset.mem_product.mp hu with ⟨hi, hc⟩
  have hi' := Finset.mem_Icc.mp hi
  have hc' := Finset.mem_Icc.mp hc
  have ha' := Finset.mem_Icc.mp ha
  apply Finset.mem_Icc.mpr
  constructor
  · exact hc'.1.trans (Nat.le_add_right _ _)
  · have htwoa : 2 * a ≤ 2 * k := Nat.mul_le_mul_left 2 ha'.2
    have hsub : s - u.1 ≤ s := Nat.sub_le _ _
    have hprod : 2 * a * (s - u.1) ≤ 2 * k * s :=
      Nat.mul_le_mul htwoa hsub
    calc
      elekesCode a s u ≤ k * s + 2 * k * s := Nat.add_le_add hc'.2 hprod
      _ = 3 * k * s := by ring

lemma elekesGrid_distance_eq_of_code_eq
    {k s a : ℕ} {u v : ℕ × ℕ}
    (hu : u ∈ elekesParameters k s)
    (hv : v ∈ elekesParameters k s)
    (hcode : elekesCode a s u = elekesCode a s v) :
    dist (xyPoint a 0) (elekesGridPoint s u) =
      dist (xyPoint a 0) (elekesGridPoint s v) := by
  rcases Finset.mem_product.mp hu with ⟨hui, _⟩
  rcases Finset.mem_product.mp hv with ⟨hvi, _⟩
  have hui' := (Finset.mem_Icc.mp hui).2
  have hvi' := (Finset.mem_Icc.mp hvi).2
  have hcodeR :
      (u.2 : ℝ) + 2 * (a : ℝ) * ((s - u.1 : ℕ) : ℝ) =
        (v.2 : ℝ) + 2 * (a : ℝ) * ((s - v.1 : ℕ) : ℝ) := by
    exact_mod_cast hcode
  rw [Nat.cast_sub hui', Nat.cast_sub hvi'] at hcodeR
  have huRad := (elekesGrid_radicand_pos hu).le
  have hvRad := (elekesGrid_radicand_pos hv).le
  have hsq :
      dist (xyPoint a 0) (elekesGridPoint s u) ^ 2 =
        dist (xyPoint a 0) (elekesGridPoint s v) ^ 2 := by
    rw [elekesGridPoint, elekesGridPoint, dist_xyPoint_sq, dist_xyPoint_sq]
    simp only [zero_sub, neg_sq]
    rw [Real.sq_sqrt huRad, Real.sq_sqrt hvRad]
    nlinarith
  have hdu0 : 0 ≤ dist (xyPoint a 0) (elekesGridPoint s u) := dist_nonneg
  have hdv0 : 0 ≤ dist (xyPoint a 0) (elekesGridPoint s v) := dist_nonneg
  nlinarith

lemma elekesGrid_distanceRadii_card_le
    {k s a : ℕ} (_hk : 1 ≤ k) (_hs : 1 ≤ s)
    (ha : a ∈ Finset.Icc 1 k) :
    (distanceRadii (xyPoint a 0) (elekesGrid k s)).card ≤ 3 * k * s := by
  let f : ℕ × ℕ → ℝ := fun u => dist (xyPoint a 0) (elekesGridPoint s u)
  let g : ℕ × ℕ → ℕ := elekesCode a s
  have hfactor : ∀ x ∈ elekesParameters k s, ∀ y ∈ elekesParameters k s,
      g x = g y → f x = f y := by
    intro x hx y hy hxy
    exact elekesGrid_distance_eq_of_code_eq hx hy hxy
  calc
    (distanceRadii (xyPoint a 0) (elekesGrid k s)).card =
        ((elekesParameters k s).image f).card := by
      simp only [distanceRadii, elekesGrid, Finset.image_image]
      change ((elekesParameters k s).image
        (fun u => dist (xyPoint a 0) (elekesGridPoint s u))).card = _
      rfl
    _ ≤ ((elekesParameters k s).image g).card :=
      card_image_le_card_image_of_eq_imp _ _ _ hfactor
    _ ≤ (Finset.Icc 1 (3 * k * s)).card := by
      apply Finset.card_le_card
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
      exact elekesCode_mem_Icc ha hu
    _ = 3 * k * s := by
      simp

lemma distanceRadii_union_card_le (p : Point) (A B : Finset Point) :
    (distanceRadii p (A ∪ B)).card ≤
      (distanceRadii p A).card + (distanceRadii p B).card := by
  simp only [distanceRadii, Finset.image_union]
  exact Finset.card_union_le _ _

lemma elekes_full_distance_bound {k s a : ℕ}
    (hk : 1 ≤ k) (hs : 1 ≤ s) (ha : a ∈ Finset.Icc 1 k) :
    (distanceRadii (xyPoint a 0) (elekesCenters k ∪ elekesGrid k s)).card ≤
      k + 3 * k * s := by
  calc
    (distanceRadii (xyPoint a 0) (elekesCenters k ∪ elekesGrid k s)).card ≤
        (distanceRadii (xyPoint a 0) (elekesCenters k)).card +
          (distanceRadii (xyPoint a 0) (elekesGrid k s)).card :=
      distanceRadii_union_card_le _ _ _
    _ ≤ (elekesCenters k).card + 3 * k * s := by
      exact Nat.add_le_add Finset.card_image_le
        (elekesGrid_distanceRadii_card_le hk hs ha)
    _ = k + 3 * k * s := by rw [elekesCenters_card hk]

/-- Elekes's construction in the exact eventual-`n` form required by the
definition of `αₖ`.  The constant `8k+1` is deliberately coarse. -/
theorem elekes_eventual_low_points (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset Point, S.card = n ∧
        k ≤ (lowPinnedDistancePoints S (8 * k + 1)).card := by
  refine ⟨max k 1, ?_⟩
  intro n hn
  have hkn : k ≤ n := (le_max_left k 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right k 1).trans hn
  let s : ℕ := Nat.sqrt n + 1
  have hs : 1 ≤ s := by simp [s]
  have hcapacity : n - k ≤ (elekesGrid k s).card := by
    rw [elekesGrid_card hk hs]
    have hnlt : n < s ^ 2 := by
      simpa [s, pow_two] using Nat.lt_succ_sqrt n
    have hsle : s ^ 2 ≤ k * s ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (s ^ 2) hk
    omega
  obtain ⟨Q, hQgrid, hQcard⟩ := Finset.exists_subset_card_eq hcapacity
  let S : Finset Point := elekesCenters k ∪ Q
  have hCQ : Disjoint (elekesCenters k) Q :=
    (elekesCenters_disjoint_grid (k := k) (s := s)).mono_right hQgrid
  have hScard : S.card = n := by
    change (elekesCenters k ∪ Q).card = n
    rw [Finset.card_union_of_disjoint hCQ, elekesCenters_card hk, hQcard]
    omega
  refine ⟨S, hScard, ?_⟩
  calc
    k = (elekesCenters k).card := (elekesCenters_card hk).symm
    _ ≤ (lowPinnedDistancePoints S (8 * k + 1)).card := Finset.card_le_card (by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
  · have hSsub : S ⊆ elekesCenters k ∪ elekesGrid k s := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_right _ (hQgrid hx)
    have herase : S.erase (xyPoint a 0) ⊆
        elekesCenters k ∪ elekesGrid k s :=
      (Finset.erase_subset _ _).trans hSsub
    have hcountNat : pinnedDistanceCount (xyPoint a 0) S ≤ k + 3 * k * s := by
      exact (distanceRadii_card_mono (p := xyPoint a 0) herase).trans
        (elekes_full_distance_bound hk hs ha)
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
    have hsReal : (s : ℝ) ≤ 2 * Real.sqrt n := by
      dsimp [s]
      push_cast
      have hnat := Real.nat_sqrt_le_real_sqrt (a := n)
      linarith
    have hcountReal : (pinnedDistanceCount (xyPoint a 0) S : ℝ) ≤
        7 * (k : ℝ) * Real.sqrt n := by
      have hc : (pinnedDistanceCount (xyPoint a 0) S : ℝ) ≤
          (k : ℝ) + 3 * k * s := by exact_mod_cast hcountNat
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
      nlinarith
    change (pinnedDistanceCount (xyPoint a 0) S : ℝ) <
      (8 * (k : ℝ) + 1) * Real.sqrt S.card
    rw [hScard]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    nlinarith)

end Erdos652
