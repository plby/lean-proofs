import ErdosProblems.Erdos957.Basic

open Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos957Packing

abbrev Point := EuclideanSpace ℝ (Fin 2)

lemma norm_sq_eq_coordinates (x : Point) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  · positivity

lemma abs_coordinate_le_norm (x : Point) (i : Fin 2) :
    |x i| ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)]
  rw [norm_sq_eq_coordinates]
  fin_cases i
  · change |x 0| ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2
    rw [sq_abs]
    exact le_add_of_nonneg_right (sq_nonneg (x 1))
  · change |x 1| ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2
    rw [sq_abs]
    exact le_add_of_nonneg_left (sq_nonneg (x 0))

/-- Coordinates of a point relative to an origin, quantized into half-unit cells. -/
noncomputable def halfCell (o x : Point) : ℤ × ℤ :=
  (⌊2 * (x 0 - o 0)⌋, ⌊2 * (x 1 - o 1)⌋)

lemma sub_lt_half_of_floor_two_eq {u v : ℝ}
    (h : ⌊2 * u⌋ = ⌊2 * v⌋) : |u - v| < 1 / 2 := by
  have hu₀ : ((Int.floor (2 * u) : ℤ) : ℝ) ≤ 2 * u := Int.floor_le _
  have hu₁ : 2 * u < ((Int.floor (2 * u) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hv₀ : ((Int.floor (2 * v) : ℤ) : ℝ) ≤ 2 * v := Int.floor_le _
  have hv₁ : 2 * v < ((Int.floor (2 * v) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [h] at hu₀ hu₁
  rw [abs_lt]
  constructor <;> linarith

lemma dist_lt_one_of_halfCell_eq {o x y : Point}
    (hcell : halfCell o x = halfCell o y) : dist x y < 1 := by
  have h₀ : ⌊2 * (x 0 - o 0)⌋ = ⌊2 * (y 0 - o 0)⌋ := congrArg Prod.fst hcell
  have h₁ : ⌊2 * (x 1 - o 1)⌋ = ⌊2 * (y 1 - o 1)⌋ := congrArg Prod.snd hcell
  have hdiff₀ := sub_lt_half_of_floor_two_eq h₀
  have hdiff₁ := sub_lt_half_of_floor_two_eq h₁
  rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [norm_sq_eq_coordinates]
  change (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 < 1 ^ 2
  rw [abs_lt] at hdiff₀ hdiff₁
  norm_num at hdiff₀ hdiff₁ ⊢
  nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]

lemma floor_two_mem_Ico_neg20_20 {u : ℝ} (hu : |u| < 10) :
    Int.floor (2 * u) ∈ Finset.Ico (-20 : ℤ) 20 := by
  simp only [Finset.mem_Ico, Int.le_floor, Int.floor_lt]
  norm_num
  rw [abs_lt] at hu
  constructor <;> linarith

/-- The absolute half-unit grid cell of a point. -/
noncomputable def absoluteHalfCell (x : Point) : ℤ × ℤ :=
  (⌊2 * x 0⌋, ⌊2 * x 1⌋)

lemma dist_lt_one_of_absoluteHalfCell_eq {x y : Point}
    (hcell : absoluteHalfCell x = absoluteHalfCell y) : dist x y < 1 := by
  have h₀ : ⌊2 * x 0⌋ = ⌊2 * y 0⌋ := congrArg Prod.fst hcell
  have h₁ : ⌊2 * x 1⌋ = ⌊2 * y 1⌋ := congrArg Prod.snd hcell
  have hdiff₀ := sub_lt_half_of_floor_two_eq h₀
  have hdiff₁ := sub_lt_half_of_floor_two_eq h₁
  rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [norm_sq_eq_coordinates]
  change (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 < 1 ^ 2
  rw [abs_lt] at hdiff₀ hdiff₁
  norm_num at hdiff₀ hdiff₁ ⊢
  nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]

/-- Generic coordinate-minimum grid packing bound.  At integer diameter
threshold `K`, each coordinate occupies at most `2K+1` half-unit cells. -/
theorem card_le_grid_of_pairwise_one_le_dist
    (K : ℤ)
    (A : Finset Point)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ (K : ℝ)) :
    A.card ≤ (2 * K + 1).toNat ^ 2 := by
  classical
  by_cases hA : A.Nonempty
  · let C₀ : Finset ℤ := A.image fun x ↦ ⌊2 * x 0⌋
    let C₁ : Finset ℤ := A.image fun x ↦ ⌊2 * x 1⌋
    have hC₀ : C₀.Nonempty := hA.image _
    have hC₁ : C₁.Nonempty := hA.image _
    let m₀ : ℤ := C₀.min' hC₀
    let m₁ : ℤ := C₁.min' hC₁
    let w : ℤ := 2 * K + 1
    let I₀ : Finset ℤ := Finset.Ico m₀ (m₀ + w)
    let I₁ : Finset ℤ := Finset.Ico m₁ (m₁ + w)
    obtain ⟨y₀, hy₀A, hy₀⟩ := Finset.mem_image.mp (Finset.min'_mem C₀ hC₀)
    obtain ⟨y₁, hy₁A, hy₁⟩ := Finset.mem_image.mp (Finset.min'_mem C₁ hC₁)
    have hcoord (x : Point) (hx : x ∈ A) (y : Point) (hy : y ∈ A) (i : Fin 2) :
        |x i - y i| ≤ (K : ℝ) := by
      calc
        |x i - y i| = |(x - y) i| := by rfl
        _ ≤ ‖x - y‖ := abs_coordinate_le_norm (x - y) i
        _ = dist x y := by rw [dist_eq_norm]
        _ ≤ (K : ℝ) := hdiam x hx y hy
    have hmem₀ (x : Point) (hx : x ∈ A) : ⌊2 * x 0⌋ ∈ I₀ := by
      simp only [I₀, Finset.mem_Ico]
      constructor
      · simpa [m₀] using
          (Finset.min'_le C₀ ⌊2 * x 0⌋ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      · have hxfloor : ((Int.floor (2 * x 0) : ℤ) : ℝ) ≤ 2 * x 0 := Int.floor_le _
        have hyfloor : 2 * y₀ 0 < ((Int.floor (2 * y₀ 0) : ℤ) : ℝ) + 1 :=
          Int.lt_floor_add_one _
        have hxy := (abs_le.mp (hcoord x hx y₀ hy₀A 0)).2
        have hcast : ((Int.floor (2 * x 0) : ℤ) : ℝ) <
            ((Int.floor (2 * y₀ 0) + (2 * K + 1) : ℤ) : ℝ) := by
          push_cast
          linarith
        have hint : Int.floor (2 * x 0) < Int.floor (2 * y₀ 0) + (2 * K + 1) := by
          exact_mod_cast hcast
        simpa [m₀, w, hy₀] using hint
    have hmem₁ (x : Point) (hx : x ∈ A) : ⌊2 * x 1⌋ ∈ I₁ := by
      simp only [I₁, Finset.mem_Ico]
      constructor
      · simpa [m₁] using
          (Finset.min'_le C₁ ⌊2 * x 1⌋ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      · have hxfloor : ((Int.floor (2 * x 1) : ℤ) : ℝ) ≤ 2 * x 1 := Int.floor_le _
        have hyfloor : 2 * y₁ 1 < ((Int.floor (2 * y₁ 1) : ℤ) : ℝ) + 1 :=
          Int.lt_floor_add_one _
        have hxy := (abs_le.mp (hcoord x hx y₁ hy₁A 1)).2
        have hcast : ((Int.floor (2 * x 1) : ℤ) : ℝ) <
            ((Int.floor (2 * y₁ 1) + (2 * K + 1) : ℤ) : ℝ) := by
          push_cast
          linarith
        have hint : Int.floor (2 * x 1) < Int.floor (2 * y₁ 1) + (2 * K + 1) := by
          exact_mod_cast hcast
        simpa [m₁, w, hy₁] using hint
    have himage : A.image absoluteHalfCell ⊆ I₀ ×ˢ I₁ := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_product.mpr ⟨hmem₀ x hx, hmem₁ x hx⟩
    have hinj : Set.InjOn absoluteHalfCell A := by
      intro x hx y hy hxy
      by_contra hne
      exact (not_lt_of_ge (hsep x hx y hy hne))
        (dist_lt_one_of_absoluteHalfCell_eq hxy)
    calc
      A.card = (A.image absoluteHalfCell).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (I₀ ×ˢ I₁).card := Finset.card_le_card himage
      _ = (2 * K + 1).toNat ^ 2 := by
        simp only [I₀, I₁, Finset.card_product, Int.card_Ico]
        have h₀ : (m₀ + w - m₀ : ℤ) = w := by omega
        have h₁ : (m₁ + w - m₁ : ℤ) = w := by omega
        rw [h₀, h₁]
        simp [w, pow_two]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

/-- The threshold needed by the locality argument: one-separated planar sets
of diameter below `101` contain at most `203² = 41209` points. -/
theorem card_le_41209_of_pairwise_one_le_dist
    (A : Finset Point)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y < 101) :
    A.card ≤ 41209 := by
  apply card_le_grid_of_pairwise_one_le_dist 101 A hsep
  intro x hx y hy
  exact (hdiam x hx y hy).le

/-- Closed-diameter version of `card_le_41209_of_pairwise_one_le_dist`. -/
theorem card_le_41209_of_pairwise_one_le_dist_of_dist_le
    (A : Finset Point)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 101) :
    A.card ≤ 41209 := by
  simpa using card_le_grid_of_pairwise_one_le_dist 101 A hsep hdiam

/-- Sharpened grid packing: since the diameter is below `10`, the range of
each coordinate has length below `10`.  Starting at the least occupied
half-unit cell in each coordinate therefore uses at most `21 × 21` cells. -/
theorem card_le_441_of_pairwise_one_le_dist
    (A : Finset Point)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y < 10) :
    A.card ≤ 441 := by
  classical
  by_cases hA : A.Nonempty
  · let C₀ : Finset ℤ := A.image fun x ↦ ⌊2 * x 0⌋
    let C₁ : Finset ℤ := A.image fun x ↦ ⌊2 * x 1⌋
    have hC₀ : C₀.Nonempty := hA.image _
    have hC₁ : C₁.Nonempty := hA.image _
    let m₀ : ℤ := C₀.min' hC₀
    let m₁ : ℤ := C₁.min' hC₁
    let I₀ : Finset ℤ := Finset.Ico m₀ (m₀ + 21)
    let I₁ : Finset ℤ := Finset.Ico m₁ (m₁ + 21)
    obtain ⟨y₀, hy₀A, hy₀⟩ := Finset.mem_image.mp (Finset.min'_mem C₀ hC₀)
    obtain ⟨y₁, hy₁A, hy₁⟩ := Finset.mem_image.mp (Finset.min'_mem C₁ hC₁)
    have hcoord (x : Point) (hx : x ∈ A) (y : Point) (hy : y ∈ A) (i : Fin 2) :
        |x i - y i| < 10 := by
      calc
        |x i - y i| = |(x - y) i| := by rfl
        _ ≤ ‖x - y‖ := abs_coordinate_le_norm (x - y) i
        _ = dist x y := by rw [dist_eq_norm]
        _ < 10 := hdiam x hx y hy
    have hmem₀ (x : Point) (hx : x ∈ A) : ⌊2 * x 0⌋ ∈ I₀ := by
      simp only [I₀, Finset.mem_Ico]
      constructor
      · simpa [m₀] using
          (Finset.min'_le C₀ ⌊2 * x 0⌋ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      · have hxfloor : ((Int.floor (2 * x 0) : ℤ) : ℝ) ≤ 2 * x 0 := Int.floor_le _
        have hyfloor : 2 * y₀ 0 < ((Int.floor (2 * y₀ 0) : ℤ) : ℝ) + 1 :=
          Int.lt_floor_add_one _
        have hxy := (abs_lt.mp (hcoord x hx y₀ hy₀A 0)).2
        have hcast : ((Int.floor (2 * x 0) : ℤ) : ℝ) <
            ((Int.floor (2 * y₀ 0) + 21 : ℤ) : ℝ) := by
          push_cast
          linarith
        have hint : Int.floor (2 * x 0) < Int.floor (2 * y₀ 0) + 21 := by
          exact_mod_cast hcast
        simpa [m₀, hy₀] using hint
    have hmem₁ (x : Point) (hx : x ∈ A) : ⌊2 * x 1⌋ ∈ I₁ := by
      simp only [I₁, Finset.mem_Ico]
      constructor
      · simpa [m₁] using
          (Finset.min'_le C₁ ⌊2 * x 1⌋ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      · have hxfloor : ((Int.floor (2 * x 1) : ℤ) : ℝ) ≤ 2 * x 1 := Int.floor_le _
        have hyfloor : 2 * y₁ 1 < ((Int.floor (2 * y₁ 1) : ℤ) : ℝ) + 1 :=
          Int.lt_floor_add_one _
        have hxy := (abs_lt.mp (hcoord x hx y₁ hy₁A 1)).2
        have hcast : ((Int.floor (2 * x 1) : ℤ) : ℝ) <
            ((Int.floor (2 * y₁ 1) + 21 : ℤ) : ℝ) := by
          push_cast
          linarith
        have hint : Int.floor (2 * x 1) < Int.floor (2 * y₁ 1) + 21 := by
          exact_mod_cast hcast
        simpa [m₁, hy₁] using hint
    have himage : A.image absoluteHalfCell ⊆ I₀ ×ˢ I₁ := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_product.mpr ⟨hmem₀ x hx, hmem₁ x hx⟩
    have hinj : Set.InjOn absoluteHalfCell A := by
      intro x hx y hy hxy
      by_contra hne
      exact (not_lt_of_ge (hsep x hx y hy hne))
        (dist_lt_one_of_absoluteHalfCell_eq hxy)
    calc
      A.card = (A.image absoluteHalfCell).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (I₀ ×ˢ I₁).card := Finset.card_le_card himage
      _ = 441 := by
        simp only [I₀, I₁, Finset.card_product, Int.card_Ico]
        have h₀ : (m₀ + 21 - m₀ : ℤ) = 21 := by omega
        have h₁ : (m₁ + 21 - m₁ : ℤ) = 21 := by omega
        rw [h₀, h₁]
        decide
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

/-- A deliberately coarse finite packing bound for a set of points of diameter
less than `10` and mutual separation at least `1`.

The proof maps every point to the pair of half-unit grid cells containing its
two coordinates relative to a chosen point.  The diameter hypothesis puts the
image in the `40 × 40` box `[-20,20) × [-20,20)`, while the separation
hypothesis makes the map injective. -/
theorem card_le_1600_of_pairwise_one_le_dist
    (A : Finset Point)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y < 10) :
    A.card ≤ 1600 := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨o, ho⟩ := hA
    let I : Finset ℤ := Finset.Ico (-20) 20
    have hcoord (x : Point) (hx : x ∈ A) (i : Fin 2) : |x i - o i| < 10 := by
      calc
        |x i - o i| = |(x - o) i| := by rfl
        _ ≤ ‖x - o‖ := abs_coordinate_le_norm (x - o) i
        _ = dist x o := by rw [dist_eq_norm]
        _ < 10 := hdiam x hx o ho
    have himage : A.image (halfCell o) ⊆ I ×ˢ I := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_product]
      exact ⟨floor_two_mem_Ico_neg20_20 (hcoord x hx 0),
        floor_two_mem_Ico_neg20_20 (hcoord x hx 1)⟩
    have hinj : Set.InjOn (halfCell o) A := by
      intro x hx y hy hxy
      by_contra hne
      have hlt : dist x y < 1 := dist_lt_one_of_halfCell_eq hxy
      exact (not_lt_of_ge (hsep x hx y hy hne)) hlt
    calc
      A.card = (A.image (halfCell o)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (I ×ˢ I).card := Finset.card_le_card himage
      _ = 1600 := by
        simp only [I, Finset.card_product, Int.card_Ico]
        decide
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

end Erdos957Packing

