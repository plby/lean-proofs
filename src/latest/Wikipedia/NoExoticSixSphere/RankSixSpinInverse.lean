import Wikipedia.NoExoticSixSphere.RankSixSpinMatrix

/-!
# Recovering skew coordinates from the spin matrix

Each upper-triangular entry is recovered by a real linear combination of
two spin-matrix entries. These coordinate equations prove injectivity on
actual skew matrices.
-/

namespace NoExoticSixSphere.RankSixSkewMatrix

theorem spin_eq_entry01 {A B : Matrix6} (h : spin A = spin B) :
    A 0 1 = B 0 1 := by
  have hh := congrArg (fun C : Matrix4 ↦ -((C 0 0).re + (C 3 3).re)) h
  change -((-A 0 1 - A 2 3 - A 4 5) + (-A 0 1 + A 2 3 + A 4 5)) =
    -((-B 0 1 - B 2 3 - B 4 5) + (-B 0 1 + B 2 3 + B 4 5)) at hh
  linarith only [hh]

theorem spin_eq_entry02 {A B : Matrix6} (h : spin A = spin B) :
    A 0 2 = B 0 2 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 2 3).im - (C 0 1).im)) h
  change ((A 0 2 + A 1 3) - (-A 0 2 + A 1 3)) =
    ((B 0 2 + B 1 3) - (-B 0 2 + B 1 3)) at hh
  linarith only [hh]

theorem spin_eq_entry03 {A B : Matrix6} (h : spin A = spin B) :
    A 0 3 = B 0 3 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 2 3).re - (C 0 1).re)) h
  change ((A 0 3 - A 1 2) - (-A 0 3 - A 1 2)) =
    ((B 0 3 - B 1 2) - (-B 0 3 - B 1 2)) at hh
  linarith only [hh]

theorem spin_eq_entry04 {A B : Matrix6} (h : spin A = spin B) :
    A 0 4 = B 0 4 := by
  have hh := congrArg (fun C : Matrix4 ↦ -((C 0 2).im + (C 1 3).im)) h
  change -((-A 0 4 + A 1 5) + (-A 0 4 - A 1 5)) =
    -((-B 0 4 + B 1 5) + (-B 0 4 - B 1 5)) at hh
  linarith only [hh]

theorem spin_eq_entry05 {A B : Matrix6} (h : spin A = spin B) :
    A 0 5 = B 0 5 := by
  have hh := congrArg (fun C : Matrix4 ↦ -((C 0 2).re + (C 1 3).re)) h
  change -((-A 0 5 - A 1 4) + (-A 0 5 + A 1 4)) =
    -((-B 0 5 - B 1 4) + (-B 0 5 + B 1 4)) at hh
  linarith only [hh]

theorem spin_eq_entry12 {A B : Matrix6} (h : spin A = spin B) :
    A 1 2 = B 1 2 := by
  have hh := congrArg (fun C : Matrix4 ↦ -((C 2 3).re + (C 0 1).re)) h
  change -((A 0 3 - A 1 2) + (-A 0 3 - A 1 2)) =
    -((B 0 3 - B 1 2) + (-B 0 3 - B 1 2)) at hh
  linarith only [hh]

theorem spin_eq_entry13 {A B : Matrix6} (h : spin A = spin B) :
    A 1 3 = B 1 3 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 2 3).im + (C 0 1).im)) h
  change ((A 0 2 + A 1 3) + (-A 0 2 + A 1 3)) =
    ((B 0 2 + B 1 3) + (-B 0 2 + B 1 3)) at hh
  linarith only [hh]

theorem spin_eq_entry14 {A B : Matrix6} (h : spin A = spin B) :
    A 1 4 = B 1 4 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 1 3).re - (C 0 2).re)) h
  change ((-A 0 5 + A 1 4) - (-A 0 5 - A 1 4)) =
    ((-B 0 5 + B 1 4) - (-B 0 5 - B 1 4)) at hh
  linarith only [hh]

theorem spin_eq_entry15 {A B : Matrix6} (h : spin A = spin B) :
    A 1 5 = B 1 5 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 0 2).im - (C 1 3).im)) h
  change ((-A 0 4 + A 1 5) - (-A 0 4 - A 1 5)) =
    ((-B 0 4 + B 1 5) - (-B 0 4 - B 1 5)) at hh
  linarith only [hh]

theorem spin_eq_entry23 {A B : Matrix6} (h : spin A = spin B) :
    A 2 3 = B 2 3 := by
  have hh := congrArg (fun C : Matrix4 ↦ -((C 0 0).re + (C 2 2).re)) h
  change -((-A 0 1 - A 2 3 - A 4 5) + (A 0 1 - A 2 3 + A 4 5)) =
    -((-B 0 1 - B 2 3 - B 4 5) + (B 0 1 - B 2 3 + B 4 5)) at hh
  linarith only [hh]

theorem spin_eq_entry24 {A B : Matrix6} (h : spin A = spin B) :
    A 2 4 = B 2 4 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 1 2).im - (C 0 3).im)) h
  change ((A 2 4 + A 3 5) - (-A 2 4 + A 3 5)) =
    ((B 2 4 + B 3 5) - (-B 2 4 + B 3 5)) at hh
  linarith only [hh]

theorem spin_eq_entry25 {A B : Matrix6} (h : spin A = spin B) :
    A 2 5 = B 2 5 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 1 2).re - (C 0 3).re)) h
  change ((A 2 5 - A 3 4) - (-A 2 5 - A 3 4)) =
    ((B 2 5 - B 3 4) - (-B 2 5 - B 3 4)) at hh
  linarith only [hh]

theorem spin_eq_entry34 {A B : Matrix6} (h : spin A = spin B) :
    A 3 4 = B 3 4 := by
  have hh := congrArg (fun C : Matrix4 ↦ -((C 1 2).re + (C 0 3).re)) h
  change -((A 2 5 - A 3 4) + (-A 2 5 - A 3 4)) =
    -((B 2 5 - B 3 4) + (-B 2 5 - B 3 4)) at hh
  linarith only [hh]

theorem spin_eq_entry35 {A B : Matrix6} (h : spin A = spin B) :
    A 3 5 = B 3 5 := by
  have hh := congrArg (fun C : Matrix4 ↦ ((C 1 2).im + (C 0 3).im)) h
  change ((A 2 4 + A 3 5) + (-A 2 4 + A 3 5)) =
    ((B 2 4 + B 3 5) + (-B 2 4 + B 3 5)) at hh
  linarith only [hh]

theorem spin_eq_entry45 {A B : Matrix6} (h : spin A = spin B) :
    A 4 5 = B 4 5 := by
  have hh := congrArg (fun C : Matrix4 ↦ -((C 0 0).re + (C 1 1).re)) h
  change -((-A 0 1 - A 2 3 - A 4 5) + (A 0 1 + A 2 3 - A 4 5)) =
    -((-B 0 1 - B 2 3 - B 4 5) + (B 0 1 + B 2 3 - B 4 5)) at hh
  linarith only [hh]

theorem spin_injective_on_skew {A B : Matrix6} (hA : A.transpose = -A)
    (hB : B.transpose = -B) (h : spin A = spin B) : A = B := by
  have hs : skew A = skew B := by
    simp only [skew,
      spin_eq_entry01 (A := A) (B := B) h,
      spin_eq_entry02 (A := A) (B := B) h,
      spin_eq_entry03 (A := A) (B := B) h,
      spin_eq_entry04 (A := A) (B := B) h,
      spin_eq_entry05 (A := A) (B := B) h,
      spin_eq_entry12 (A := A) (B := B) h,
      spin_eq_entry13 (A := A) (B := B) h,
      spin_eq_entry14 (A := A) (B := B) h,
      spin_eq_entry15 (A := A) (B := B) h,
      spin_eq_entry23 (A := A) (B := B) h,
      spin_eq_entry24 (A := A) (B := B) h,
      spin_eq_entry25 (A := A) (B := B) h,
      spin_eq_entry34 (A := A) (B := B) h,
      spin_eq_entry35 (A := A) (B := B) h,
      spin_eq_entry45 (A := A) (B := B) h]
  exact (skew_eq A hA).symm.trans (hs.trans (skew_eq B hB))

end NoExoticSixSphere.RankSixSkewMatrix
