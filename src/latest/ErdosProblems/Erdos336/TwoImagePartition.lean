import ErdosProblems.Erdos336.ProjectionTwoPiece

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G Q : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup Q] [DecidableEq Q]

/-- Fibre over zero for a homomorphic two-image partition. -/
def zeroImagePart (T : Finset G) (ρ : G →+ Q) : Finset G :=
  T.filter (fun x => ρ x = 0)

/-- Complementary part of a homomorphic two-image partition. -/
def nonzeroImagePart (T : Finset G) (ρ : G →+ Q) : Finset G :=
  T.filter (fun x => ρ x ≠ 0)

@[simp] theorem mem_zeroImagePart {T : Finset G} {ρ : G →+ Q} {x : G} :
    x ∈ zeroImagePart T ρ ↔ x ∈ T ∧ ρ x = 0 := by
  simp [zeroImagePart]

@[simp] theorem mem_nonzeroImagePart {T : Finset G} {ρ : G →+ Q} {x : G} :
    x ∈ nonzeroImagePart T ρ ↔ x ∈ T ∧ ρ x ≠ 0 := by
  simp [nonzeroImagePart]

/-- A set with two homomorphic image classes and three double-image classes
splits its double sumset into three disjoint pieces. -/
theorem two_image_three_sum_partition
    (T : Finset G) (ρ : G →+ Q) (hzero : 0 ∈ T)
    (himage : (T.image ρ).card = 2)
    (hdoubleImage : ((T + T).image ρ).card = 3) :
    let A₀ := zeroImagePart T ρ
    let A₁ := nonzeroImagePart T ρ
    A₀.Nonempty ∧ A₁.Nonempty ∧
    T = A₀ ∪ A₁ ∧
    Disjoint (A₀ + A₀) (A₀ + A₁) ∧
    Disjoint (A₀ + A₀) (A₁ + A₁) ∧
    Disjoint (A₀ + A₁) (A₁ + A₁) ∧
    (A₀ + A₀).card + (A₀ + A₁).card + (A₁ + A₁).card ≤
      (T + T).card := by
  classical
  dsimp
  let A₀ := zeroImagePart T ρ
  let A₁ := nonzeroImagePart T ρ
  have hzeroA₀ : 0 ∈ A₀ := mem_zeroImagePart.mpr ⟨hzero, ρ.map_zero⟩
  have hA₀ne : A₀.Nonempty := ⟨0, hzeroA₀⟩
  have hzeroImage : 0 ∈ T.image ρ := Finset.mem_image.mpr ⟨0, hzero, ρ.map_zero⟩
  have hA₁ne : A₁.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hsub : T.image ρ ⊆ {0} := by
      intro z hz
      obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hz
      have hxnot : x ∉ A₁ := by simp [hne]
      have hx0 : ρ x = 0 := by
        by_contra hx
        exact hxnot (mem_nonzeroImagePart.mpr ⟨hxT, hx⟩)
      simp [hx0]
    have hc := Finset.card_le_card hsub
    simp [himage] at hc
  obtain ⟨x₁, hx₁⟩ := hA₁ne
  let c := ρ x₁
  have hcne : c ≠ 0 := (mem_nonzeroImagePart.mp hx₁).2
  have hcImage : c ∈ T.image ρ :=
    Finset.mem_image.mpr ⟨x₁, (mem_nonzeroImagePart.mp hx₁).1, rfl⟩
  have hImageEq : T.image ρ = {0, c} := by
    have hsub : {0, c} ⊆ T.image ρ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hzeroImage
      · exact hcImage
    have hpaircard : ({0, c} : Finset Q).card = 2 :=
      Finset.card_pair hcne.symm
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hA₁map : ∀ x ∈ A₁, ρ x = c := by
    intro x hx
    have hxImage : ρ x ∈ T.image ρ :=
      Finset.mem_image.mpr ⟨x, (mem_nonzeroImagePart.mp hx).1, rfl⟩
    rw [hImageEq] at hxImage
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxImage
    rcases hxImage with hx0 | hxc
    · exact ((mem_nonzeroImagePart.mp hx).2 hx0).elim
    · exact hxc
  have hTunion : T = A₀ ∪ A₁ := by
    ext x
    simp [A₀, A₁, zeroImagePart, nonzeroImagePart]
    tauto
  have hdoubleSub : (T + T).image ρ ⊆ {0, c, c + c} := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hxT, y, hyT, rfl⟩ := Finset.mem_add.mp hw
    have hxIm : ρ x = 0 ∨ ρ x = c := by
      have : ρ x ∈ T.image ρ := Finset.mem_image.mpr ⟨x, hxT, rfl⟩
      simpa [hImageEq] using this
    have hyIm : ρ y = 0 ∨ ρ y = c := by
      have : ρ y ∈ T.image ρ := Finset.mem_image.mpr ⟨y, hyT, rfl⟩
      simpa [hImageEq] using this
    rw [ρ.map_add]
    rcases hxIm with hx | hx <;> rcases hyIm with hy | hy <;>
      simp [hx, hy, add_comm]
  have htwone0 : c + c ≠ 0 := by
    intro hcc
    have hsub : (T + T).image ρ ⊆ {0, c} := by
      intro z hz
      have hmem := hdoubleSub hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with hz0 | hzc | hzcc
      · exact Or.inl hz0
      · exact Or.inr hzc
      · exact Or.inl (hzcc.trans hcc)
    have hcCard := Finset.card_le_card hsub
    have hpaircard : ({0, c} : Finset Q).card = 2 :=
      Finset.card_pair hcne.symm
    rw [hdoubleImage, hpaircard] at hcCard
    omega
  have htwonec : c + c ≠ c := by
    intro hcc
    apply hcne
    have hcancel : c + c = c + 0 := by simpa using hcc
    exact add_left_cancel hcancel
  have hmapA₀ : ∀ x ∈ A₀, ρ x = 0 := fun x hx => (mem_zeroImagePart.mp hx).2
  have hD00_01 : Disjoint (A₀ + A₀) (A₀ + A₁) := by
    rw [Finset.disjoint_left]
    intro z hz00 hz01
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz00
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hz01
    have hm := congrArg ρ huv
    simp only [map_add, hmapA₀ x hx, hmapA₀ y hy,
      hmapA₀ u hu, hA₁map v hv, add_zero, zero_add] at hm
    exact hcne hm
  have hD00_11 : Disjoint (A₀ + A₀) (A₁ + A₁) := by
    rw [Finset.disjoint_left]
    intro z hz00 hz11
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz00
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hz11
    have hm := congrArg ρ huv
    simp only [map_add, hmapA₀ x hx, hmapA₀ y hy,
      hA₁map u hu, hA₁map v hv, add_zero] at hm
    exact htwone0 hm
  have hD01_11 : Disjoint (A₀ + A₁) (A₁ + A₁) := by
    rw [Finset.disjoint_left]
    intro z hz01 hz11
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz01
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hz11
    have hm := congrArg ρ huv
    simp only [map_add, hmapA₀ x hx, hA₁map y hy,
      hA₁map u hu, hA₁map v hv, zero_add] at hm
    exact htwonec hm
  have hUsub : (A₀ + A₀) ∪ (A₀ + A₁) ∪ (A₁ + A₁) ⊆ T + T := by
    intro z hz
    simp only [Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · exact Finset.add_subset_add
        (fun _ hx => (mem_zeroImagePart.mp hx).1)
        (fun _ hx => (mem_zeroImagePart.mp hx).1) hz
    · exact Finset.add_subset_add
        (fun _ hx => (mem_zeroImagePart.mp hx).1)
        (fun _ hx => (mem_nonzeroImagePart.mp hx).1) hz
    · exact Finset.add_subset_add
        (fun _ hx => (mem_nonzeroImagePart.mp hx).1)
        (fun _ hx => (mem_nonzeroImagePart.mp hx).1) hz
  have hUcard := Finset.card_le_card hUsub
  rw [Finset.card_union_of_disjoint
      ((Finset.disjoint_union_left).mpr ⟨hD00_11, hD01_11⟩),
    Finset.card_union_of_disjoint hD00_01] at hUcard
  exact ⟨hA₀ne, ⟨x₁, hx₁⟩, hTunion, hD00_01, hD00_11, hD01_11, hUcard⟩

end Erdos336
