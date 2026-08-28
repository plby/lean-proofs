import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineBasic

/-!
# Extending supported actual sheaf sections by zero

Apply an actual sheaf endomorphism whose support is a closed subset of
an open set, then extend by zero to a larger open set. The extension is
constructed by genuine two-open sheaf gluing and is uniquely specified
by its two restrictions. This is the section-level operation used to
solve actual one-cocycles from fine decompositions.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- The open complement of a specified closed support. -/
def outsideSupport (K : Set X) (hK : IsClosed K) : Opens X := ⟨Kᶜ, hK.isOpen_compl⟩

/-- The two genuine opens used for extension by zero. -/
def extensionCover (K : Set X) (hK : IsClosed K) (V U : Opens X) : Bool → Opens X
  | false => U ⊓ V
  | true => U ⊓ outsideSupport K hK

theorem extensionCover_le (K : Set X) (hK : IsClosed K) (V U : Opens X) (b : Bool) :
    extensionCover K hK V U b ≤ U := by
  cases b <;> exact inf_le_left

theorem extensionCover_covers (K : Set X) (hK : IsClosed K) (V U : Opens X)
    (hKV : K ⊆ V) : U ≤ iSup (extensionCover K hK V U) := by
  intro x hx
  by_cases h : x ∈ K
  · exact Opens.mem_iSup.mpr ⟨false, hx, hKV h⟩
  · exact Opens.mem_iSup.mpr ⟨true, hx, h⟩

variable (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (K : Set X) (hK : IsClosed K) (V : Opens X) (hKV : K ⊆ V)

include hKV

/-- An actual section is determined by these two restrictions. -/
theorem supportedExtension_ext (U : Opens X) {s t : Section F U}
    (hV : res F (V := U ⊓ V) inf_le_left s = res F inf_le_left t)
    (hKc : res F (V := U ⊓ outsideSupport K hK) inf_le_left s =
      res F inf_le_left t) : s = t := by
  apply F.eq_of_locally_eq' (extensionCover K hK V U) U
    (fun b => homOfLE (extensionCover_le K hK V U b))
    (extensionCover_covers K hK V U hKV)
  intro b
  cases b
  · exact hV
  · exact hKc

variable (φ : F ⟶ F) (hφ : IsZeroOn φ (outsideSupport K hK))

include hφ

/-- Apply the supported endomorphism and genuinely glue the result to
zero off its closed support. -/
theorem exists_supportedExtension (U : Opens X) (s : Section F (U ⊓ V)) :
    ∃ t : Section F U,
      res F (V := U ⊓ V) inf_le_left t = φ.hom.app (op (U ⊓ V)) s ∧
      res F (V := U ⊓ outsideSupport K hK) inf_le_left t = 0 := by
  let A := extensionCover K hK V U
  let t : ∀ b : Bool, Section F (A b)
    | false => φ.hom.app (op (U ⊓ V)) s
    | true => 0
  have ht : TopCat.Presheaf.IsCompatible F.obj A t := by
    intro i j
    cases i <;> cases j
    · rfl
    · change res F (V := (U ⊓ V) ⊓ (U ⊓ outsideSupport K hK)) inf_le_left
          (φ.hom.app (op (U ⊓ V)) s) = res F inf_le_right 0
      rw [map_zero, res_map,
        hφ ((U ⊓ V) ⊓ (U ⊓ outsideSupport K hK)) (inf_le_right.trans inf_le_right)]
      rfl
    · change res F (V := (U ⊓ outsideSupport K hK) ⊓ (U ⊓ V)) inf_le_left 0 =
        res F inf_le_right (φ.hom.app (op (U ⊓ V)) s)
      rw [map_zero, res_map,
        hφ ((U ⊓ outsideSupport K hK) ⊓ (U ⊓ V)) (inf_le_left.trans inf_le_right)]
      rfl
    · rfl
  obtain ⟨q, hq, _⟩ := F.existsUnique_gluing' A U
    (fun b => homOfLE (extensionCover_le K hK V U b))
    (extensionCover_covers K hK V U hKV) t ht
  exact ⟨q, hq false, hq true⟩

/-- The actual extension section supplied by the proved gluing construction. -/
def supportedExtension (U : Opens X) (s : Section F (U ⊓ V)) : Section F U :=
  (exists_supportedExtension F K hK V hKV φ hφ U s).choose

/-- On its original open domain the extension is the literal action. -/
theorem supportedExtension_on (U : Opens X) (s : Section F (U ⊓ V)) :
    res F (V := U ⊓ V) inf_le_left (supportedExtension F K hK V hKV φ hφ U s) =
      φ.hom.app (op (U ⊓ V)) s :=
  (exists_supportedExtension F K hK V hKV φ hφ U s).choose_spec.1

/-- Away from its closed support the actual extension is zero. -/
theorem supportedExtension_off (U : Opens X) (s : Section F (U ⊓ V)) :
    res F (V := U ⊓ outsideSupport K hK) inf_le_left
      (supportedExtension F K hK V hKV φ hφ U s) = 0 :=
  (exists_supportedExtension F K hK V hKV φ hφ U s).choose_spec.2

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
