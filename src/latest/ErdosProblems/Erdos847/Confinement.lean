/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos847.Pictures
import ErdosProblems.Erdos847.FiniteArch
import ErdosProblems.Erdos847.ConfinementKernels

namespace Erdos847Confinement

open Function Set
open Erdos847Pictures Erdos847FiniteArch

set_option autoImplicit false

variable {V P C N : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

section NormalizedSections

variable (source : Picture G P C) (x : V)
variable (lines : Set (Combinatorics.Line (MusicFiber source x) N))
variable {l : Alphabet → RawAmalgamPoint source x lines}

abbrev normalizedSection (R : NormalizedRawQuasiline source x lines l)
    (s : N) (i : Alphabet) : P :=
  sectionPoint source x (R.line i) (R.point i) s

/-- A constant outer section in normalized form is necessarily on the music
line. -/
theorem constant_section_mem_fiber
    (R : NormalizedRawQuasiline source x lines l)
    (s : N) (q : P) (hq : ∀ i, normalizedSection source x lines R s i = q) :
    source.proj q = x := by
  by_contra hqout
  have hq0 : q = R.point 0 := by
    rcases sectionPoint_mem_fiber_or_eq source x (R.line 0) (R.point 0) s with h | h
    · exact False.elim (hqout ((hq 0).symm ▸ h))
    · exact (hq 0).symm.trans h
  have hq1 : q = R.point 1 := by
    rcases sectionPoint_mem_fiber_or_eq source x (R.line 1) (R.point 1) s with h | h
    · exact False.elim (hqout ((hq 1).symm ▸ h))
    · exact (hq 1).symm.trans h
  have hbad : normalizedSection source x lines R R.coordinate 0 =
      normalizedSection source x lines R R.coordinate 1 := by
    change sectionPoint source x (R.line 0) (R.point 0) R.coordinate =
      sectionPoint source x (R.line 1) (R.point 1) R.coordinate
    rw [R.section_zero, R.section_one, ← hq0, ← hq1]
  exact Fin.zero_ne_one (R.source_section.1 hbad)

/-- Every section in normalized form is constant on the music line or is a
source quasiline. -/
theorem normalized_section_dichotomy
    (R : NormalizedRawQuasiline source x lines l) (s : N) :
    (∃ q, source.proj q = x ∧ ∀ i,
      normalizedSection source x lines R s i = q) ∨
      IsQuasiline source.embed (normalizedSection source x lines R s) := by
  rcases raw_quasiline_section source x lines (fun i => l (R.perm i))
      R.line R.point R.word_eq R.outer_quasiline s with hconst | hline
  · obtain ⟨q, hq⟩ := hconst
    exact Or.inl ⟨q, constant_section_mem_fiber source x lines R s q hq, hq⟩
  · exact Or.inr hline

/-- At most one entry of a nonconstant source section lies on the music
line. -/
theorem source_section_atMostOne_fiber
    (R : NormalizedRawQuasiline source x lines l) (s : N)
    (hs : IsQuasiline source.embed (normalizedSection source x lines R s))
    {i j : Alphabet}
    (hi : source.proj (normalizedSection source x lines R s i) = x)
    (hj : source.proj (normalizedSection source x lines R s j) = x) : i = j := by
  exact mapsOntoEdge_proj_injective source
    (source.quasiline_maps_edge _ hs) (hi.trans hj.symm)

/-- If all three normalized representative points are off the music line,
the status of a constant section is three copies of the same fixed letter. -/
theorem constant_section_status
    (R : NormalizedRawQuasiline source x lines l)
    (hp : ∀ i, source.proj (R.point i) ≠ x)
    (s : N) (q : P) (hq : source.proj q = x)
    (hsec : ∀ i, normalizedSection source x lines R s i = q) :
    ∃ a : MusicFiber source x,
      (R.line 0).idxFun s = some a ∧
      (R.line 1).idxFun s = some a ∧
      (R.line 2).idxFun s = some a := by
  let a : MusicFiber source x := ⟨q, hq⟩
  have fixed (i : Alphabet) : (R.line i).idxFun s = some a := by
    obtain ⟨f, hf, hval⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line i) (R.point i) q (hp i) hq s (hsec i)
    have hfa : f = a := Subtype.ext hval
    simpa [hfa] using hf
  exact ⟨a, fixed 0, fixed 1, fixed 2⟩

/-- The section-point formula is precisely the admissibility condition used
by the finite ternary classifiers. -/
theorem section_admissible
    (R : NormalizedRawQuasiline source x lines l) (s : N) :
    Erdos847ConfinementKernels.Admissible (fun q => source.proj q = x)
      R.point (normalizedSection source x lines R s) := by
  intro i
  exact sectionPoint_mem_fiber_or_eq source x (R.line i) (R.point i) s

/--
If the third entry of the normalized base section is also outside the music
fiber, then every nonconstant section has the same ordered row as the base
section.  Consequently all three selected outer lines agree.
-/
theorem outside_third_lines_equal
    (R : NormalizedRawQuasiline source x lines l)
    (hthird : source.proj
      (normalizedSection source x lines R R.coordinate 2) ≠ x) :
    R.line 0 = R.line 1 ∧ R.line 0 = R.line 2 := by
  classical
  let base : Alphabet → P := normalizedSection source x lines R R.coordinate
  have hb0 : base 0 = R.point 0 := R.section_zero
  have hb1 : base 1 = R.point 1 := R.section_one
  have hb2 : base 2 = R.point 2 := by
    apply (sectionPoint_mem_fiber_or_eq source x (R.line 2) (R.point 2)
      R.coordinate).resolve_left
    exact hthird
  have hp : ∀ i, source.proj (R.point i) ≠ x := by
    intro i
    fin_cases i
    · exact R.point_zero_not_fiber
    · exact R.point_one_not_fiber
    · simpa [base, hb2] using hthird
  have hbaseLine : IsCombinatorialLine source.embed base :=
    source.quasiline_is_line base R.source_section
  have each_nonconstant_eq (s : N)
      (hs : IsQuasiline source.embed (normalizedSection source x lines R s)) :
      normalizedSection source x lines R s = base := by
    let row : Alphabet → P := normalizedSection source x lines R s
    have hrowMaps := source.quasiline_maps_edge row hs
    have hrowAtMost : ∀ i j,
        source.proj (row i) = x → source.proj (row j) = x → i = j := by
      intro i j hi hj
      exact mapsOntoEdge_proj_injective source hrowMaps (hi.trans hj.symm)
    have hforms := Erdos847ConfinementKernels.normalized_row_four_forms
      (section_admissible source x lines R s) hrowAtMost
    have hrange : Set.range row = Set.range base := by
      have hrowLine : IsCombinatorialLine source.embed row :=
        source.quasiline_is_line row hs
      rcases hforms with h0 | h1 | h2 | h3
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (1 : Alphabet) ≠ 2)
          (h0.2.1.trans hb1.symm) (h0.2.2.trans hb2.symm))
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (0 : Alphabet) ≠ 2)
          (h1.1.trans hb0.symm) (h1.2.2.trans hb2.symm))
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (0 : Alphabet) ≠ 1)
          (h2.1.trans hb0.symm) (h2.2.1.trans hb1.symm))
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (0 : Alphabet) ≠ 1)
          (h3.1.trans hb0.symm) (h3.2.1.trans hb1.symm))
    by_contra hne
    have hcoords : row 0 ≠ R.point 0 ∨ row 1 ≠ R.point 1 ∨
        row 2 ≠ base 2 := by
      by_contra hall
      push Not at hall
      apply hne
      funext i
      fin_cases i
      · exact hall.1.trans hb0.symm
      · exact hall.2.1.trans hb1.symm
      · exact hall.2.2
    have hnormal := Erdos847ConfinementKernels.same_range_normal_forms
      R.point_zero_not_fiber R.point_one_not_fiber hs.1
      (section_admissible source x lines R s)
      (by simpa [hb0, hb1, Erdos847Pictures.range_fin3] using hrange)
      hcoords
    rcases hnormal with hswap0 | hswap1
    · have hp20 : R.point 2 = R.point 0 := hswap0.2.2.2
      have hb20 : base 2 = base 0 := hb2.trans (hp20.trans hb0.symm)
      exact (by decide : (2 : Alphabet) ≠ 0) (R.source_section.1 hb20)
    · have hp21 : R.point 2 = R.point 1 := hswap1.2.2.2
      have hb21 : base 2 = base 1 := hb2.trans (hp21.trans hb1.symm)
      exact (by decide : (2 : Alphabet) ≠ 1) (R.source_section.1 hb21)
  have hidx (i j : Alphabet) : (R.line i).idxFun = (R.line j).idxFun := by
    funext s
    rcases normalized_section_dichotomy source x lines R s with hconst | hline
    · obtain ⟨q, hq, hsec⟩ := hconst
      obtain ⟨a, h0, h1, h2⟩ := constant_section_status source x lines R hp s q hq hsec
      fin_cases i <;> fin_cases j <;> simp_all
    · have hrow := congrFun (each_nonconstant_eq s hline)
      have hmove (k : Alphabet) : (R.line k).idxFun s = none :=
        (moving_iff_sectionPoint_eq source x (R.line k) (R.point k) (hp k) s).2 <| by
          have := hrow k
          fin_cases k <;> simp_all [base]
      rw [hmove i, hmove j]
  constructor
  · exact Erdos847FiniteArch.line_eq_of_idxFun_eq (hidx 0 1)
  · exact Erdos847FiniteArch.line_eq_of_idxFun_eq (hidx 0 2)

def NormalizedConfined
    (R : NormalizedRawQuasiline source x lines l) : Prop :=
  ∃ (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
      (p : Alphabet → P),
    IsQuasiline source.embed p ∧
      ∀ i, l (R.perm i) = standardCopy source x lines U hU (p i)

theorem isQuasiline_reindex {D Q : Type*}
    (embed : Q → D → Alphabet) (q : Alphabet → Q)
    (hq : IsQuasiline embed q) (σ : Equiv.Perm Alphabet) :
    IsQuasiline embed (fun i => q (σ i)) := by
  constructor
  · intro i j hij
    exact σ.injective (hq.1 hij)
  · intro d
    rcases hq.2 d with ⟨a, ha⟩ | hm
    · exact Or.inl ⟨a, fun i => ha (σ i)⟩
    · exact Or.inr (hm.comp σ.injective)

/-- If every nonconstant section has the normalized base ordering, the raw
quasiline lies in the standard copy indexed by `R.line 0`. -/
theorem confined_of_all_nonconstant_base
    (R : NormalizedRawQuasiline source x lines l)
    (hall : ∀ s, IsQuasiline source.embed
      (normalizedSection source x lines R s) →
      normalizedSection source x lines R s =
        normalizedSection source x lines R R.coordinate) :
    NormalizedConfined source x lines R := by
  let base := normalizedSection source x lines R R.coordinate
  refine ⟨R.line 0, R.line_mem 0, base, R.source_section, ?_⟩
  intro i
  apply Subtype.ext
  rw [R.word_eq i]
  funext sc
  simp only [extendWord]
  congr 1
  rcases normalized_section_dichotomy source x lines R sc.1 with hconst | hline
  · obtain ⟨q, hq, hsec⟩ := hconst
    obtain ⟨f, hf, hval⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line 0) (R.point 0) q R.point_zero_not_fiber hq sc.1 (hsec 0)
    rw [show sectionPoint source x (R.line i) (R.point i) sc.1 = q from hsec i]
    simp [sectionPoint, hf, hval]
  · have hrow := hall sc.1 hline
    have hmove : (R.line 0).idxFun sc.1 = none :=
      (moving_iff_sectionPoint_eq source x (R.line 0) (R.point 0)
        R.point_zero_not_fiber sc.1).2 <| by
          have hh := congrFun hrow 0
          change sectionPoint source x (R.line 0) (R.point 0) sc.1 =
            sectionPoint source x (R.line 0) (R.point 0) R.coordinate at hh
          exact hh.trans R.section_zero
    have hh := congrFun hrow i
    change sectionPoint source x (R.line i) (R.point i) sc.1 = base i at hh
    rw [hh]
    simp [sectionPoint, hmove]

/-- Same-range part of Proposition 4.5.  Either all rows have the base
ordering and confinement is immediate, or the exact RRS tripod occurs. -/
theorem same_range_fiber_confined_or_tripod
    (R : NormalizedRawQuasiline source x lines l)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (hallRange : ∀ s,
      IsQuasiline source.embed (normalizedSection source x lines R s) →
      Set.range (normalizedSection source x lines R s) =
        Set.range (normalizedSection source x lines R R.coordinate)) :
    NormalizedConfined source x lines R ∨
      ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTripod U W Z := by
  classical
  let base := normalizedSection source x lines R R.coordinate
  by_cases hdiff : ∃ s, IsQuasiline source.embed
      (normalizedSection source x lines R s) ∧
      normalizedSection source x lines R s ≠ base
  · obtain ⟨t, htline, htdiff⟩ := hdiff
    let row := normalizedSection source x lines R t
    have hb0 : base 0 = R.point 0 := R.section_zero
    have hb1 : base 1 = R.point 1 := R.section_one
    have hbaseRange : Set.range base =
        ({R.point 0, R.point 1, base 2} : Set P) := by
      rw [range_fin3, hb0, hb1]
    have htcoords : row 0 ≠ R.point 0 ∨ row 1 ≠ R.point 1 ∨ row 2 ≠ base 2 := by
      by_contra h
      push Not at h
      apply htdiff
      funext i
      fin_cases i
      · exact h.1.trans hb0.symm
      · exact h.2.1.trans hb1.symm
      · exact h.2.2
    have htNormal := Erdos847ConfinementKernels.same_range_normal_forms
      R.point_zero_not_fiber R.point_one_not_fiber htline.1
      (section_admissible source x lines R t)
      (by rw [hallRange t htline, hbaseRange]) htcoords
    rcases htNormal with hA | hB
    · have hp2 : source.proj (R.point 2) ≠ x := by
        rw [hA.2.2.2]
        exact R.point_zero_not_fiber
      have hpAll : ∀ i, source.proj (R.point i) ≠ x := by
        intro i
        fin_cases i
        · exact R.point_zero_not_fiber
        · exact R.point_one_not_fiber
        · exact hp2
      let a : MusicFiber source x := ⟨base 2, hfiber⟩
      have table : ∀ s,
          (∃ c, (R.line 0).idxFun s = some c ∧
            (R.line 1).idxFun s = some c ∧ (R.line 2).idxFun s = some c) ∨
          ((R.line 0).idxFun s = none ∧ (R.line 1).idxFun s = none ∧
            (R.line 2).idxFun s = some a) ∨
          ((R.line 0).idxFun s = some a ∧ (R.line 1).idxFun s = none ∧
            (R.line 2).idxFun s = none) := by
        intro s
        rcases normalized_section_dichotomy source x lines R s with hc | hl
        · obtain ⟨q, hq, hs⟩ := hc
          obtain ⟨c, h0, h1, h2⟩ := constant_section_status source x lines R
            hpAll s q hq hs
          exact Or.inl ⟨c, h0, h1, h2⟩
        · have hrange := hallRange s hl
          by_cases heq : normalizedSection source x lines R s = base
          · right; left
            have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
              (R.point 0) R.point_zero_not_fiber s).2 <| by
                have hh := congrFun heq 0
                change sectionPoint source x (R.line 0) (R.point 0) s = base 0 at hh
                exact hh.trans hb0
            have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
              (R.point 1) R.point_one_not_fiber s).2 <| by
                have hh := congrFun heq 1
                change sectionPoint source x (R.line 1) (R.point 1) s = base 1 at hh
                exact hh.trans hb1
            obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
              (R.line 2) (R.point 2) (base 2) hp2 hfiber s (congrFun heq 2)
            have hfa : f = a := Subtype.ext hv
            exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
          · have hcoords : normalizedSection source x lines R s 0 ≠ R.point 0 ∨
                normalizedSection source x lines R s 1 ≠ R.point 1 ∨
                normalizedSection source x lines R s 2 ≠ base 2 := by
              by_contra h
              push Not at h
              apply heq
              funext i
              fin_cases i
              · exact h.1.trans hb0.symm
              · exact h.2.1.trans hb1.symm
              · exact h.2.2
            have hn := Erdos847ConfinementKernels.same_range_normal_forms
              R.point_zero_not_fiber R.point_one_not_fiber hl.1
              (section_admissible source x lines R s)
              (by rw [hrange, hbaseRange]) hcoords
            rcases hn with hn | hn
            · right; right
              obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
                (R.line 0) (R.point 0) (base 2) R.point_zero_not_fiber hfiber s hn.1
              have hfa : f = a := Subtype.ext hv
              have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
                (R.point 1) R.point_one_not_fiber s).2 hn.2.1
              have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
                (R.point 2) hp2 s).2 (hn.2.2.1.trans hA.2.2.2.symm)
              exact ⟨by simpa [hfa] using hf, hm1, hm2⟩
            · exfalso
              apply (by decide : (1 : Alphabet) ≠ 0)
              apply R.source_section.1
              change base 1 = base 0
              exact hb1.trans ((hn.2.2.2.symm.trans hA.2.2.2).trans hb0.symm)
      have hS : (R.line 0).idxFun R.coordinate = none ∧
          (R.line 1).idxFun R.coordinate = none ∧
          (R.line 2).idxFun R.coordinate = some a := by
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber R.coordinate).2 R.section_zero
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber R.coordinate).2 R.section_one
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 2) (R.point 2) (base 2) hp2 hfiber R.coordinate rfl
        have hfa : f = a := Subtype.ext hv
        exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
      have hT : (R.line 0).idxFun t = some a ∧
          (R.line 1).idxFun t = none ∧ (R.line 2).idxFun t = none := by
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 0) (R.point 0) (base 2) R.point_zero_not_fiber hfiber t hA.1
        have hfa : f = a := Subtype.ext hv
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber t).2 hA.2.1
        have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
          (R.point 2) hp2 t).2 (hA.2.2.1.trans hA.2.2.2.symm)
        exact ⟨by simpa [hfa] using hf, hm1, hm2⟩
      right
      exact ⟨R.line 0, R.line 1, R.line 2, R.line_mem 0, R.line_mem 1,
        R.line_mem 2, Erdos847FiniteArch.isRawTripod_of_section_table
          (R.line 0) (R.line 1) (R.line 2) a R.coordinate t table hS hT⟩
    · -- The second normal form is the same tripod with lines 0 and 1 exchanged.
      have hp2 : source.proj (R.point 2) ≠ x := by
        rw [hB.2.2.2]
        exact R.point_one_not_fiber
      have hpAll : ∀ i, source.proj (R.point i) ≠ x := by
        intro i
        fin_cases i
        · exact R.point_zero_not_fiber
        · exact R.point_one_not_fiber
        · exact hp2
      let a : MusicFiber source x := ⟨base 2, hfiber⟩
      have table : ∀ s,
          (∃ c, (R.line 1).idxFun s = some c ∧
            (R.line 0).idxFun s = some c ∧ (R.line 2).idxFun s = some c) ∨
          ((R.line 1).idxFun s = none ∧ (R.line 0).idxFun s = none ∧
            (R.line 2).idxFun s = some a) ∨
          ((R.line 1).idxFun s = some a ∧ (R.line 0).idxFun s = none ∧
            (R.line 2).idxFun s = none) := by
        intro s
        rcases normalized_section_dichotomy source x lines R s with hc | hl
        · obtain ⟨q, hq, hs⟩ := hc
          obtain ⟨c, h0, h1, h2⟩ := constant_section_status source x lines R
            hpAll s q hq hs
          exact Or.inl ⟨c, h1, h0, h2⟩
        · have hrange := hallRange s hl
          by_cases heq : normalizedSection source x lines R s = base
          · right; left
            have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
              (R.point 1) R.point_one_not_fiber s).2 <| by
                have hh := congrFun heq 1
                change sectionPoint source x (R.line 1) (R.point 1) s = base 1 at hh
                exact hh.trans hb1
            have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
              (R.point 0) R.point_zero_not_fiber s).2 <| by
                have hh := congrFun heq 0
                change sectionPoint source x (R.line 0) (R.point 0) s = base 0 at hh
                exact hh.trans hb0
            obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
              (R.line 2) (R.point 2) (base 2) hp2 hfiber s (congrFun heq 2)
            have hfa : f = a := Subtype.ext hv
            exact ⟨hm1, hm0, by simpa [hfa] using hf⟩
          · have hcoords : normalizedSection source x lines R s 0 ≠ R.point 0 ∨
                normalizedSection source x lines R s 1 ≠ R.point 1 ∨
                normalizedSection source x lines R s 2 ≠ base 2 := by
              by_contra h
              push Not at h
              apply heq
              funext i
              fin_cases i
              · exact h.1.trans hb0.symm
              · exact h.2.1.trans hb1.symm
              · exact h.2.2
            have hn := Erdos847ConfinementKernels.same_range_normal_forms
              R.point_zero_not_fiber R.point_one_not_fiber hl.1
              (section_admissible source x lines R s)
              (by rw [hrange, hbaseRange]) hcoords
            rcases hn with hn | hn
            · exfalso
              apply (by decide : (0 : Alphabet) ≠ 1)
              apply R.source_section.1
              change base 0 = base 1
              exact hb0.trans ((hn.2.2.2.symm.trans hB.2.2.2).trans hb1.symm)
            · right; right
              obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
                (R.line 1) (R.point 1) (base 2) R.point_one_not_fiber hfiber s hn.2.1
              have hfa : f = a := Subtype.ext hv
              have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
                (R.point 0) R.point_zero_not_fiber s).2 hn.1
              have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
                (R.point 2) hp2 s).2 (hn.2.2.1.trans hB.2.2.2.symm)
              exact ⟨by simpa [hfa] using hf, hm0, hm2⟩
      have hS : (R.line 1).idxFun R.coordinate = none ∧
          (R.line 0).idxFun R.coordinate = none ∧
          (R.line 2).idxFun R.coordinate = some a := by
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber R.coordinate).2 R.section_one
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber R.coordinate).2 R.section_zero
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 2) (R.point 2) (base 2) hp2 hfiber R.coordinate rfl
        have hfa : f = a := Subtype.ext hv
        exact ⟨hm1, hm0, by simpa [hfa] using hf⟩
      have hT : (R.line 1).idxFun t = some a ∧
          (R.line 0).idxFun t = none ∧ (R.line 2).idxFun t = none := by
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 1) (R.point 1) (base 2) R.point_one_not_fiber hfiber t hB.2.1
        have hfa : f = a := Subtype.ext hv
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber t).2 hB.1
        have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
          (R.point 2) hp2 t).2 (hB.2.2.1.trans hB.2.2.2.symm)
        exact ⟨by simpa [hfa] using hf, hm0, hm2⟩
      right
      exact ⟨R.line 1, R.line 0, R.line 2, R.line_mem 1, R.line_mem 0,
        R.line_mem 2, Erdos847FiniteArch.isRawTripod_of_section_table
          (R.line 1) (R.line 0) (R.line 2) a R.coordinate t table hS hT⟩
  · left
    apply confined_of_all_nonconstant_base source x lines R
    intro s hs
    by_contra hne
    exact hdiff ⟨s, hs, hne⟩

/-- The first of the two distinct-range normal forms produces the exact
outer-line triangle.  Linearity of the base graph rules out the complementary
fiber mask for every later section. -/
theorem distinct_range_zero_triangle
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (t : N)
    (htline : IsQuasiline source.embed
      (normalizedSection source x lines R t))
    (b : P)
    (hb : source.proj b = x)
    (hba : b ≠ normalizedSection source x lines R R.coordinate 2)
    (ht0 : normalizedSection source x lines R t 0 = R.point 0)
    (ht1 : normalizedSection source x lines R t 1 = b)
    (ht2 : normalizedSection source x lines R t 2 = R.point 2) :
    ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTriangle U W Z := by
  classical
  let base := normalizedSection source x lines R R.coordinate
  let row := normalizedSection source x lines R t
  have hb0 : base 0 = R.point 0 := R.section_zero
  have hb1 : base 1 = R.point 1 := R.section_one
  have htMaps := source.quasiline_maps_edge row htline
  have htProjInj := mapsOntoEdge_proj_injective source htMaps
  have hp2 : source.proj (R.point 2) ≠ x := by
    intro hp2
    apply (by decide : (1 : Alphabet) ≠ 2)
    apply htProjInj
    simpa [row, ht1, ht2, hb, hp2]
  have hpAll : ∀ i, source.proj (R.point i) ≠ x := by
    intro i
    fin_cases i
    · exact R.point_zero_not_fiber
    · exact R.point_one_not_fiber
    · exact hp2
  have hproj12 : source.proj (R.point 1) = source.proj (R.point 2) := by
    have h := linear_forces_third_projection source hlinear base row
      (source.quasiline_maps_edge base R.source_section) htMaps
      (by simpa [base, row, hb0, ht0])
      (by simpa [base, row, ht1, hb, hfiber])
    simpa [base, row, hb1, ht2] using h
  let aa : MusicFiber source x := ⟨base 2, hfiber⟩
  let bb : MusicFiber source x := ⟨b, hb⟩
  have hab : aa ≠ bb := by
    intro h
    apply hba
    exact congrArg Subtype.val h.symm
  have table : ∀ s,
      (∃ c, (R.line 0).idxFun s = some c ∧
        (R.line 1).idxFun s = some c ∧ (R.line 2).idxFun s = some c) ∨
      ((R.line 0).idxFun s = none ∧ (R.line 1).idxFun s = none ∧
        (R.line 2).idxFun s = some aa) ∨
      ((R.line 0).idxFun s = none ∧ (R.line 1).idxFun s = some bb ∧
        (R.line 2).idxFun s = none) := by
    intro s
    rcases normalized_section_dichotomy source x lines R s with hc | hl
    · obtain ⟨q, hq, hs⟩ := hc
      obtain ⟨c, h0, h1, h2⟩ := constant_section_status source x lines R
        hpAll s q hq hs
      exact Or.inl ⟨c, h0, h1, h2⟩
    · let q := normalizedSection source x lines R s
      have hqMaps := source.quasiline_maps_edge q hl
      have hqProjInj := mapsOntoEdge_proj_injective source hqMaps
      have hforms := Erdos847ConfinementKernels.normalized_row_four_forms
        (section_admissible source x lines R s)
        (by
          intro i j hi hj
          exact source_section_atMostOne_fiber source x lines R s hl hi hj)
      rcases hforms with hF0 | hF1 | hF2 | hM
      · exfalso
        apply (by decide : (1 : Alphabet) ≠ 2)
        apply hqProjInj
        simpa [q, hF0.2.1, hF0.2.2] using hproj12
      · right; right
        have hRange : Set.range q = Set.range row :=
          combinatorialLine_range_eq_of_two_points source.embed source.embed_injective
            q row (source.quasiline_is_line q hl)
            (source.quasiline_is_line row htline)
            (by decide : (0 : Alphabet) ≠ 2)
            (hF1.1.trans ht0.symm) (hF1.2.2.trans ht2.symm)
        have hqb : q 1 = b := by
          have hm : q 1 ∈ Set.range row := by
            rw [← hRange]
            exact Set.mem_range_self 1
          rw [range_fin3] at hm
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
          rcases hm with h | h | h
          · exfalso
            apply R.point_zero_not_fiber
            have hxrow : source.proj (row 0) = x := by
              rw [← h]
              exact hF1.2.1
            simpa [row, ht0] using hxrow
          · simpa [q, row] using h.trans ht1
          · exfalso
            apply hp2
            have hxrow : source.proj (row 2) = x := by
              rw [← h]
              exact hF1.2.1
            simpa [row, ht2] using hxrow
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber s).2 hF1.1
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 1) (R.point 1) b R.point_one_not_fiber hb s hqb
        have hfb : f = bb := Subtype.ext hv
        have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
          (R.point 2) hp2 s).2 hF1.2.2
        exact ⟨hm0, by simpa [hfb] using hf, hm2⟩
      · right; left
        have hRange : Set.range q = Set.range base :=
          combinatorialLine_range_eq_of_two_points source.embed source.embed_injective
            q base (source.quasiline_is_line q hl)
            (source.quasiline_is_line base R.source_section)
            (by decide : (0 : Alphabet) ≠ 1)
            (hF2.1.trans hb0.symm) (hF2.2.1.trans hb1.symm)
        have hqa : q 2 = base 2 := by
          have hm : q 2 ∈ Set.range base := by
            rw [← hRange]
            exact Set.mem_range_self 2
          rw [range_fin3] at hm
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
          rcases hm with h | h | h
          · exfalso
            apply R.point_zero_not_fiber
            rw [← hb0, ← h]
            exact hF2.2.2
          · exfalso
            apply R.point_one_not_fiber
            rw [← hb1, ← h]
            exact hF2.2.2
          · simpa [q, base] using h
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber s).2 hF2.1
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber s).2 hF2.2.1
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 2) (R.point 2) (base 2) hp2 hfiber s hqa
        have hfa : f = aa := Subtype.ext hv
        exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
      · exfalso
        have hRange : Set.range q = Set.range base :=
          combinatorialLine_range_eq_of_two_points source.embed source.embed_injective
            q base (source.quasiline_is_line q hl)
            (source.quasiline_is_line base R.source_section)
            (by decide : (0 : Alphabet) ≠ 1)
            (hM.1.trans hb0.symm) (hM.2.1.trans hb1.symm)
        have hm : q 2 ∈ Set.range base := by
          rw [← hRange]
          exact Set.mem_range_self 2
        rw [range_fin3] at hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with h | h | h
        · apply (by decide : (2 : Alphabet) ≠ 0)
          apply hl.1
          exact h.trans (hb0.trans hM.1.symm)
        · apply (by decide : (2 : Alphabet) ≠ 1)
          apply hl.1
          exact h.trans (hb1.trans hM.2.1.symm)
        · apply hp2
          have hxq : source.proj (q 2) = x := by
            rw [h]
            exact hfiber
          simpa [q, hM.2.2] using hxq
  have hS : (R.line 0).idxFun R.coordinate = none ∧
      (R.line 1).idxFun R.coordinate = none ∧
      (R.line 2).idxFun R.coordinate = some aa := by
    have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
      (R.point 0) R.point_zero_not_fiber R.coordinate).2 R.section_zero
    have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
      (R.point 1) R.point_one_not_fiber R.coordinate).2 R.section_one
    obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line 2) (R.point 2) (base 2) hp2 hfiber R.coordinate rfl
    have hfa : f = aa := Subtype.ext hv
    exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
  have hT : (R.line 0).idxFun t = none ∧
      (R.line 1).idxFun t = some bb ∧ (R.line 2).idxFun t = none := by
    have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
      (R.point 0) R.point_zero_not_fiber t).2 ht0
    obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line 1) (R.point 1) b R.point_one_not_fiber hb t ht1
    have hfb : f = bb := Subtype.ext hv
    have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
      (R.point 2) hp2 t).2 ht2
    exact ⟨hm0, by simpa [hfb] using hf, hm2⟩
  exact ⟨R.line 0, R.line 1, R.line 2, R.line_mem 0, R.line_mem 1, R.line_mem 2,
    Erdos847FiniteArch.isRawTriangle_of_section_table
      (R.line 0) (R.line 1) (R.line 2) aa bb R.coordinate t hab table hS hT⟩

/-- The symmetric distinct-range normal form reduces to
`distinct_range_zero_triangle` by swapping the first two ternary indices. -/
theorem distinct_range_one_triangle
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (t : N)
    (htline : IsQuasiline source.embed
      (normalizedSection source x lines R t))
    (b : P)
    (hb : source.proj b = x)
    (hba : b ≠ normalizedSection source x lines R R.coordinate 2)
    (ht0 : normalizedSection source x lines R t 0 = b)
    (ht1 : normalizedSection source x lines R t 1 = R.point 1)
    (ht2 : normalizedSection source x lines R t 2 = R.point 2) :
    ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTriangle U W Z := by
  let τ : Equiv.Perm Alphabet := Equiv.swap 0 1
  have hτ2 : τ 2 = 2 := by
    simp [τ, Equiv.swap_apply_of_ne_of_ne]
  let S : NormalizedRawQuasiline source x lines l := {
    perm := τ.trans R.perm
    line := fun i => R.line (τ i)
    point := fun i => R.point (τ i)
    coordinate := R.coordinate
    line_mem := fun i => R.line_mem (τ i)
    word_eq := by
      intro i
      simpa [τ] using R.word_eq (τ i)
    outer_quasiline := by
      simpa using isQuasiline_reindex (rawEmbed source x lines)
        (fun i => l (R.perm i)) R.outer_quasiline τ
    source_section := by
      simpa using isQuasiline_reindex source.embed
        (fun i => sectionPoint source x (R.line i) (R.point i) R.coordinate)
        R.source_section τ
    point_zero_not_fiber := by simpa [τ] using R.point_one_not_fiber
    point_one_not_fiber := by simpa [τ] using R.point_zero_not_fiber
    section_zero := by simpa [τ] using R.section_one
    section_one := by simpa [τ] using R.section_zero }
  exact distinct_range_zero_triangle source x lines S hlinear
    (by simpa [normalizedSection, S, hτ2] using hfiber) t
    (by
      have hs := isQuasiline_reindex source.embed
        (normalizedSection source x lines R t) htline τ
      simpa [normalizedSection, S] using hs)
    b hb
    (by simpa [normalizedSection, S, hτ2] using hba)
    (by simpa [normalizedSection, S, τ] using ht1)
    (by simpa [normalizedSection, S, τ] using ht0)
    (by simpa [normalizedSection, S, hτ2] using ht2)

/-- The complete distinct-range branch: the elementary ternary classifier
chooses one of the two orientations proved above. -/
theorem distinct_range_fiber_triangle
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (t : N)
    (htline : IsQuasiline source.embed
      (normalizedSection source x lines R t))
    (htrange : Set.range (normalizedSection source x lines R t) ≠
      Set.range (normalizedSection source x lines R R.coordinate)) :
    ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTriangle U W Z := by
  let base := normalizedSection source x lines R R.coordinate
  let row := normalizedSection source x lines R t
  have hb0 : base 0 = R.point 0 := R.section_zero
  have hb1 : base 1 = R.point 1 := R.section_one
  have hp01 : R.point 0 ≠ R.point 1 := by
    intro h
    apply (by decide : (0 : Alphabet) ≠ 1)
    apply R.source_section.1
    exact R.section_zero.trans (h.trans R.section_one.symm)
  have hinter : (Set.range row ∩
      ({R.point 0, R.point 1, base 2} : Set P)).Subsingleton := by
    have hi := combinatorialLine_range_inter_subsingleton source.embed
      source.embed_injective row base
      (source.quasiline_is_line row htline)
      (source.quasiline_is_line base R.source_section) htrange
    simpa [range_fin3, hb0, hb1] using hi
  have hforms := Erdos847ConfinementKernels.distinct_range_normal_forms
    hp01 R.point_zero_not_fiber R.point_one_not_fiber
    (section_admissible source x lines R t)
    (by
      intro i j hi hj
      exact source_section_atMostOne_fiber source x lines R t htline hi hj)
    hinter
  rcases hforms with ⟨b, hb, hba, ht0, ht1, ht2⟩ |
      ⟨b, hb, hba, ht0, ht1, ht2⟩
  · exact distinct_range_zero_triangle source x lines R hlinear hfiber t htline
      b hb hba ht0 ht1 ht2
  · exact distinct_range_one_triangle source x lines R hlinear hfiber t htline
      b hb hba ht0 ht1 ht2

/-- Proposition 4.5 in normalized form, specialized to a linear ternary base
graph.  The only alternatives to confinement are an exact RRS tripod or
triangle, both excluded by the sparse selected line system. -/
theorem normalized_confined_of_sparse_linear
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (htripod : RawLineSystemHasNoTripod lines)
    (htriangle : RawLineSystemHasNoTriangle lines) :
    NormalizedConfined source x lines R := by
  let base := normalizedSection source x lines R R.coordinate
  by_cases hfiber : source.proj (base 2) = x
  · by_cases hall : ∀ s,
        IsQuasiline source.embed (normalizedSection source x lines R s) →
        Set.range (normalizedSection source x lines R s) = Set.range base
    · rcases same_range_fiber_confined_or_tripod source x lines R hfiber hall with
        hconf | ⟨U, W, Z, hU, hW, hZ, htrip⟩
      · exact hconf
      · exact False.elim (htripod hU hW hZ htrip)
    · push Not at hall
      obtain ⟨t, htline, htrange⟩ := hall
      obtain ⟨U, W, Z, hU, hW, hZ, htri⟩ :=
        distinct_range_fiber_triangle source x lines R hlinear hfiber t htline htrange
      exact False.elim (htriangle hU hW hZ htri)
  · have hlines := outside_third_lines_equal source x lines R hfiber
    have hb2 : base 2 = R.point 2 := by
      apply (sectionPoint_mem_fiber_or_eq source x (R.line 2) (R.point 2)
        R.coordinate).resolve_left
      exact hfiber
    have hbase : base = R.point := by
      funext i
      fin_cases i
      · exact R.section_zero
      · exact R.section_one
      · exact hb2
    refine ⟨R.line 0, R.line_mem 0, R.point, ?_, ?_⟩
    · rw [← hbase]
      exact R.source_section
    · intro i
      have hli : R.line i = R.line 0 := by
        fin_cases i
        · rfl
        · exact hlines.1.symm
        · exact hlines.2.symm
      apply Subtype.ext
      simpa [standardCopy, hli] using R.word_eq i

/-- Concrete confinement theorem for the literal raw partite amalgamation. -/
theorem raw_everyQuasilineConfined_of_sparse_linear
    (hlinear : G.Linear)
    (htripod : RawLineSystemHasNoTripod lines)
    (htriangle : RawLineSystemHasNoTriangle lines) :
    EveryQuasilineConfined source (rawAmalgamationData source x lines) := by
  intro q hq
  obtain ⟨R⟩ := normalize_raw_quasiline source x lines q hq
  obtain ⟨U, hU, p, hp, hcopy⟩ :=
    normalized_confined_of_sparse_linear source x lines R hlinear htripod htriangle
  let p' : Alphabet → P := fun i => p (R.perm.symm i)
  refine ⟨⟨U, hU⟩, p', isQuasiline_reindex source.embed p hp R.perm.symm, ?_⟩
  intro i
  have h := hcopy (R.perm.symm i)
  simpa [p', rawAmalgamationData] using h

/-- The FiberExtension-ready picture supplied by the actual raw amalgamation
once the selected Hales--Jewett lines have no tripod and no triangle. -/
noncomputable def rawAmalgamationPicture_of_sparse_linear
    (hlinear : G.Linear)
    (htripod : RawLineSystemHasNoTripod lines)
    (htriangle : RawLineSystemHasNoTriangle lines) :
    Picture G (RawAmalgamPoint source x lines) (N × C) :=
  amalgamationPicture source (rawAmalgamationData source x lines)
    (raw_everyQuasilineConfined_of_sparse_linear source x lines
      hlinear htripod htriangle)

end NormalizedSections

end Erdos847Confinement
