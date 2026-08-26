import ErdosProblems.Erdos1123.CountableExtension
import ErdosProblems.Erdos1123.CouplingIsomorphism
import ErdosProblems.Erdos1123.CHEnumeration

/-! # CH back-and-forth for atomless finite-block presentations -/

namespace Erdos1123

open Filter
open scoped Topology

/-- The concrete conditions required of a finite-block presentation. -/
structure BlockStructure (W : WeightSequence ℕ) where
  disjoint : ∀ n m, n ≠ m → Disjoint (W.support n) (W.support m)
  atomBound : ℕ → ℝ
  atomBound_nonneg : ∀ n, 0 ≤ atomBound n
  atomBound_tendsto : Tendsto atomBound atTop (𝓝 0)
  weight_le : ∀ n x, x ∈ W.support n → W.weight n x ≤ atomBound n
  normalized : Tendsto (W.mass Set.univ) atTop (𝓝 1)

namespace Coupling

variable {W V : WeightSequence ℕ}

/-- The two constant pairs form the initial coupling. -/
def initial (hW : BlockStructure W) (hV : BlockStructure V) : Coupling W V where
  algebra := ⊥
  matching := by
    intro p hp
    rcases BooleanSubalgebra.mem_bot.mp hp with rfl | rfl
    · change Tendsto (fun n => W.mass ∅ n - V.mass ∅ n) atTop (𝓝 0)
      simpa only [WeightSequence.mass_empty, sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · change Tendsto (fun n => W.mass Set.univ n - V.mass Set.univ n) atTop (𝓝 0)
      simpa only [sub_self] using hW.normalized.sub hV.normalized

instance initial_countable (hW : BlockStructure W) (hV : BlockStructure V) :
    Countable (initial hW hV).algebra := by
  have h : ((initial hW hV).algebra : Set (Set ℕ × Set ℕ)).Countable :=
    (Set.countable_singleton ⊤).insert ⊥
  exact h.to_subtype

/-- The empty relation is allowed while forming unions; every nonempty stage
is the carrier of an actual coupling. -/
def GoodRelation (R : Set (Set ℕ × Set ℕ)) : Prop :=
  R = ∅ ∨ ∃ C : Coupling W V, (C.algebra : Set (Set ℕ × Set ℕ)) = R

theorem mem_iff_carrier_eq (C : Coupling W V) {R : Set (Set ℕ × Set ℕ)}
    (hC : (C.algebra : Set (Set ℕ × Set ℕ)) = R) (p : Set ℕ × Set ℕ) :
    p ∈ C.algebra ↔ p ∈ R := by
  change p ∈ (C.algebra : Set (Set ℕ × Set ℕ)) ↔ p ∈ R
  rw [hC]

theorem goodRelation_of_mem {R : Set (Set ℕ × Set ℕ)} (hR : GoodRelation (W := W) (V := V) R)
    {p : Set ℕ × Set ℕ} (hp : p ∈ R) :
    ∃ C : Coupling W V, (C.algebra : Set (Set ℕ × Set ℕ)) = R := by
  rcases hR with h | h
  · exact False.elim (Set.notMem_empty p (h ▸ hp))
  · exact h

theorem goodRelation_iUnion {κ : Type*} (R : κ → Set (Set ℕ × Set ℕ))
    (hDirected : Directed (· ⊆ ·) R) (hGood : ∀ i, GoodRelation (W := W) (V := V) (R i)) :
    GoodRelation (W := W) (V := V) (⋃ i, R i) := by
  classical
  let U := ⋃ i, R i
  by_cases hempty : U = ∅
  · exact Or.inl hempty
  have hbot : (⊥ : Set ℕ × Set ℕ) ∈ U := by
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨C, hC⟩ := goodRelation_of_mem (hGood i) hi
    exact Set.mem_iUnion.mpr ⟨i, hC ▸ C.algebra.bot_mem⟩
  have hsup {p q : Set ℕ × Set ℕ} (hp : p ∈ U) (hq : q ∈ U) : p ⊔ q ∈ U := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    obtain ⟨C, hC⟩ := goodRelation_of_mem (hGood k) (hik hi)
    exact Set.mem_iUnion.mpr ⟨k, (C.mem_iff_carrier_eq hC _).mp
      (C.algebra.sup_mem ((C.mem_iff_carrier_eq hC _).mpr (hik hi))
        ((C.mem_iff_carrier_eq hC _).mpr (hjk hj)))⟩
  have hinf {p q : Set ℕ × Set ℕ} (hp : p ∈ U) (hq : q ∈ U) : p ⊓ q ∈ U := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    obtain ⟨C, hC⟩ := goodRelation_of_mem (hGood k) (hik hi)
    exact Set.mem_iUnion.mpr ⟨k, (C.mem_iff_carrier_eq hC _).mp
      (C.algebra.inf_mem ((C.mem_iff_carrier_eq hC _).mpr (hik hi))
        ((C.mem_iff_carrier_eq hC _).mpr (hjk hj)))⟩
  have hcompl {p : Set ℕ × Set ℕ} (hp : p ∈ U) : pᶜ ∈ U := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨C, hC⟩ := goodRelation_of_mem (hGood i) hi
    exact Set.mem_iUnion.mpr ⟨i, (C.mem_iff_carrier_eq hC _).mp
      (C.algebra.compl_mem ((C.mem_iff_carrier_eq hC _).mpr hi))⟩
  let L : BooleanSubalgebra (Set ℕ × Set ℕ) :=
    { carrier := U
      supClosed' := fun _ hp _ hq => hsup hp hq
      infClosed' := fun _ hp _ hq => hinf hp hq
      compl_mem' := hcompl
      bot_mem' := hbot }
  have hmatch (p : Set ℕ × Set ℕ) (hp : p ∈ L) :
      Tendsto (fun n => W.mass p.1 n - V.mass p.2 n) atTop (𝓝 0) := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨C, hC⟩ := goodRelation_of_mem (hGood i) hi
    exact C.matching p ((C.mem_iff_carrier_eq hC p).mpr hi)
  exact Or.inr ⟨⟨L, hmatch⟩, rfl⟩

theorem countable_forth_and_back (C : Coupling W V) [Countable C.algebra]
    (hW : BlockStructure W) (hV : BlockStructure V) (A : Set ℕ) :
    ∃ D : Coupling W V, Countable D.algebra ∧ C.algebra ≤ D.algebra ∧
      (∃ B, (A, B) ∈ D.algebra) ∧ (∃ B, (B, A) ∈ D.algebra) := by
  obtain ⟨D, hDc, hCD, B, hAB⟩ := C.exists_countable_extension hV.disjoint hV.atomBound
    hV.atomBound_nonneg hV.atomBound_tendsto hV.weight_le A
  let : Countable D.algebra := hDc
  obtain ⟨E, hEc, hDE, B', hAB'⟩ := D.symm.exists_countable_extension hW.disjoint hW.atomBound
    hW.atomBound_nonneg hW.atomBound_tendsto hW.weight_le A
  let : Countable E.algebra := hEc
  refine ⟨E.symm, inferInstance, ?_, ⟨B, ?_⟩, ⟨B', ?_⟩⟩
  · intro p hp
    exact hDE (hCD hp)
  · exact hDE hAB
  · exact hAB'

/-- CH produces a coupling whose two coordinate projections are surjective. -/
theorem exists_total_of_ch (hCH : ContinuumHypothesis)
    (hW : BlockStructure W) (hV : BlockStructure V) :
    ∃ C : Coupling W V, (∀ A, ∃ B, (A, B) ∈ C.algebra) ∧
      (∀ B, ∃ A, (A, B) ∈ C.algebra) := by
  let Good := GoodRelation (W := W) (V := V)
  let Requirement (A : Set ℕ) (R : Set (Set ℕ × Set ℕ)) :=
    (∃ B, (A, B) ∈ R) ∧ (∃ B, (B, A) ∈ R)
  have hExtend (R : Set (Set ℕ × Set ℕ)) (hc : R.Countable) (hg : Good R) (A : Set ℕ) :
      ∃ T, T.Countable ∧ Good T ∧ R ⊆ T ∧ Requirement A T := by
    have hC : ∃ C : Coupling W V, Countable C.algebra ∧ R ⊆ C.algebra := by
      rcases hg with hr | ⟨C, hC⟩
      · exact ⟨initial hW hV, inferInstance, hr ▸ Set.empty_subset _⟩
      · refine ⟨C, ?_, hC.symm ▸ Set.Subset.refl R⟩
        exact (hC.symm ▸ hc).to_subtype
    obtain ⟨C, hCc, hRC⟩ := hC
    let : Countable C.algebra := hCc
    obtain ⟨D, hDc, hCD, hf, hb⟩ := C.countable_forth_and_back hW hV A
    let : Countable D.algebra := hDc
    exact ⟨D.algebra, Set.to_countable _, Or.inr ⟨D, rfl⟩, hRC.trans hCD, hf, hb⟩
  obtain ⟨R, hR, hReq⟩ := exists_good_meeting_all_sets hCH Good Requirement
    ⟨∅, Set.countable_empty, Or.inl rfl⟩ goodRelation_iUnion
    (by
      intro A s t h hreq
      obtain ⟨⟨B, hB⟩, ⟨B', hB'⟩⟩ := hreq
      exact ⟨⟨B, h hB⟩, ⟨B', h hB'⟩⟩) hExtend
  obtain ⟨B, hB⟩ := (hReq ∅).1
  obtain ⟨C, hC⟩ := goodRelation_of_mem hR hB
  refine ⟨C, ?_, ?_⟩
  · intro A
    obtain ⟨B, hB⟩ := (hReq A).1
    exact ⟨B, (C.mem_iff_carrier_eq hC _).mpr hB⟩
  · intro A
    obtain ⟨B, hB⟩ := (hReq A).2
    exact ⟨B, (C.mem_iff_carrier_eq hC _).mpr hB⟩

end Coupling

/-- Under CH, any two asymptotically normalized finite-block quotients with vanishing largest
atoms are isomorphic. All extension and recursion lemmas are proved above. -/
theorem block_algebras_isomorphic_of_ch (hCH : ContinuumHypothesis)
    (W V : WeightSequence ℕ) (hW : BlockStructure W) (hV : BlockStructure V) :
    Nonempty (W.Algebra ≃o V.Algebra) := by
  obtain ⟨C, hd, hr⟩ := Coupling.exists_total_of_ch hCH hW hV
  exact ⟨C.quotientIso hd hr⟩

end Erdos1123
