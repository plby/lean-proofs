import ErdosProblems.Erdos118.LabelCoarsening

/-!
Intrinsic numerical cut indices depend only on ordinary words. Interior
parsing is unique, and annotation projection gives exactly the intrinsic
root/body label sets. This does not assert the remaining separation or
coloring conditions for a clear pair.
-/

namespace Erdos118.CutIndices

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening

theorem partial_bodies_injective {p q : G2} {n m : ℕ} {u v : List ℕ}
    (hu : u.length < n) (hv : v.length < m)
    (h : p.flatMap levelWord ++ n :: u = q.flatMap levelWord ++ m :: v) :
    p = q ∧ n = m ∧ u = v := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => exact ⟨rfl, List.cons.inj h⟩
    | cons a q =>
      have he : n = a.length ∧ u = a ++ (q.flatMap levelWord ++ m :: v) := by
        simpa only [List.flatMap_nil, List.nil_append, List.flatMap_cons, levelWord,
          List.cons_append, List.append_assoc, List.cons.injEq] using h
      have hlen := congrArg List.length he.2
      simp only [List.length_append, List.length_cons] at hlen
      omega
  | cons a p ih =>
    cases q with
    | nil =>
      have he : a.length = m ∧ a ++ (p.flatMap levelWord ++ n :: u) = v := by
        simpa only [List.flatMap_nil, List.nil_append, List.flatMap_cons, levelWord,
          List.cons_append, List.append_assoc, List.cons.injEq] using h
      have hlen := congrArg List.length he.2
      simp only [List.length_append, List.length_cons] at hlen
      omega
    | cons b q =>
      have he : a.length = b.length ∧
          a ++ (p.flatMap levelWord ++ n :: u) = b ++ (q.flatMap levelWord ++ m :: v) := by
        simpa only [List.flatMap_cons, levelWord, List.cons_append, List.append_assoc,
          List.cons.injEq] using h
      obtain ⟨hab, htail⟩ := List.append_inj he.2 he.1
      obtain ⟨hpq, hnm, huv⟩ := ih htail
      exact ⟨congrArg₂ List.cons hab hpq, hnm, huv⟩

theorem interior_word_injective : Function.Injective InteriorWords.Position.word := by
  intro P Q h
  have he : P.root = Q.root ∧
      P.done.flatMap levelWord ++ P.size :: P.entries =
        Q.done.flatMap levelWord ++ Q.size :: Q.entries := by
    simpa only [InteriorWords.Position.word, PartialWordResponses.partialWord,
      List.cons.injEq] using h
  obtain ⟨hd, hs, hu⟩ := partial_bodies_injective P.unfinished Q.unfinished he.2
  have hr := he.1
  cases P
  cases Q
  cases hr
  cases hd
  cases hs
  cases hu
  rfl

def Cut (S T : Stem) (i j : ℕ) : Prop :=
  ∃ y ∈ T.ordinary, ProperBelow y S ∧ ∃ P : InteriorWords.Position,
    P.word = PrefixRealization.below y S.ordinary ∧ P.done.length = i ∧ P.entries.length = j

def InteriorCuts (S T : Stem) : Prop :=
  ∀ y ∈ T.ordinary, ProperBelow y S →
    ∃ P : InteriorWords.Position, P.word = PrefixRealization.below y S.ordinary

structure ExactAnnotations (S T : Stem) : Prop where
  root : ∀ x, x ∈ S.rootLabel ↔ ∃ i j, Cut S T i j ∧ i + 1 = x
  body : ∀ i, ∀ hi : i < S.bodyLabels.length, ∀ j, j ∈ S.bodyLabels[i] ↔ Cut S T i j

theorem cut_congr {S S' T T' : Stem} (hS : S.ordinary = S'.ordinary)
    (hT : T.ordinary = T'.ordinary) (i j : ℕ) : Cut S T i j ↔ Cut S' T' i j := by
  simp only [Cut, ProperBelow, hS, hT]

theorem jointCut_indices {P : Pending} {Q : InteriorWords.Position} {S : Stem}
    {hS : S.done.length = S.root} {y : ℕ} (hP : JointCut P S hS y)
    (hQ : Q.word = PrefixRealization.below y S.ordinary) :
    Q.done.length = P.position.stem.done.length ∧ Q.entries.length = P.position.entries.length := by
  have he : Q = P.position.toInterior := interior_word_injective
    (hQ.trans (hP.ordinary.symm.trans P.position.toInterior_word.symm))
  subst Q
  simp [Position.toInterior]

theorem projection_interior {S T U : Stem} {hS : S.done.length = S.root}
    {hU : U.done.length = U.root} (A : Projection S hS T.ordinary U hU) : InteriorCuts U T := by
  intro y hy hproper
  have hp : ProperBelow y S := by simpa only [ProperBelow, A.ordinary] using hproper
  obtain ⟨P, hP⟩ := A.cuts y hy hp
  exact ⟨P.position.toInterior, P.position.toInterior_word.trans hP.ordinary⟩

theorem projection_root_exact {S T U : Stem} {hS : S.done.length = S.root}
    {hU : U.done.length = U.root} (A : Projection S hS T.ordinary U hU) (x : ℕ) :
    x ∈ U.rootLabel ↔ ∃ i j, Cut U T i j ∧ i + 1 = x := by
  constructor
  · intro hx
    obtain ⟨P, y, hy, hproper, hP, hindex⟩ := A.rootUsed x hx
    refine ⟨P.position.stem.done.length, P.position.entries.length,
      ⟨y, hy, ?_, P.position.toInterior, ?_, ?_, rfl⟩, hindex⟩
    · simpa only [ProperBelow, A.ordinary] using hproper
    · rw [Position.toInterior_word, A.ordinary]
      exact hP.ordinary
    · simp [Position.toInterior]
  · rintro ⟨i, j, ⟨y, hy, hproper, Q, hQ, hi, hj⟩, rfl⟩
    have hp : ProperBelow y S := by simpa only [ProperBelow, A.ordinary] using hproper
    obtain ⟨P, hP⟩ := A.cuts y hy hp
    have hindices := jointCut_indices hP hQ
    have hiP : i = P.position.stem.done.length := hi.symm.trans hindices.1
    rw [hiP]
    exact selected_root_mem P U hU hP.labels

theorem projection_body_exact {S T U : Stem} {hS : S.done.length = S.root}
    {hU : U.done.length = U.root} (A : Projection S hS T.ordinary U hU)
    (i : ℕ) (hi : i < U.bodyLabels.length) (j : ℕ) : j ∈ U.bodyLabels[i] ↔ Cut U T i j := by
  constructor
  · intro hj
    obtain ⟨P, y, hy, hproper, hP, hiP, hjP⟩ := A.bodyUsed i hi j hj
    refine ⟨y, hy, ?_, P.position.toInterior, ?_, ?_, hjP⟩
    · simpa only [ProperBelow, A.ordinary] using hproper
    · rw [Position.toInterior_word, A.ordinary]
      exact hP.ordinary
    · simpa only [Position.toInterior, List.length_map] using hiP
  · rintro ⟨y, hy, hproper, Q, hQ, hiQ, hjQ⟩
    have hp : ProperBelow y S := by simpa only [ProperBelow, A.ordinary] using hproper
    obtain ⟨P, hP⟩ := A.cuts y hy hp
    have hindices := jointCut_indices hP hQ
    have hiP : i = P.position.stem.done.length := hiQ.symm.trans hindices.1
    have hjP : j = P.position.entries.length := hjQ.symm.trans hindices.2
    obtain ⟨_, hmem⟩ := selected_body_mem P U hU hP.labels
    simpa only [hiP, hjP] using hmem

theorem projection_exact {S T U : Stem} {hS : S.done.length = S.root}
    {hU : U.done.length = U.root} (A : Projection S hS T.ordinary U hU) : ExactAnnotations U T :=
  ⟨projection_root_exact A, projection_body_exact A⟩

theorem interiorCuts_congr_other {S T T' : Stem} (hT : T'.ordinary = T.ordinary)
    (h : InteriorCuts S T) : InteriorCuts S T' := by
  simpa only [InteriorCuts, hT] using h

theorem exactAnnotations_congr_other {S T T' : Stem} (hT : T'.ordinary = T.ordinary)
    (h : ExactAnnotations S T) : ExactAnnotations S T' := by
  constructor
  · intro x
    simpa only [Cut, hT] using h.root x
  · intro i hi j
    simpa only [Cut, hT] using h.body i hi j

/-- Both words can be annotated with exactly their intrinsic cut indices,
without changing either ordinary word. Separation beyond disjoint support
is not part of this statement. -/
theorem output_pair_annotations {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : (LabelledRealization.vertex hH s).1.length ≠
      (LabelledRealization.vertex hH t).1.length) :
    ∃ U : Stem, ∃ _hU : U.done.length = U.root, ∃ V : Stem, ∃ _hV : V.done.length = V.root,
      U.root = (LabelledRealization.output hH s).stem.root ∧
      V.root = (LabelledRealization.output hH t).stem.root ∧
      U.ordinary = (LabelledRealization.output hH s).stem.ordinary ∧
      V.ordinary = (LabelledRealization.output hH t).stem.ordinary ∧
      Disjoint U.decorated.toFinset V.decorated.toFinset ∧
      InteriorCuts U V ∧ InteriorCuts V U ∧ ExactAnnotations U V ∧ ExactAnnotations V U := by
  obtain ⟨U, hU, hPU⟩ := output_pair_projection hH s t hroots
  obtain ⟨V, hV, hPV⟩ := output_pair_projection hH t s hroots.symm
  have hUsub : U.decorated.toFinset ⊆ (LabelledRealization.output hH s).stem.decorated.toFinset :=
    fun x hx ↦ List.mem_toFinset.mpr (hPU.decorated.subset (List.mem_toFinset.mp hx))
  have hVsub : V.decorated.toFinset ⊆ (LabelledRealization.output hH t).stem.decorated.toFinset :=
    fun x hx ↦ List.mem_toFinset.mpr (hPV.decorated.subset (List.mem_toFinset.mp hx))
  have hdis := (LabelledRealization.output_properties_of_roots_ne hH s t hroots).1
  refine ⟨U, hU, V, hV, hPU.root, hPV.root, hPU.ordinary, hPV.ordinary,
    hdis.mono hUsub hVsub, ?_, ?_, ?_, ?_⟩
  · exact interiorCuts_congr_other hPV.ordinary
      (projection_interior (T := (LabelledRealization.output hH t).stem) hPU)
  · exact interiorCuts_congr_other hPU.ordinary
      (projection_interior (T := (LabelledRealization.output hH s).stem) hPV)
  · exact exactAnnotations_congr_other hPV.ordinary
      (projection_exact (T := (LabelledRealization.output hH t).stem) hPU)
  · exact exactAnnotations_congr_other hPU.ordinary
      (projection_exact (T := (LabelledRealization.output hH s).stem) hPV)

end Erdos118.CutIndices
