import ErdosProblems.Erdos547.FineTreePartition
import ErdosProblems.Erdos547.ColourDistance
import ErdosProblems.Erdos547.ShrubEmbedding

/-!
# The one or two roots of an actual fine-partition shrub
-/

namespace Erdos547

open Finset SimpleGraph

structure ShrubRootData {U : Type*} (T : SimpleGraph U) (W S : Finset U) where
  seed : ↥W
  root : ↥S
  second : Option (↥W × ↥S)
  primary_edge : T.Adj seed.val root.val
  secondary_edge : ∀ z, second = some z → T.Adj z.1.val z.2.val
  attachments : ∀ z : ↥W, ∀ u : ↥S, T.Adj z.val u.val →
    (z = seed ∧ u = root) ∨ second = some (z, u)
  rooted : IsRootedShrub (T.induce (S : Set U)) root (second.map Prod.snd)

namespace FineTreePartition

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}

theorem nonempty_shrub_root_data (P : FineTreePartition T r ℓ col) (hT : T.IsTree)
    (S : Finset U) (hS : S ∈ P.shrubs) : Nonempty (ShrubRootData T P.seeds S) := by
  classical
  have htree := P.shrub_tree S hS
  let A := P.seeds.filter (fun z ↦ 0 < degreeIn T S z)
  obtain ⟨a, ha, hda⟩ := P.has_attachment S hS
  let sa : ↥P.seeds := ⟨a, ha⟩
  have haA : a ∈ A := Finset.mem_filter.mpr ⟨ha, hda⟩
  have hroot (z : ↥P.seeds) (hz : 0 < degreeIn T S z.val) :
      ∃ x : ↥S, T.Adj z.val x.val ∧ ∀ y : ↥S, T.Adj z.val y.val → y = x := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hz
    obtain ⟨hxS, hzx⟩ := Finset.mem_filter.mp hx
    refine ⟨⟨x, hxS⟩, hzx, ?_⟩
    intro y hzy
    apply Subtype.ext
    exact unique_attachment_to_connected hT.isAcyclic (S : Set U) htree.connected.preconnected
      (fun hzS ↦ Finset.disjoint_left.mp (P.disjoint_seeds S hS) hzS z.property)
      y.property hxS hzy hzx
  obtain ⟨x, hax, huniqx⟩ := hroot sa hda
  have hdeg (z : ↥P.seeds) (u : ↥S) (hzu : T.Adj z.val u.val) : 0 < degreeIn T S z.val :=
    Finset.card_pos.mpr ⟨u.val, Finset.mem_filter.mpr ⟨u.property, hzu⟩⟩
  by_cases hsecond : (A.erase a).Nonempty
  · obtain ⟨b, hb⟩ := hsecond
    have hbA := (Finset.mem_erase.mp hb).2
    have hba := (Finset.mem_erase.mp hb).1
    obtain ⟨hbW, hdb⟩ := Finset.mem_filter.mp hbA
    let sb : ↥P.seeds := ⟨b, hbW⟩
    obtain ⟨y, hby, huniqy⟩ := hroot sb hdb
    have herase : (A.erase a).card ≤ 1 := by
      rw [Finset.card_erase_of_mem haA]
      have hcard : A.card ≤ 2 := P.attachment_count S hS
      omega
    have hcover (z : ↥P.seeds) (hz : 0 < degreeIn T S z.val) : z = sa ∨ z = sb := by
      by_cases hza : z.val = a
      · exact Or.inl (Subtype.ext hza)
      · have hzA : z.val ∈ A.erase a :=
          Finset.mem_erase.mpr ⟨hza, Finset.mem_filter.mpr ⟨z.property, hz⟩⟩
        exact Or.inr (Subtype.ext (Finset.card_le_one.mp herase z.val hzA b hb))
    have hcolseed : col sa.val = col sb.val :=
      P.attachment_colour S hS a ha b hbW hda hdb
    have hcolxy : col x.val = col y.val := by
      have h₁ := col.valid hax
      have h₂ := col.valid hby
      rw [← hcolseed] at h₂
      omega
    let cS : (T.induce (S : Set U)).Coloring (Fin 2) := {
      toFun := fun z ↦ col z.val
      map_rel' := fun h ↦ col.valid h
    }
    have heven : (T.induce (S : Set U)).dist x y % 2 = 0 :=
      (dist_even_iff_colour_eq _ htree.connected.preconnected cS x y).mpr hcolxy
    have hdist : 4 ≤ (T.induce (S : Set U)).dist x y :=
      inner_attachment_distance_lower T hT (S : Set U) htree a b x y hax hby
        (P.attachment_distance S hS a ha b hbW hda hdb hba.symm)
    refine ⟨{
      seed := sa
      root := x
      second := some (sb, y)
      primary_edge := hax
      secondary_edge := ?_
      attachments := ?_
      rooted := ?_
    }⟩
    · intro z hz
      have he : (sb, y) = z := Option.some.inj hz
      subst z
      exact hby
    · intro z u hzu
      rcases hcover z (hdeg z u hzu) with rfl | rfl
      · exact Or.inl ⟨rfl, huniqx u hzu⟩
      · exact Or.inr (by rw [huniqy u hzu])
    · refine ⟨htree, ?_, ?_⟩
      · intro z hz
        have he : y = z := Option.some.inj hz
        subst z
        exact heven
      · intro z hz
        have he : y = z := Option.some.inj hz
        subst z
        exact hdist
  · have hcover (z : ↥P.seeds) (hz : 0 < degreeIn T S z.val) : z = sa := by
      apply Subtype.ext
      by_contra hza
      exact hsecond ⟨z.val, Finset.mem_erase.mpr
        ⟨hza, Finset.mem_filter.mpr ⟨z.property, hz⟩⟩⟩
    refine ⟨{
      seed := sa
      root := x
      second := none
      primary_edge := hax
      secondary_edge := fun _ h ↦ by cases h
      attachments := ?_
      rooted := ⟨htree, (fun _ h ↦ by cases h), (fun _ h ↦ by cases h)⟩
    }⟩
    intro z u hzu
    have hz := hcover z (hdeg z u hzu)
    subst z
    exact Or.inl ⟨rfl, huniqx u hzu⟩

end FineTreePartition

end Erdos547

#print axioms Erdos547.FineTreePartition.nonempty_shrub_root_data
