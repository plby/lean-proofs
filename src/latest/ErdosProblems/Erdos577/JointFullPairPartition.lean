import ErdosProblems.Erdos577.JointFullCompletion

/-! Two explicit cycle pairs join a terminal replacement to partition the twelve-vertex set. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma outside_pair_partition (v : Quadrilateral G) (x y z w : V) (b : Finset V)
    (hcard : ({x, y, z, w} : Finset V).card = 4)
    (hx : x ∉ v.support) (hy : y ∉ v.support) (hz : z ∉ v.support) (hw : w ∉ v.support)
    (hdis : Disjoint (({x, y, z, w} : Finset V) ∪ v.support) b)
    (a : V) (ha : a ∈ b) (hfirst : QuadOn G {a, v 0, y, v 1})
    (hsecond : QuadOn G {z, v 2, v 3, w}) (hrep : QuadOn G (insert x (b.erase a))) :
    Nonempty (BlockPartition G (({x, y, z, w} ∪ v.support) ∪ b)) := by
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := JointCore.four_distinct hcard
  have haout : a ∉ ({x, y, z, w} : Finset V) ∪ v.support :=
    fun hh ↦ disjoint_left.mp hdis hh ha
  have han (u : V) (hu : u ∈ ({x, y, z, w} : Finset V)) : a ≠ u :=
    fun he ↦ haout (mem_union_left _ (he.symm ▸ hu))
  have hacard : ({a, y, z, w} : Finset V).card = 4 :=
    card_eq_four.mpr ⟨a, y, z, w, han y (by simp), han z (by simp), han w (by simp),
      hyz, hyw, hzw, rfl⟩
  obtain ⟨hd, he⟩ := parallel_factor_geometry v a y z w
    (fun hh ↦ haout (mem_union_right _ hh)) hy hz hw hacard
  have he0 : ({a, y, z, w} : Finset V) ∪ v.support =
      insert a (insert y ({z, w} ∪ v.support)) := by
    simp only [insert_union, singleton_union]
  have parts : BlockPartition G (insert a (insert y ({z, w} ∪ v.support))) :=
    he0 ▸ he ▸ (BlockPartition.single hfirst).union (BlockPartition.single hsecond) hd
  have hsub : insert y ({z, w} ∪ v.support) ⊆ ({x, y, z, w} : Finset V) ∪ v.support := by
    intro u hu
    simp only [mem_insert, mem_union, mem_singleton] at hu ⊢
    tauto
  have hxbase : x ∉ insert y ({z, w} ∪ v.support) := by
    simp only [mem_insert, mem_union, mem_singleton, not_or]
    exact ⟨hxy, ⟨hxz, hxw⟩, hx⟩
  have hxb : x ∉ b := fun hh ↦ disjoint_left.mp hdis (mem_union_left _ (by simp)) hh
  have hxout : x ∉ insert y ({z, w} ∪ v.support) ∪ b := by
    simpa only [mem_union, not_or] using And.intro hxbase hxb
  let all := parts.replacementUnion (hdis.mono_left hsub) hxout ha (BlockPartition.single hrep)
  have hefinal : insert x (insert y ({z, w} ∪ v.support) ∪ b) =
      (({x, y, z, w} : Finset V) ∪ v.support) ∪ b := by
    simp only [insert_union, singleton_union]
  exact ⟨hefinal ▸ all⟩

end Erdos577.JointFinal
