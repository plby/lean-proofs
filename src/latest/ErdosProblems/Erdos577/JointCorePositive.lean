import ErdosProblems.Erdos577.JointCoreCopies
import ErdosProblems.Erdos577.JointCoreComplements

/-! Complementary quadrilaterals and universal third-row replacements in the actual core. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SourcePattern.complements (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.triangle q.support) (h : SourcePattern tag p q)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) :
    G.Adj p.center (q 2) ∧ G.Adj p.center (q 3) ∧ G.Adj (q 2) (q 3) ∧
    QuadOn G ((p.triangle ∪ q.support) \ {p.center, q 2, q 3}) ∧
    5 ≤ edgeCount G ((p.triangle ∪ q.support) \ {p.center, q 2, q 3}) ∧
    QuadOn G ((p.triangle ∪ q.support) \ {q 2, p.center, p.vertices 2}) ∧
    QuadOn G ((p.triangle ∪ q.support) \ {q 3, p.center, p.vertices 2}) ∧
    QuadOn G ((p.triangle ∪ q.support) \ {q 2, q 3, p.vertices 2}) := by
  let f := modelCopy tag p q hd u hu h
  have hinj : Function.Injective (f : Fin 8 → V) := f.injective
  have h1 : f 1 = p.center := labeling_nonzero p q hd u hu 1 (by decide)
  have h2 : f 2 = p.vertices 2 := labeling_nonzero p q hd u hu 2 (by decide)
  have h6 : f 6 = q 2 := labeling_right p q hd u hu 2
  have h7 : f 7 = q 3 := labeling_right p q hd u hu 3
  have hk : core.image f = p.triangle ∪ q.support := labeling_core p q hd u hu
  have he := distinguished_edges tag
  have h16 : G.Adj (f 1) (f 6) := f.toHom.map_rel' he.1
  have h17 : G.Adj (f 1) (f 7) := f.toHom.map_rel' he.2.1
  have h67 : G.Adj (f 6) (f 7) := f.toHom.map_rel' he.2.2
  rw [h1, h6] at h16
  rw [h1, h7] at h17
  rw [h6, h7] at h67
  have hp := (primary_quad tag).image f
  have hpE := (primary_edges tag).trans (edgeCount_image_le f (core \ {1, 6, 7}))
  have hs1 := (secondary_first tag).image f
  have hs2 := (secondary_second tag).image f
  have ht := (tertiary_quad tag).image f
  change QuadOn G ((core \ {1, 6, 7}).image f) at hp
  change 5 ≤ edgeCount G ((core \ {1, 6, 7}).image f) at hpE
  change QuadOn G ((core \ {6, 1, 2}).image f) at hs1
  change QuadOn G ((core \ {7, 1, 2}).image f) at hs2
  change QuadOn G ((core \ {6, 7, 2}).image f) at ht
  have hs (s : Finset (Fin 8)) : (core \ s).image f =
      (p.triangle ∪ q.support) \ s.image f := by
    rw [image_sdiff _ _ hinj, hk]
  simp only [hs, image_insert, image_singleton, h1, h2, h6, h7] at hp hpE hs1 hs2 ht
  exact ⟨h16, h17, h67, hp, hpE, hs1, hs2, ht⟩

omit [DecidableRel G.Adj] in
theorem SourcePattern.third_universal (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.triangle q.support) (h : SourcePattern tag p q)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) :
    ∀ v ∈ q.support, QuadOn G (insert (p.vertices 3) (q.support.erase v)) := by
  classical
  intro v hv
  obtain ⟨i, rfl⟩ := (q.mem_support v).mp hv
  let f := modelCopy tag p q hd u hu h
  have h3 : f 3 = p.vertices 3 := labeling_nonzero p q hd u hu 3 (by decide)
  have hq : block.image f = q.support := labeling_block p q hd u hu
  have hi : f (Fin.natAdd 4 i) = q i := labeling_right p q hd u hu i
  have hm : Fin.natAdd 4 i ∈ block := by fin_cases i <;> decide +kernel
  have hr := (third_replacement tag (Fin.natAdd 4 i) hm).image f
  have he : (block.erase (Fin.natAdd 4 i)).image f = (block.image f).erase (f (Fin.natAdd 4 i)) :=
    image_erase f.injective block (Fin.natAdd 4 i)
  rwa [image_insert, he, h3, hq, hi] at hr

end Erdos577.JointCore
