import ErdosProblems.Erdos577.ChainExchange

/-! Change only the displayed support of a local chain along a proved set equality. -/

namespace Erdos577.LocalChain

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : Finset V}

def withSupport (d : LocalChain G s) (h : s = t) : LocalChain G t where
  terminal := d.terminal
  triangle := d.triangle
  block := d.block
  triangle_clique := d.triangle_clique
  terminal_not_mem := d.terminal_not_mem
  quad := d.quad
  disjoint := d.disjoint
  cover := d.cover.trans h

@[simp] lemma withSupport_terminal (d : LocalChain G s) (h : s = t) :
    (d.withSupport h).terminal = d.terminal := rfl

@[simp] lemma withSupport_triangle (d : LocalChain G s) (h : s = t) :
    (d.withSupport h).triangle = d.triangle := rfl

@[simp] lemma withSupport_block (d : LocalChain G s) (h : s = t) :
    (d.withSupport h).block = d.block := rfl

@[simp] lemma withSupport_remainder (d : LocalChain G s) (h : s = t) :
    (d.withSupport h).remainder = d.remainder := rfl

end Erdos577.LocalChain
