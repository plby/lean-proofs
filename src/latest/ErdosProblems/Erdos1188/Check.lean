import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
#check Fin.castSuccEmb
#check Fin.castSucc
#check Function.Embedding.trans
#check Fin.last
