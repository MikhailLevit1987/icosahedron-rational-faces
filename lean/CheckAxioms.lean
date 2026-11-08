import Icosahedron

/-! Run with `lake env lean CheckAxioms.lean`. Expected output for each theorem:
`depends on axioms: [propext, Classical.choice, Quot.sound]` (no `sorryAx`, and no
`Lean.ofReduceBool`, i.e. no `native_decide`). -/

#print axioms Icosahedron.no_rational_point_on_every_face
#print axioms Icosahedron.separation
#print axioms Icosahedron.reduction
#print axioms Icosahedron.K.real_all
#print axioms Icosahedron.K.complex_all
