import SystemE.Sorts.Segments

/--
Triangles are called "Areas" in [Avigad et al., 2009]
-/
inductive Triangle
| ofPoints (a b c : Point)

namespace Triangle

def sides : Triangle → Segment × Segment × Segment
| ofPoints a b c => (⟨a,b⟩, ⟨b,c⟩, ⟨c,a⟩)

axiom area : Triangle → ℝ

notation:max "△" a ":" b ":" c:66 => ofPoints a b c

noncomputable instance : Coe Triangle Real := ⟨area⟩

instance : LT Triangle := ⟨fun a b => area a < area b⟩

end Triangle
