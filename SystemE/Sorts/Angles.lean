import SystemE.Sorts.Points

/--
An angle ∠ABC is defined by three points.
-/
inductive Angle
| ofPoints (A B C : Point)

namespace Angle

@[irreducible]
def Right : ℝ := 90

notation "∟" => Right

axiom degree : Angle → ℝ

notation:71 "∠" a ":" b ":" c:72 => degree (ofPoints a b c)

noncomputable instance : Coe Angle ℝ := ⟨degree⟩

instance : LT Angle := ⟨fun a b => degree a < degree b⟩

end Angle
