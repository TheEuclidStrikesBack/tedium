import Mathlib.Data.Real.Sqrt

open Lean PrettyPrinter

/--
A 2D point of coordinates `x` and `y`.
-/
@[irreducible]
structure Point where
coords ::
  x : ℝ
  y : ℝ

namespace Point

@[app_unexpander Point.coords]
def unexpand_coords : Unexpander
| `($_ $t $s) => `(⟨$t,$s⟩)
| _ => throw ()

noncomputable instance : HSub Point Point ℝ :=
⟨fun a b => Real.sqrt ((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y))⟩

@[simp]
lemma diff_def {a b : Point} : a - b =  Real.sqrt ((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y)) := by rfl

@[simp]
lemma x_coord_of_coords (x y : ℝ) : Point.x ⟨x, y⟩ = x := by rfl

@[simp]
lemma y_coord_of_coords (x y : ℝ) : Point.y ⟨x, y⟩ = y := by rfl

end Point
