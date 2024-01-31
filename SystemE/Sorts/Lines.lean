import SystemE.Sorts.Points

/--
A 2D line satisfy the equation ax + by - c = 0.
-/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nzero : a ≠ 0 ∨ b ≠ 0

namespace Line

lemma not_degen : ∀ L : Line, L.a ≠ 0 ∨ L.b ≠ 0 :=
by
  intros L
  apply L.nzero

def toSet : Line → Set Point
| Line.mk a b c _ => fun p => a * p.1 + b * p.2 = c

end Line
