import SystemE.Sorts.Points

/--
A circle has a centre and a positive radius.
-/
structure Circle where
  centre : Point
  radius : ℝ
  ndegen : radius > 0

namespace Circle

def toSet : Circle → Set Point
| Circle.mk c r _ => fun p => (p - c : ℝ) = r

end Circle
