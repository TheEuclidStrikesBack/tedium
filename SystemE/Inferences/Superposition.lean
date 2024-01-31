import SystemE.Sorts
import SystemE.Relations

/--
A combination of the two superposition rules in [Avigad et al., 2009]
-/
theorem superposition : ∀ (a b c d g h : Point) (AB BC AC L : Line),
  formTriangle a b c AB BC AC ∧ distinctPointsOnLine d g L ∧ ¬(h.onLine L) →
  ∃ (b' c' : Point) (BC' AC' : Line), (∠ b:a:c = ∠ b':d:c') ∧ (∠ a:c:b = ∠ d:c':b') ∧ (∠ c:b:a = ∠ c':b':d) ∧
  |(a─b)| = |(d─b')| ∧ |(b─c)| = |(b'─c')| ∧ |(c─a)| = |(c'─d)| ∧ b'.onLine L ∧ ¬(between b' d g) ∧ c'.sameSide h L ∧ distinctPointsOnLine b' c' BC' ∧ distinctPointsOnLine d c' AC' :=
by
  sorry
