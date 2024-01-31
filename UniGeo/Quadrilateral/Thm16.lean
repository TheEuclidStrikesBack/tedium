import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_16 : ∀ (F G H I : Point) (FG HI GH FI FH : Line),
  formQuadrilateral F G H I FG HI GH FI ∧
  distinctPointsOnLine F H FH ∧
  |(F─I)| = |(G─H)| ∧
  |(H─I)| = |(F─G)| →
  ∠ F:H:I = ∠ G:F:H :=
by
  euclid_intros
  euclid_assert (△ F:G:H).congruent (△ H:I:F)
  euclid_apply Triangle.congruent_if (△ F:G:H) (△ H:I:F)
  -- euclid_finish
  admit

end UniGeo.Quadrilateral
