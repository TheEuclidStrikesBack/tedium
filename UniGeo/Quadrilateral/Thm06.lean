import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_6 : ∀ (F G H I : Point) (FG HI GH FI FH : Line),
  formQuadrilateral F G H I FG HI GH FI ∧
  distinctPointsOnLine F H FH ∧
  |(F─G)| = |(H─I)| ∧
  ¬ HI.intersectsLine FG →
  |(G─H)| = |(F─I)| :=
by
  euclid_intros
  have : ∠ F:H:I = ∠ G:F:H := by
    euclid_apply Elements.Book1.proposition_29''' I G H F HI FG FH
    euclid_finish
  euclid_assert (△ F:G:H).congruent (△ H:I:F)
  euclid_apply Triangle.congruent_if (△ F:G:H) (△ H:I:F)
  -- euclid_finish
  admit

end UniGeo.Quadrilateral
