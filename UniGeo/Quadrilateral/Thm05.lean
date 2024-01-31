import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_5 : ∀ (E F G H : Point) (EF GH FG EH EG : Line),
  formQuadrilateral E F G H EF GH FG EH ∧
  distinctPointsOnLine E G EG ∧
  |(E─F)| = |(G─H)| ∧
  ¬ GH.intersectsLine EF →
  ∠ E:G:F = ∠ G:E:H :=
by
  euclid_intros
  have : ∠ E:G:H = ∠ F:E:G := by
    euclid_apply Elements.Book1.proposition_29''' H F G E GH EF EG
    euclid_finish
  euclid_assert (△ E:F:G).congruent (△ G:H:E)
  euclid_apply Triangle.congruent_if (△ E:F:G) (△ G:H:E)
  -- euclid_finish
  admit

end UniGeo.Quadrilateral