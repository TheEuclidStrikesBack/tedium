import SystemE.Constructions.Points

theorem intersection_lines : ∀ (L M : Line), L.intersectsLine M →
  ∃ a : Point, (a.onLine L) ∧ (a.onLine M) := by sorry

theorem intersection_circle_line : ∀ (α : Circle) (L : Line), L.intersectsCircle α →
  ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) := by sorry

theorem intersections_circle_line : ∀ (α : Circle) (L : Line), L.intersectsCircle α →
  ∃ (a b : Point), (a.onCircle α) ∧ (a.onLine L) ∧ (b.onCircle α) ∧ (b.onLine L) ∧ a ≠ b := by sorry

theorem intersection_circle_line_between_points : ∀ (α : Circle) (L : Line) (b c :Point),
  (b.insideCircle α) ∧ (b.onLine L) ∧ (c.outsideCircle α) ∧ (c.onLine L) →
  ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) ∧ (between b a c) := by sorry

theorem intersection_circle_line_extending_points : ∀ (α : Circle) (L : Line) (b c :Point),
  (b.insideCircle α) ∧ distinctPointsOnLine b c L →
  ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) ∧ (between a b c) := by sorry

theorem intersection_circles : ∀ (α β : Circle), α.intersectsCircle β →
  ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β) := by sorry

theorem intersections_circles : ∀ (α β : Circle), α.intersectsCircle β →
  ∃ (a b : Point), (a.onCircle α) ∧ (a.onCircle β) ∧ (b.onCircle α) ∧ (b.onCircle β) ∧ a ≠ b := by sorry

theorem intersection_same_side : ∀ (α β : Circle) (b c d : Point) (L : Line),
  (α.intersectsCircle β) ∧ (c.isCentre α) ∧ (d.isCentre β) ∧ (c.onLine L) ∧ (d.onLine L) ∧ ¬(b.onLine L) →
  ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β) ∧ (a.sameSide b L) := by sorry

theorem intersection_opposite_side : ∀ (α β : Circle) (b c d : Point) (L : Line),
  (α.intersectsCircle β) ∧ (c.isCentre α) ∧ (d.isCentre β) ∧ (c.onLine L) ∧ (d.onLine L) ∧ ¬(b.onLine L) →
  ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β) ∧ a.opposingSides b L := by sorry
