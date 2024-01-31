import SystemE.Relations

theorem line_from_points : ∀ (a b : Point), a ≠ b →
  ∃ L : Line, (a.onLine L) ∧ (b.onLine L) := by sorry

theorem circle_from_points : ∀ (a b : Point), a ≠ b →
  ∃ α : Circle, (a.isCentre α) ∧ (b.onCircle α) := by sorry
