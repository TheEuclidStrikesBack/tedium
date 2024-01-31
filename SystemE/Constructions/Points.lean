import SystemE.Sorts
import SystemE.Relations

syntax " PointOnLine_def " ("at" ident)? : tactic
macro_rules
  | `(tactic| PointOnLine_def) => `(tactic| rw [Point.onLine, Line.toSet, Set.mem_def]; simp only;)
  | `(tactic| PointOnLine_def at $h) => `(tactic| rw [Point.onLine, Line.toSet, Set.mem_def] at $h:ident; simp only at $h:ident)

namespace Line

-- useful for proof implementations. Note the guard
noncomputable def as_function (L : Line) (_ : ¬ L.b = 0) : ℝ → ℝ := fun x => (L.c - L.a*x)/L.b

end Line

theorem arbitrary_point : ∃ _ : Point, true := by use ⟨0, 0⟩

theorem distinct_points : ∀ p₁ : Point, ∃ p₂ : Point, p₁ ≠ p₂ :=
by
  rintro ⟨x₁, y₁⟩
  use ⟨x₁ + 1, y₁ + 1⟩
  simp

theorem line_nonempty : ∀ l : Line, ∃ p : Point, p.onLine l :=
by
  rintro ⟨a, b, c, h⟩
  by_cases (a = 0)
  . have : b ≠ 0 := by tauto
    use (Point.coords 0 (c/b))
    PointOnLine_def
    ring_nf!; rw [mul_comm, ← mul_assoc, mul_comm (a := b⁻¹), mul_inv_cancel this, one_mul]
  . have : a ≠ 0 := by tauto
    use (Point.coords (c/a) 0)
    PointOnLine_def
    ring_nf! ; rw [mul_comm, ← mul_assoc, mul_comm (a := a⁻¹), mul_inv_cancel this, one_mul]

theorem exists_distincts_points_on_line :
  ∀ l : Line, ∀ p : Point, ∃ p' : Point, p ≠ p' ∧ p'.onLine l :=
by
  intro l p
  by_cases hp : (p.onLine l)
  · rcases l with ⟨a, b, c, h⟩
    rcases p with ⟨xₚ, yₚ⟩
    use ⟨xₚ + b, yₚ - a⟩
    constructor
    · cases h
      · have : yₚ ≠ yₚ - a := by sorry
        simp [this]
      · have : xₚ ≠ xₚ + b := by sorry
        sorry
    · PointOnLine_def at hp
      PointOnLine_def
      ring_nf
      assumption
  · rcases line_nonempty l with ⟨q, hq⟩
    use q
    constructor <;> try assumption
    by_contra hpq
    subst hpq
    contradiction

theorem exists_point_between_points_on_line :
  ∀ (L : Line) (b c : Point), distinctPointsOnLine b c L
  → ∃ a : Point, (a.onLine L) ∧ (between b a c) := by sorry

theorem exists_point_between_points_not_on_line :
  ∀ (L M : Line) (b c : Point), distinctPointsOnLine b c L ∧ L ≠ M
  → ∃ a : Point, (a.onLine L) ∧ (between b a c) ∧ ¬(a.onLine M) := by sorry

/--
This rule is not in [Avigad et al., 2009] but is convenient for proving some propositions.
-/
theorem point_between_points_shorter_than : ∀ (L : Line) (b c : Point) (s : Segment),
  distinctPointsOnLine b c L ∧ (|s| > 0) →
  ∃ a : Point, (a.onLine L) ∧ (between b a c) ∧ ((b─a) < s) := by sorry

theorem extend_point :
  ∀ (L : Line) (b c : Point), distinctPointsOnLine b c L
  → ∃ a : Point, (a.onLine L) ∧ (between b c a) := by sorry

theorem extend_point_not_on_line :
  ∀ (L M : Line) (b c : Point), distinctPointsOnLine b c L ∧ L ≠ M
  → ∃ a : Point, (a.onLine L) ∧ (between b c a) ∧ ¬(a.onLine M) := by sorry

/--
This rule is not in [Avigad et al., 2009] but is convenient for proving some propositions.
-/
theorem extend_point_longer :
  ∀ (L : Line) (b c : Point) (s : Segment), distinctPointsOnLine b c L
  → ∃ a : Point, (a.onLine L) ∧ (between b c a) ∧ ((c─a) > s) := by sorry

theorem point_same_side :
  ∀ (L : Line) (b : Point), ¬(b.onLine L) → ∃ a : Point, a.sameSide b L := by sorry

theorem distinct_point_same_side:
  ∀ (L : Line) (b c : Point), ¬(b.onLine L) → ∃ a : Point, a ≠ c ∧ a.sameSide b L := by sorry

/--
A stronger version of the Points construction rule 6 in [Avigad et al., 2009], which is convenient for proving some propositions.
-/
theorem point_on_line_same_side :
  ∀ (L M : Line) (b : Point), ¬(b.onLine L) ∧ (L.intersectsLine M)
  → ∃ a : Point, a.onLine M ∧ a.sameSide b L := by sorry

theorem exists_point_opposite :
  ∀ (L : Line) (b : Point), ¬(b.onLine L) → ∃ a : Point, a.opposingSides b L := by sorry

theorem exists_distinct_point_opposite_side :
  ∀ (L : Line) (b c : Point), ¬(b.onLine L) → ∃ a : Point, a ≠ c ∧ a.opposingSides b L := by sorry

theorem exists_point_on_circle :
  ∀ (α : Circle), ∃ a : Point, a.onCircle α := by sorry

theorem exists_distinct_point_on_circle :
  ∀ (α : Circle) (b : Point), ∃ a : Point, a ≠ b ∧ (a.onCircle α) := by sorry

theorem exists_point_inside_circle :
  ∀ (α : Circle), ∃ a : Point, a.insideCircle α := by sorry

theorem exists_distinct_point_inside_circle :
  ∀ (α : Circle) (b : Point), ∃ a : Point, a ≠ b ∧ a.insideCircle α := by sorry

theorem exists_point_outside_circle :
  ∀ (α : Circle), ∃ a : Point, a.outsideCircle α := by sorry

theorem exists_distinct_point_outside_circle :
  ∀ (α : Circle) (b : Point),  ∃ a : Point, a ≠ b ∧ a.outsideCircle α := by sorry
