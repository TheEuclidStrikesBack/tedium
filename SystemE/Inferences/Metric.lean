import SystemE.Sorts
import SystemE.Relations

--
-- Metric inferences defined in Sec. 3.5 of Avigad et al., 2009
-- They are NOT used explicitly in the tactics written by humans.
-- *
--   + is associative and commutative, with identity 0.

--   < is a linear ordering with least element 0

--   For any x, y, and z, if x < y then x + z < y + z

--
-- 1.
-- ab = 0 if and only if a = b.
--


@[aesop unsafe [apply,forward]]
theorem zero_segment_if : ∀ (a b : Point),
  |(a ─ b)| = 0 → a = b :=
by
  rintro ⟨x_a, y_a⟩ ⟨x_b, y_b⟩ h
  unfold Segment.length at h
  simp at h
  sorry

@[aesop unsafe [apply,forward]]
theorem zero_segment_onlyif : ∀ (a b : Point),
  a = b → |(a─b)| = 0 := by sorry

--
-- 2.
-- ab ≥ 0
--
@[simp]
theorem segment_gte_zero : ∀ (s : Segment),
  0 ≤ s.length := by sorry

--
-- 3.
-- ab = ba.
--
@[simp]
theorem segment_symmetric : ∀ (a b : Point),
  |(a─b)| = |(b─a)| := by sorry

--
-- 4.
-- a != b and b != c imply \abc = \cba.

-- Kaiyu: Jeremy's paper has a typo here? It says "a != b and a != c".
@[aesop unsafe [apply,forward]]
theorem angle_symm : ∀ (a b c : Point),
  (a ≠ b) ∧ (b ≠ c) → (∠ a:b:c = ∠ c:b:a) := by sorry

--
-- 5.
-- 0 ≤ \abc and \abc ≤ right-angle + right-angle.
--
@[simp]
theorem angle_range : ∀ (ang : Angle),
  (0 : ℝ) ≤ ang ∧ ang ≤ ∟ + ∟ := by sorry

--
-- 6.
-- △aab = 0. △
--
@[simp]
theorem degenerated_area : ∀ (a b : Point), Triangle.area △ a:a:b = 0 := by sorry

--
-- 7.
-- △abc ≥ 0.
--
@[simp]
theorem area_gte_zero : ∀ (ar : Triangle), 0 ≤ Triangle.area ar := by sorry

--
-- 8.
-- △abc = △cab and △abc = △acb.
--
@[simp]
theorem area_symm_1 : ∀ (a b c : Point),
    (△a:b:c) = (△c:a:b) := by sorry

@[simp]
theorem area_symm_2 : ∀ (a b c : Point),
    (△ a:b:c) = (△a:c:b) := by sorry

--
-- 9.
-- If ab = a′b′, bc = b′c′, ca = c′a′, \abc = \a′b′c′, \bca = \b′c′a′, and
-- \cab = \c′a′b′, then △abc = △a′b′c′.
--
@[aesop unsafe [apply,forward]]
theorem area_congruence : ∀ (a b c a' b' c' : Point),
    (a─b) = (a'─b') ∧
    (b─c) = (b'─c') ∧
    (c─a) = (c'─a') ∧
    (∠ a:b:c) = (∠ a':b':c') ∧
    (∠ b:c:a) = (∠ b':c':a') ∧
    (∠ c:a:b) = (∠ c':a':b')
    → (△ a:b:c) = (△ a':b':c') := by sorry
